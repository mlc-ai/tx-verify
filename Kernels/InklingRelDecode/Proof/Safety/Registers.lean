-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.StoreOnce
public import Lemmas.Flow.NotRegister

@[expose] public section

/-!
# The register-request branch of `Unsafe`

`SetMaxNReg.Unsafe` has four clauses for a request `e` of direction `inc` and count `n`:

1. a previous request of the thread left a count `m` with `n < m` (increase) or `m < n` (decrease);
2. the warpgroup is not whole inside the block;
3. a request of the same warpgroup with the same ordinal differs in direction or count;
4. a later request (ordinal above 0) does not follow the previous requests of every thread of its
   warpgroup in base causality order.

Clauses 1 and 2 are decided here. Every `setmaxnreg` of the program is `inc 256` or `dec 24`
(an audit by `decide +kernel`, and `Flow.fires_setMaxReg_op` for the event), so a previous count
is 256 or 24 and no request lowers an increase or raises a decrease; the block is 256 threads, two
whole warpgroups. Clauses 3 and 4 are about the four warps of warpgroup 1 (the workers), whose
requests depend on their roles (`RegAgree`, `RegSync`, fields of `Protocol`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every register adjustment of the program is `inc 256` or `dec 24`. -/
def regOk : Op → Bool
  | .setMaxReg inc n => (inc && n == 256) || (!inc && n == 24)
  | _ => true

theorem kernel_regOk : kernel.code.all (fun ins => regOk ins.op) = true := by decide +kernel

/-- **A register request is `inc 256` or `dec 24`.** -/
theorem request_values (hX : Consistent L kernel asms mem0 X) {e : EvId} {pc n inst : Nat}
    {inc : Bool} (h : SetMaxNReg.Request X e pc inc n inst) :
    (inc = true ∧ n = 256) ∨ (inc = false ∧ n = 24) := by
  rcases Flow.get_source hX h with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · have hop := fires_setMaxReg_op hf (show (⟨pc, .setMaxReg inc n inst⟩ : Event).kind =
      .setMaxReg inc n inst from rfl)
    have hall := List.all_eq_true.mp kernel_regOk ins (List.mem_of_getElem? hc)
    rw [hop] at hall
    simp only [regOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hall
    rcases hall with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨h1, h2⟩

/-- The fold that tracks a thread's last request count. -/
def lastCount (old : Option Nat) (ev : Event) : Option Nat :=
  match ev.kind with
  | .setMaxReg _ n _ => some n
  | _ => old

theorem foldl_lastCount {m : Nat} : ∀ (l : List Event) (o : Option Nat),
    l.foldl lastCount o = some m → o = some m ∨
      ∃ (k pc : Nat) (inc : Bool) (inst : Nat),
        l[k]? = some (Event.mk pc (Kind.setMaxReg inc m inst)) := by
  intro l
  induction l with
  | nil => intro o h; exact .inl h
  | cons ev l ih =>
    intro o h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h' | ⟨k, pc, inc, inst, hk⟩
    · obtain ⟨pc, kd⟩ := ev
      cases kd with
      | setMaxReg inc n inst =>
        simp only [lastCount, Option.some.injEq] at h'
        exact .inr ⟨0, pc, inc, inst, by simp [h']⟩
      | _ => exact .inl (by simpa [lastCount] using h')
    · exact .inr ⟨k + 1, pc, inc, inst, by simpa using hk⟩

/-- The count a thread's previous request left is the count of an earlier request event. -/
theorem prior_request {e : EvId} {m : Nat} (h : SetMaxNReg.prior X e = some m) :
    ∃ k < e.2, ∃ pc inc inst, X.get (e.1, k) = some ⟨pc, .setMaxReg inc m inst⟩ := by
  have h' : ((X.tr e.1).take e.2).foldl lastCount none = some m := h
  rcases foldl_lastCount _ _ h' with h0 | ⟨k, pc, inc, inst, hk⟩
  · cases h0
  · rw [List.getElem?_take] at hk
    split at hk
    · rename_i hlt
      exact ⟨k, hlt, pc, inc, inst, hk⟩
    · cases hk

/-- **Requests of one warpgroup with one ordinal agree**: the same direction and count. -/
def RegAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {e f : EvId} {pc pc' n n' inst inst' : Nat} {inc inc' : Bool},
    SetMaxNReg.SameGroup L e.1 f.1 → SetMaxNReg.Request X e pc inc n inst →
    SetMaxNReg.Request X f pc' inc' n' inst' →
    SetMaxNReg.ordinal X e = SetMaxNReg.ordinal X f → inc = inc' ∧ n = n'

/-- **A later request follows the warpgroup's previous requests** in base causality order: every
thread of the warpgroup made the request of the previous ordinal, before it. It is asked only of
a request at a site that no assumption exempts (`Assumptions.setMaxNRegSync` exempts the loop-head
request, ASM-SETMAXNREG-SYNC). -/
def RegSync (L : Launch) (X : Execution) : Prop :=
  ∀ {e : EvId} {pc n inst : Nat} {inc : Bool}, SetMaxNReg.Request X e pc inc n inst →
    asms.all (fun a => !a.regSyncExempt pc) = true →
    0 < SetMaxNReg.ordinal X e → ∀ h, h < L.threads → SetMaxNReg.SameGroup L e.1 h →
      ∃ j pc' inc' n' inst', SetMaxNReg.Request X (h, j) pc' inc' n' inst' ∧
        SetMaxNReg.ordinal X (h, j) + 1 = SetMaxNReg.ordinal X e ∧
        baseCausality L X (h, j) e

/-- **No register request is unsafe**, given the agreement and synchronization of the warpgroups
(clauses 3 and 4); clauses 1 and 2 are decided on the program text and the launch. -/
theorem no_regUnsafe (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (ha : RegAgree L X) (hs : RegSync L X) : ¬ SetMaxNReg.UnsafeAt asms L X := by
  rintro ⟨e, pc, inc, n, inst, hreq, ⟨m, hm, hlt⟩ | hgrp | ⟨f, pc', inc', n', inst', hsg, hf,
    hord, hne⟩ | ⟨hex, hpos, hsync⟩⟩
  · obtain ⟨k, -, pc1, inc1, inst1, hk⟩ := prior_request hm
    have hv := request_values hX hreq
    have hv' := request_values hX
      (show SetMaxNReg.Request X (e.1, k) pc1 inc1 m inst1 from hk)
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv' with ⟨-, h3⟩ | ⟨-, h3⟩ <;> subst h1 <;>
      simp only [Bool.false_eq_true, ite_true, ite_false] at hlt <;> omega
  · rw [hpre.block] at hgrp
    omega
  · obtain ⟨h1, h2⟩ := ha hsg hreq hf hord
    rcases hne with hne | hne
    · exact hne h1
    · exact hne h2
  · exact hsync (fun h hh hg => hs hreq hex hpos h hh hg)

end
end PTX.Kernels.InklingRelDecode.Proof.Safety

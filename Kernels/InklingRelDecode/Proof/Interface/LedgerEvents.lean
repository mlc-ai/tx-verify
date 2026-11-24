-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.BarStatic
public import Kernels.InklingRelDecode.Proof.Thread.LedgerClosure

@[expose] public section

/-!
# The register requests and barrier-1 events of an event, from its state

`Thread/LedgerTables.lean` gives every abstract state of a thread the request (`tReq`) and the
barrier-1 event (`tB1`) its own instruction is. An event fired from the state is a register
request exactly when the state's instruction is one, with the instruction's direction and count
(`event_req`), and is a barrier-1 event exactly when the state's instruction is
`barrier.sync 1` (`event_b1`). So the counts of requests and of barrier-1 events before a state
follow the state's phase (`LedgerInv.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The phase of a thread's state. -/
def tPh : TSt → Nat × Nat
  | .d s => dPh s
  | .w s => wPh s

/-- The register request a state's instruction is. -/
def tReq : TSt → Option (Bool × Nat)
  | .d s => dReq s
  | .w s => wReqS s

/-- Whether a state's instruction is `barrier.sync 1`. -/
def tB1 : TSt → Bool
  | .d s => dB1 s
  | .w s => wB1S s

theorem t_static (s : TSt) : reqAt (TSt.pc s) = tReq s ∧ barAt (TSt.pc s) = tB1 s := by
  cases s with
  | d s => exact d_static s
  | w s => exact w_static s

/-- Every `setmaxnreg` of the program has a count the model accepts. -/
def reqValid : Op → Bool
  | .setMaxReg _ n => SetMaxNReg.validCount n
  | _ => true

theorem kernel_reqValid : kernel.code.all (fun ins => reqValid ins.op) = true := by
  decide +kernel

/-- **An event is a register request exactly when its state's instruction is**, with the
instruction's direction and count. -/
theorem event_req (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    (SetMaxNReg.isRequest e = true ↔ (tReq s).isSome = true) ∧
      ∀ pc i n inst, e = ⟨pc, .setMaxReg i n inst⟩ → tReq s = some (i, n) := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hs := (t_static s).1
  by_cases hq : ∃ i n, ins.op = .setMaxReg i n
  · obtain ⟨i, n, hop⟩ := hq
    have hall := List.all_eq_true.mp kernel_reqValid ins (List.mem_of_getElem? hc')
    rw [hop] at hall hf'
    simp only [reqValid] at hall
    obtain ⟨inst, rfl⟩ := fires_of_setMaxReg_op hall hf'
    have h1 : tReq s = some (i, n) := by
      rw [← hs]
      simp [reqAt, hc', hop]
    refine ⟨?_, ?_⟩
    · simp [SetMaxNReg.isRequest, h1]
    · intro pc' i' n' inst' h
      simp only [Event.mk.injEq, Kind.setMaxReg.injEq] at h
      obtain ⟨-, rfl, rfl, -⟩ := h
      exact h1
  · have hn : tReq s = none := by
      rw [← hs]
      simp only [reqAt, hc']
      cases hop : ins.op <;> simp_all
    refine ⟨?_, ?_⟩
    · rw [hn]
      simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
      intro hr
      obtain ⟨pc, kd⟩ := e
      cases kd <;> simp only [SetMaxNReg.isRequest, Bool.false_eq_true] at hr
      rename_i inc n inst
      exact hq ⟨inc, n, fires_setMaxReg_op hf' rfl⟩
    · intro pc i n inst h
      exfalso
      subst h
      exact hq ⟨i, n, fires_setMaxReg_op hf' rfl⟩

/-- The operation of an instruction whose event is a barrier arrival with id `id`. -/
theorem bar_kind_op (hb : L.block ≠ 128) {g : Nat} {t : TState} {ins : Instr} {o : Option TState}
    {pc : Nat} {e : Event} {id : Nat} {c : Option Nat} {m : BarMode}
    (hmem : ins ∈ kernel.code) (hf : Fires pc (eventTmpl asms L g t ins.op) e o)
    (hk : e.kind = .bar id c m) :
    (∃ al, ins.op = .barSync (.imm (id : Int)) al) ∨
      (id = 0 ∧ ∃ al, ins.op = .barSyncN (.imm 0) (.imm 128) al) := by
  have hop := fires_bar_op hf hk
  have hall := List.all_eq_true.mp kernel_barForm ins hmem
  cases hins : ins.op with
  | barSync b al =>
    rw [hins] at hf hall
    cases b with
    | imm v =>
      simp only [barForm, decide_eq_true_eq] at hall
      obtain ⟨n, rfl⟩ : ∃ n : Nat, v = n := ⟨v.toNat, (Int.toNat_of_nonneg hall.1).symm⟩
      have := EvD.fires_barSync_imm (by omega) hf
      rw [this] at hk
      simp only [Kind.bar.injEq] at hk
      obtain ⟨rfl, -, -⟩ := hk
      exact .inl ⟨al, rfl⟩
    | _ => simp [barForm] at hall
  | barSyncN b c' al =>
    rw [hins] at hf hall
    cases b with
    | imm v =>
      cases c' with
      | imm w =>
        by_cases h0 : v = 0
        · by_cases h1 : w = 128
          · subst h0 h1
            have := EvD.fires_barSyncN_128 hb hf
            rw [this] at hk
            simp only [Kind.bar.injEq] at hk
            obtain ⟨rfl, -, -⟩ := hk
            exact .inr ⟨rfl, al, rfl⟩
          · simp [barForm, h0, h1] at hall
        · simp [barForm, h0] at hall
      | _ => simp [barForm] at hall
    | _ => simp [barForm] at hall
  | barArrive b c' al =>
    rw [hins] at hall
    simp [barForm] at hall
  | _ =>
    rw [hins] at hop
    simp [barOp] at hop

/-- **An event is a barrier-1 event exactly when its state's instruction is `barrier.sync 1`.** -/
theorem event_b1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    Execution.isBarId 1 e = tB1 s := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hs := (t_static s).2
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  simp only [barAt, hc'] at hs
  rw [← hs]
  cases h1 : Execution.isBarId 1 e
  · -- not a barrier-1 event: the instruction is not `barrier.sync 1`
    symm
    cases hop : ins.op with
    | barSync b al =>
      cases b with
      | imm v =>
        by_cases hv : v = 1
        · subst hv
          have hid : (1 : Nat) < 16 := by decide
          have := EvD.fires_barSync_imm (id := 1) hid (by rw [hop] at hf'; exact_mod_cast hf')
          rw [this] at h1
          simp [Execution.isBarId] at h1
        · simp [hv]
      | _ => simp
    | _ => simp
  · obtain ⟨pc, c, m, hev⟩ := NamedBar.isBarId_form h1
    have hk : e.kind = .bar 1 c m := by rw [hev]
    rcases bar_kind_op hb hmem hf' hk with ⟨al, hop⟩ | ⟨h0, -⟩
    · simp [hop]
    · omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

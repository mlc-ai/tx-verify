-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Proof.Correction.SafeSt
import Lemmas.Isa.Tmpl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The values of the correction warps' stores

On the data machine's states: a log-sum-exp store is the row's, from its sum and maximum
(`lse_val`), and the operands of a Tensor Memory store are the values of its registers
(`tcSt_vals`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The bytes of a store of 32-bit registers. -/
theorem store32_val {A : List Assumption} {t : TState} {a : MemAccess} {sp : Space}
    {base wd r : Nat} {v : Value} (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base wd) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hw : a.elem.width = 32) (hsrc : a.srcs[t.sub]? = some (.reg r)) (hr : t.regs r = some v)
    (hv : v.bytes = 4) {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) {acc : Acc} {bs : List Byte}
    (he : e.kind = .wr acc bs) : bs = v.toBytes := by
  rw [eventTmpl, memTmpl_store hrule hs hb hk hsem, hw] at hf
  unfold storeTmpl at hf
  split at hf
  · simp only [Fires] at hf
    rw [hf.1] at he
    cases he
  · rw [hsrc] at hf
    have h1 : readValue L g t 32 (.reg r) >>= storeValue 32 = .ok v := by
      have h2 : readValue L g t 32 (.reg r) = .ok v := by
        simp [readValue, readReg, hr, pure, Except.pure]
      rw [h2]
      exact storeValue_of_bytes hv
    simp only [h1, Fires] at hf
    rw [hf.1] at he
    cases he
    rfl

private theorem mapM_vals {α : Type} {r : α → Exec Value} {f : Nat → Value} :
    ∀ {l : List α}, (∀ i < l.length, ∃ x, l[i]? = some x ∧ r x = .ok (f i)) →
      l.mapM r = .ok ((List.range l.length).map f) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l x ih =>
    intro h
    obtain ⟨y, h1, h2⟩ := h l.length (by simp)
    simp only [List.getElem?_concat_length, Option.some.injEq] at h1
    subst h1
    have hl := ih fun i hi => by
      obtain ⟨y, h1, h2⟩ := h i (by simp; omega)
      exact ⟨y, by rwa [List.getElem?_append_left hi] at h1, h2⟩
    rw [List.mapM_append, hl]
    simp [h2, bind, Except.bind, pure, Except.pure, List.range_succ]

/-- **The values of a Tensor Memory store** are those of its registers. -/
theorem tcSt_vals {A : List Assumption} {t : TState} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hsh : ∀ s, sh ≠ .packed16 s) {f : Nat → Value}
    (hss : ∀ i < ss.length, ∃ r, ss[i]? = some (.reg r) ∧ t.regs r = some (f i)) {pc : Nat}
    {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    {a : Nat} {vals : List Value} {sh' : TcShape} (he : e.kind = .tc (.st a vals sh')) :
    vals = (List.range ss.length).map f := by
  have key : ∀ u : TState, u.regs = t.regs → Fires pc (tcTmpl L g u (.tcSt ta ss sh)) e o →
      vals = (List.range ss.length).map f := by
    intro u hu hf
    have hm : ss.mapM (readValue L g u 32) = .ok ((List.range ss.length).map f) := by
      refine mapM_vals fun i hi => ?_
      obtain ⟨r, h1, h2⟩ := hss i hi
      exact ⟨_, h1, by simp [readValue, readReg, hu, h2, pure, Except.pure]⟩
    rw [tcTmpl_tcSt_plain hsh, hm] at hf
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hf
    repeat' split at hf
    all_goals simp_all [ofExec, Fires]
  change Fires pc (tcStTmpl A L g t ta ss sh) e o at hf
  unfold tcStTmpl at hf
  split at hf
  · split at hf
    · split at hf <;> (simp only [Fires] at hf; rw [hf.1] at he; cases he)
    · exact key { t with sub := 0 } rfl hf
  · exact key t rfl hf

set_option maxHeartbeats 4000000 in
/-- **The bytes of a log-sum-exp store.** -/
theorem lse_val {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g).AtD d t) (hk0 : d.k = 0) (hc : kernel.code[(code p L g).pc d]? = some ins)
    (hf : Fires ((code p L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    {hh : Fin 2} (hs : d.site = .lse hh) {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (lseSel p (rsOf d.v hh) (rmOf d.v hh)).toBytes := by
  have hreg : ∀ r ∈ Flow.live (livePc d), t.regs r = some (valueOf p L g d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub = 0 := by rw [h.2.1]; simp [hk0]
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  simp only at hs ⊢
  subst hs
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) ?_ hf hk
    simp only [valueOf, values, valuesLse, lookupLit, lseSel]
    split <;> first | rfl | exact erealValue_f32_bytes _

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction

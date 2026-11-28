-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Induct
public import Kernels.InklingRelDecode.Proof.Softmax.Data.VTypStep
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasHalf

/-! # The words of the value state are typed along the trace

The bias words a thread's loads return are `bf16` numbers (`bias_half`), so the words its value
state holds are bias words; given that the scores its score load returns are numbers, the state is
typed (`VTyp`) at every softmax state. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The step keeps the value state typed**, when the score loads return numbers. -/
public theorem vtyp_succ {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    {k : Nat} {ent : Control.Entry} {old y : Data.D} {e : Event} (he : X.get (g, k) = some e)
    (pc : e.pc = old.c.site.pc) (hn : succ ent L g old e = some (some y)) (hv : VTyp old.v) :
    VTyp y.v := by
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  obtain ⟨pc0, kind⟩ := e
  refine vtyp_step hv (fun ⟨j, hj⟩ a bs hk => ?_) (fun hs a vals sh hk => ?_)
  · have site : (∃ j : Fin 64, pc0 = 680 + 2 * j.val) ∨ ∃ j : Fin 64, pc0 = 1124 + 2 * j.val := by
      rcases hj with h | h <;> rw [h] at pc
      · exact .inl ⟨j, pc⟩
      · exact .inr ⟨j, pc⟩
    cases hk
    obtain ⟨x, hx⟩ := bias_half hp hX hf he site
    show Bw ((rebuild 3 bs).toOption.getD (b32 0))
    rw [hx]
    exact Or.inl ⟨x, rfl⟩
  · cases hk
    have h0 : pc0 = Flow.tmemLoad_0 := pc.trans (by rw [hs]; rfl)
    subst h0
    exact hS k a vals sh he

/-- **The value state is typed at every softmax state**, when the score loads return numbers. -/
public theorem soft_vtyp {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → VTyp y.v := by
  refine soft_induct hp hX (fun _ y => VTyp y.v) (fun _ => ⟨fun _ => bw_dflt, fun _ => bw_dflt,
    fun x hx => by simp at hx⟩) ?_
  intro k ent old y e he hu pc hn hv
  exact vtyp_succ hp hX hf hS he pc hn hv

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.CurStep
public import Kernels.InklingRelDecode.Proof.Softmax.Soft.ScoreAt

@[expose] public section

/-! # The words the first window reads, along the trace

The bias words and the score words of the value state together with the control invariant, at
every softmax state of a lane (one pass of `soft_ind`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The control invariant, the bias words and the score words at every softmax state.** -/
theorem soft_win {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hB : Lib.BiasEv Q L g X) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → ent.Ok →
        EntSp Q L g ent →
        Led X g k y ∧ Inv ent (g % L.block) y.c ∧ CurOk Q L g ent y ∧ ScOk X g k y := by
  intro k hk s hs nub w ent y n hsd ok E
  obtain ⟨led, inv, key⟩ := (soft_ind hp hX
    (fun ent k y => EntSp Q L g ent → CurOk Q L g ent y ∧ ScOk X g k y)
    (fun ent _ _ _ _ => ⟨cur_vac (Or.inl rfl),
      ⟨fun h => by simp [scored] at h, fun h => by simp [scored] at h⟩⟩)
    (fun k ent old y e ok he hu fd pc hn led inv J E =>
      ⟨cur_step hB E ok he hu fd pc hn led inv (J E).1, sc_step he hu fd hn led (J E).2⟩)
    k hk s hs nub).2 w ent y n hsd ok
  exact ⟨led, inv, (key E).1, (key E).2⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReachFrame
public import Lemmas.Flow.SegChain

@[expose] public section

/-! # An exact segment of control code keeps the facts it does not write

`Seg.frameSet`: an exact segment (`Seg`) whose code stays in a frame set `S` (`frameSetB`) until its
end, an event instruction, carries facts `H` on registers the set does not write from its start to
its end. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Flow.Code

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem Seg.frameSet (hA : RulesFrame A) {S : List Nat} {H F G : List (Nat × Value)} {n s b : Nat}
    (hB : frameSetB K S (H.map Prod.fst) = true) (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    (hp : (S.contains s || evAtB K s) = true) (h : Seg K A L g n s F b G) :
    Seg K A L g n s (F ++ H) b (G ++ H) := by
  intro t ht
  obtain ⟨hF, hH⟩ := (holds_append _ _ _).mp ht.2.2.2.2
  obtain ⟨t', hr, ht'⟩ := h t (At.mono ht hF)
  refine ⟨t', hr, ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, (holds_append _ _ _).mpr
    ⟨ht'.2.2.2.2, (rtg_frameSet hA hB hS (ht.1 ▸ hp) hH (run_rtg hr)).2⟩⟩

end
end PTX.Flow

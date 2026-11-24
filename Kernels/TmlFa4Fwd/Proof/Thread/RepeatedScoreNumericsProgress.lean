-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreRoundProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainMaximum
import Kernels.TmlFa4Fwd.Proof.Thread.AllScoreLoadWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Numeric PTX.Assumption Correction TcMma

/-- The score provenance for a consistent prefix supplies the word widths for local packing. -/
theorem repeatedLoadedScoreWidth {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (mode : Repeated) (q : Fin 4) {g pos address : Nat} {words : List Value}
    (he : X.get (g,pos) =
      some ⟨scorePc mode.round q,.tc (.ld address words .s32x32b)⟩) :
    ∀ k < 32, (words.getD k (b32 0)).bytes = 4 := by
  obtain ⟨_,_,_,_,_,_,hWords⟩ := scoreLoadWordsOfLaunch hp hX hFrame mode.round q he
  intro k hk
  have hWord := hWords ⟨k,hk⟩
  simp only [List.getD_eq_getElem?_getD,hWord,Option.getD_some]
  rfl

/-- A protected output footprint supplies the recorded word widths for both score paths. -/
theorem warpRepeatedScoresOfFootprint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hGuard : SyncGuarded l kernel X)
    (hLayout : TcMma.LayoutInjective X) (lead ordinal : Nat) (mode : Repeated) (stage : Fin 2)
    {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (scorePc mode.round 0) (F g))
    (hAddresses : ∀ g, SameWarp l lead g → ∀ q : Fin 4,
      (scoreReg mode.round q,b32 (scoreAddress l g stage q)) ∈ F g)
    (hRank : ∀ g (hWarp : SameWarp l lead g),
      ((X.tr g).take (input g hWarp).pos).countP isTcColl = ordinal)
    (hWords : ∀ g, SameWarp l lead g → ∀ q : Fin 4, ∀ k < 32, ∀ v,
      TcMma.LastWrote l Assumptions.all X
        (tcDataCell l g .s32x32b (scoreAddress l g stage q) k) v → v.bytes = 4) :
    ∀ g (hWarp : SameWarp l lead g), Nonempty (PackedScorePrefix l X g mode stage 4
      (input g hWarp)) :=
  warpRepeatedScoresOfMaximal hp hMax hGuard hLayout lead ordinal mode stage input hAddresses hRank
    hWords (fun _ _ q _ he => repeatedLoadedScoreWidth hp hMax.1 hFrame mode q he)

/-- Every packed word can be interpreted as the actual finite score of its column. -/
theorem PackedScorePrefix.scoreColumnsOfFootprint {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g : Nat} {mode : Repeated} {stage : Fin 2}
    {F : List (Nat × Value)} {input : OpeningTripCursor l X g (scorePc mode.round 0) F}
    (c : PackedScorePrefix l X g mode stage 4 input) :
    ∃ scores : Nat → ℝ, ∀ (q : Fin 4) (k : Fin 32), (c.words q)[k.val]? =
      some (.float .f32 (scores (32*q.val+k.val))) := by
  have hScores (q : Fin 4) (k : Fin 32) :
      ∃ value : ℝ, (c.words q)[k.val]? = some (.float .f32 value) := by
    obtain ⟨_,_,_,_,_,_,hWords⟩ :=
      scoreLoadWordsOfLaunch hp hX hFrame mode.round q (c.score q q.isLt)
    exact ⟨_,hWords k⟩
  let values (q : Fin 4) (k : Fin 32) := Classical.choose (hScores q k)
  let scores (i : Nat) :=
    values ⟨i/32%4,Nat.mod_lt _ (by decide)⟩ ⟨i%32,Nat.mod_lt _ (by decide)⟩
  refine ⟨scores,fun q k => ?_⟩
  have hQuarter : (32*q.val+k.val)/32%4 = q.val := by
    have := q.isLt
    have := k.isLt
    rw [show (32*q.val+k.val)/32 = q.val by omega,Nat.mod_eq_of_lt q.isLt]
  have hWord : (32*q.val+k.val)%32 = k.val := by
    have := k.isLt
    omega
  have hIndex : scores (32*q.val+k.val) = values q k := by
    unfold scores
    rw [show (⟨_,Nat.mod_lt _ (by decide)⟩ : Fin 4) = q from Fin.ext hQuarter,
      show (⟨_,Nat.mod_lt _ (by decide)⟩ : Fin 32) = k from Fin.ext hWord]
  rw [hIndex]
  exact Classical.choose_spec (hScores q k)

end PTX.Kernels.TmlFa4Fwd.Softmax

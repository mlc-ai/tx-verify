-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedBodyInputs
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedVisitNext
import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasStageAcquire
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Thread Correction

theorem BiasedStageMember.ofSameWarp {l : Launch} {cta g h : Nat} {stage : Fin 2}
    (hm : BiasedStageMember l cta stage g) (hw : SameWarp l g h) :
    BiasedStageMember l cta stage h := by
  have e : warpIndex l g = warpIndex l h := hw.2
  exact ⟨hw.1.2.1,hw.1.2.2 ▸ hm.2.1,e ▸ hm.2.2.1,e ▸ hm.2.2.2⟩

theorem warpOf_sameWarp {l : Launch} {g h : Nat} (hw : SameWarp l g h) :
    warpOf l h = warpOf l g := by
  have e : warpIndex l g = warpIndex l h := hw.2
  simp only [warpOf,e]

/-- More Tensor Memory collectives before one position than before another order them. -/
theorem lt_of_countP_take_lt {X : Execution} {g i j : Nat} {mark : Event → Bool}
    (h : ((X.tr g).take i).countP mark < ((X.tr g).take j).countP mark) : i < j := by
  by_contra hle
  have hs : ((X.tr g).take j).Sublist ((X.tr g).take i) :=
    (List.take_prefix_take_left (Nat.le_of_not_lt hle)).sublist
  exact absurd (hs.countP_le (p := mark)) (Nat.not_le_of_lt h)

theorem lt_of_tcCount_lt {X : Execution} {g i j : Nat}
    (h : ((X.tr g).take i).countP isTcColl < ((X.tr g).take j).countP isTcColl) : i < j :=
  lt_of_countP_take_lt h

/-- A whole stage at the heads of the same repeated biased visit passes its score acquire,
score loads, Bias acquire and Bias rendezvous, and each warp then reaches the correction join.
Score and Bias readiness are needed only for lanes still waiting for them. -/
theorem stageBiasedJoinsOfHeads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta : Nat} (hc : cta < l.grid) (stage : Fin 2) (visit : Nat)
    (block floor counter : Nat → Nat) (barsW electsW : Nat → Nat)
    (maximum : Nat → Option ℝ) (sum : Nat → ℝ)
    (heads : ∀ g, BiasedStageMember l cta stage g →
      BiasedLoopHead p l X g (warpOf l g) visit (block g) (floor g) (counter g)
        (barsW (warpIndex l g)) (electsW (warpIndex l g)) (maximum g) (sum g))
    (hScore : ∀ g, BiasedStageMember l cta stage g →
      okPolls (Scores.scoreReadyObject l (g/l.block) stage) (X.tr g) = visit →
      OpeningPollReady X (Scores.scoreReadyObject l (g/l.block) stage) (visit%2))
    (hBias : ∀ g, BiasedStageMember l cta stage g →
      (X.tr g).countP (Execution.isBarId (11+stage.val)) = visit →
      ∀ {t}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
        OpeningPollReady X (waitLoc l g stage 5) (visit%2)) :
    ∃ Y₁, Maximal l kernel Assumptions.all m Y₁ ∧ Y₁.tr = X.tr ∧ Y₁.objects = X.objects ∧
      ∀ g (hm : BiasedStageMember l cta stage g),
        ∃ Y₂, Maximal l kernel Assumptions.all m Y₂ ∧ Y₂.tr = X.tr ∧ Y₂.objects = X.objects ∧
          ∃ start, ∃ bias : Nat → Option ℝ, ∃ dot : Nat → ℝ,
          ∃ J : BiasedVisitJoin p l Y₁ Y₂ g (warpOf l g) visit start
            ((block g+(2^32-1))%2^32) (counter g) (barsW (warpIndex l g))
            (electsW (warpIndex l g)) (maximum g) (sum g) bias dot,
            (heads g hm).cursor.pos < J.join.cursor.pos ∧ (heads g hm).cursor.pos < start ∧
            (laneOf l g = 0 → Y₁.get (g,start-1) = some ⟨5278,
              .arrive (signalLoc l g stage (biasReleaseSite true)) 0 1 true .cta⟩) := by
  classical
  have hFootprint := frame X hMax.1
  -- score returns of every lane
  have returned (g : Nat) (hm : BiasedStageMember l cta stage g) :=
    (heads g hm).scoreReturnedOfPending hp hMax hm.1 hm.warp
      (by rw [hm.stage]; exact hScore g hm)
  let R (g : Nat) (hm : BiasedStageMember l cta stage g) := Classical.choice (returned g hm)
  -- one warp's rows at a common warp index
  let rowsAt (lead : Nat) (hl : BiasedStageMember l cta stage lead) (g : Nat)
      (hw : SameWarp l lead g) :
      BiasedScoreReturned p l X g (warpOf l lead) visit (block g) (floor g) (counter g)
        (barsW (warpIndex l lead)) (electsW (warpIndex l lead)) (maximum g) (sum g) := by
    have e : warpIndex l lead = warpIndex l g := hw.2
    have ew := warpOf_sameWarp hw
    rw [← ew,e]
    exact R g (hl.ofSameWarp hw)
  have hSelf (g : Nat) (hm : BiasedStageMember l cta stage g) :
      rowsAt g hm g ⟨⟨hm.1,hm.1,rfl⟩,rfl⟩ = R g hm := rfl
  have scores (g : Nat) (hm : BiasedStageMember l cta stage g) :
      Nonempty (PackedScorePrefix l X g .biased (stageOf (warpOf l g)) 4 (R g hm).loadInput) := by
    have h := warpBiasedScoresOfReturned hp hMax hFootprint (rowsAt g hm) g
      ⟨⟨hm.1,hm.1,rfl⟩,rfl⟩
    rwa [hSelf g hm] at h
  let S (g : Nat) (hm : BiasedStageMember l cta stage g) := Classical.choice (scores g hm)
  -- Bias acquires
  have rows (g : Nat) (hm : BiasedStageMember l cta stage g) :=
    (R g hm).biasOfPending hp hMax hm.1 hm.warp (S g hm)
      (by rw [hm.stage]; exact hBias g hm)
  let B (g : Nat) (hm : BiasedStageMember l cta stage g) := Classical.choice (rows g hm)
  -- the stage rendezvous
  obtain ⟨Y₁,hY₁,hT₁,hO₁,_,out⟩ := stageBiasedBodiesOfThreadRows hp hMax hFootprint hc stage
    visit block floor counter (fun g => barsW (warpIndex l g)) (fun g => electsW (warpIndex l g))
    maximum sum B
  choose biasF after hAEnd hAPos hAArr hACnt hAUnp using out
  have packed (g : Nat) (hm : BiasedStageMember l cta stage g) :=
    ((holds_append ..).mp ((holds_append ..).mp (after g hm).checkpoint.2.2.2.2).2).1
  have dots (g : Nat) (hm : BiasedStageMember l cta stage g) :=
    (B g hm).scores.biasedFmaInputsOfFootprint hp hMax.1 hFootprint (packed g hm)
  choose dotF hDot using dots
  refine ⟨Y₁,hY₁,hT₁,hO₁,?_⟩
  intro g hm
  let bias (h : Nat) := if hh : BiasedStageMember l cta stage h then biasF h hh else fun _ => none
  let dot (h : Nat) := if hh : BiasedStageMember l cta stage h then dotF h hh else fun _ => 0
  have same (h : Nat) (hw : SameWarp l g h) : warpIndex l h = warpIndex l g := hw.2.symm
  obtain ⟨Y₂,hY₂,hT₂,hO₂,joins⟩ := warpBiasedJoinOfBodies hp hY₁ (frame Y₁ hY₁.1) (warpOf l g)
    hm.warp.symm visit (barsW (warpIndex l g)) (electsW (warpIndex l g))
    (fun h => (block h+(2^32-1))%2^32) floor counter maximum sum bias dot
    (fun h hw => after h (hm.ofSameWarp hw))
    (fun h hw => biasBodyScale hp
      ((holds_append ..).mp (after h (hm.ofSameWarp hw)).checkpoint.2.2.2.2).1.1)
    (fun h hw i => by
      simp only [bias,dite_eq_left (hm.ofSameWarp hw)]
      exact hAUnp h (hm.ofSameWarp hw) i)
    (fun h hw pair hpair => by
      simp only [dot,dite_eq_left (hm.ofSameWarp hw)]
      exact hDot h (hm.ofSameWarp hw) pair hpair)
    (fun h hw => biasBodyPrior (by rw [hm.warp,same h hw])
      ((holds_append ..).mp ((holds_append ..).mp
        (after h (hm.ofSameWarp hw)).checkpoint.2.2.2.2).2).2)
    (fun h hw => by
      obtain ⟨c1,c2,c3,c4,c5,c6⟩ := hACnt h (hm.ofSameWarp hw)
      exact ⟨c1,c2.trans (congrArg barsW (same h hw)),c3.trans (congrArg electsW (same h hw)),
        c4,c5,c6⟩)
  obtain ⟨J⟩ := joins g ⟨⟨hm.1,hm.1,rfl⟩,rfl⟩
  refine ⟨Y₂,hY₂,hT₂.trans hT₁,hO₂.trans hO₁,_,bias g,dot g,J,?_,?_,?_⟩
  · apply lt_of_tcCount_lt (X := X)
    have hHead := (heads g hm).counts.1
    have hJoin := J.counts.1
    rw [hT₂,hT₁] at hJoin
    rw [hHead,hJoin]
    omega
  · apply lt_of_tcCount_lt (X := X)
    have hHead := (heads g hm).counts.1
    have hBody := (hACnt g hm).1
    rw [hT₁] at hBody
    rw [hHead,hBody]
    omega
  · intro hLead
    have e := hAArr g hm hLead
    rw [hAPos g hm,ite_eq_left hLead]
    exact e

end PTX.Kernels.TmlFa4Fwd.Softmax

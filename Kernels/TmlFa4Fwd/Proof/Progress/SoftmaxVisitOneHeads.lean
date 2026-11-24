-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxVisitOneHead
public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedOpeningAck
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityStores
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningBiasReturn

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue

/-- Two threads of one CTA with the same warp index are in the same warp. -/
private theorem sameWarpOfMembers {l : Launch} {cta g h : Nat} {stage : Fin 2}
    (hg : Softmax.BiasedStageMember l cta stage g) (hh : Softmax.BiasedStageMember l cta stage h)
    (hw : warpIndex l g = warpIndex l h) : SameWarp l g h :=
  ⟨⟨hg.1,hh.1,hg.2.1.trans hh.2.1.symm⟩,hw⟩

/-- The base case of the softmax visit induction. Every lane of a softmax stage of a scheduled
CTA with two or more KV blocks reaches the biased loop head of visit one, and the warp-barrier
and election counts there depend only on the warp. Each lane has already arrived on the main
probability object of the opening visit, and the elected lane of its opening tail election also
on the tail probability object. Stage one needs the first repeated statistics publication of
stage zero, which frees its opening acknowledgement. -/
theorem visitOneBiasedHeads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ cta) (hi : cta < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch cta).1) (stage : Fin 2)
    (published : stage = 1 → SoftmaxStagePublishedThrough l X cta 0 1) :
    let tile := (assignedCoordinates p batch cta).1
    let blocks := Mma.trips p batch tile
    let cap := blocks-Softmax.stageGeometryBlocks p batch tile stage+10
    let past := p.kLength batch-p.qLength batch+256*tile
    ∃ barsW electsW : Nat → Nat, ∀ g, Softmax.BiasedStageMember l cta stage g →
      ∃ maximum sum, ∃ head : Softmax.BiasedLoopHead p l X g (Softmax.warpOf l g) 1 (blocks-1)
          (past/128) (2^32-(blocks-Softmax.firstPlainSplit blocks cap)) (barsW (warpIndex l g))
          (electsW (warpIndex l g)) maximum sum,
        head.blocks = blocks ∧ head.split = Softmax.firstPlainSplit blocks cap ∧
        head.pastTile = past ∧
        1 ≤ ((X.tr g).take head.cursor.pos).countP
          (arrivesOn (Thread.Scores.probabilityObject l cta stage 0)) ∧
        (laneOf l g = 0 → 1 ≤ ((X.tr g).take head.cursor.pos).countP
          (arrivesOn (Thread.Loader.biasEmptyObject l cta stage))) ∧
        ∃ i inst leader, i < head.cursor.pos ∧ X.Elect (g,i) 4859 (2^32-1) inst leader ∧
          (laneOf l g = leader → 1 ≤ ((X.tr g).take head.cursor.pos).countP
            (arrivesOn (Thread.Scores.probabilityObject l cta stage 1))) := by
  intro tile blocks cap past
  classical
  have election (g : Nat) (hm : Softmax.BiasedStageMember l cta stage g) :
      Nonempty (Softmax.OpeningProbabilityElection p l X g stage) := by
    obtain ⟨hg,hCta,_,hRole⟩ := hm
    subst hCta
    exact openingProbabilityTailElectionOfMaximal hp hMax (frame X hMax.1) hg stage hRole hb lo hi
  have acknowledged (g : Nat) (hm : Softmax.BiasedStageMember l cta stage g) :
      Nonempty (Softmax.OpeningProbabilityAck l X g) := by
    obtain ⟨hg,hCta,_,hRole⟩ := hm
    subst hCta
    by_cases hOne : stage.val = 1
    · exact openingSecondAckOfRepeatedFirstPublications hp hMax frame hg (hRole.trans hOne) hb
        lo hi multiple (published (Fin.ext hOne))
    · exact openingProbabilityAckOfMaximal hp hMax (frame X hMax.1) hg stage hRole hb lo hi
        (fun h => absurd h hOne)
  let el (g : Nat) (hm : Softmax.BiasedStageMember l cta stage g) :=
    Classical.choice (election g hm)
  let base (g : Nat) (hm : Softmax.BiasedStageMember l cta stage g) : Nat :=
    elections X g ((el g hm).barrier.wait.tail.main.main.stored.wait.statistics.index+10)
  let electsW (w : Nat) : Nat :=
    if h : ∃ g, Softmax.BiasedStageMember l cta stage g ∧ warpIndex l g = w then
      base h.choose h.choose_spec.1+1 else 0
  refine ⟨fun _ => 1,electsW,fun g hm => ?_⟩
  have hw : ∃ h, Softmax.BiasedStageMember l cta stage h ∧ warpIndex l h = warpIndex l g :=
    ⟨g,hm,rfl⟩
  have hBase : electsW (warpIndex l g) = base g hm+1 := by
    simp only [electsW,dite_eq_left hw]
    have hs := sameWarpOfMembers hw.choose_spec.1 hm hw.choose_spec.2
    exact congrArg (·+1) ((el _ hw.choose_spec.1).electionsAgree hMax.1 hs (el g hm))
  let c := el g hm
  have ⟨hg,hCta,_,hRole⟩ := hm
  subst hCta
  obtain ⟨maximum,sum,head,hBlocks,hSplit,hPast,hAfter⟩ :=
    (Classical.choice (acknowledged g hm)).visitOneHead hp hMax
      (frame X hMax.1) hg stage hRole hb lo hi multiple c
  obtain ⟨head',hPos,hBlocks',hSplit',hPast'⟩ := head.recast rfl
    (show 1 = (fun _ => 1) (warpIndex l g) from rfl) hBase.symm
  refine ⟨maximum,sum,head',hBlocks'.trans hBlocks,hSplit'.trans hSplit,hPast'.trans hPast,?_,
    fun hLane => ?_,c.barrier.wait.tail.main.main.stored.wait.statistics.index+10,c.label,c.leader,
    by omega,c.elected,fun hLeader => ?_⟩
  · exact Softmax.probabilityArrivalBefore c.barrier.wait.tail.main.credited (by omega)
  · obtain ⟨i,_,hGet⟩ := openingBiasLeaderCreditOfMaximal hp hMax (frame X hMax.1) hg hb lo hi
      stage hRole hLane
    have hLe : i+1 ≤ c.barrier.wait.tail.main.main.stored.wait.statistics.index+10 := by
      by_contra hGt
      have := c.laterEvents (by omega) hGet
      simp at this
    have h1 := countP_take_succ
      (p := arrivesOn (Thread.Loader.biasEmptyObject l (g/l.block) stage)) hGet
      (by simp [arrivesOn,sourceArrive])
    have h2 := countP_take_mono (arrivesOn (Thread.Loader.biasEmptyObject l (g/l.block) stage))
      (X.tr g) (show i+1+1 ≤ head'.cursor.pos by omega)
    omega
  · exact Softmax.probabilityArrivalBefore
      (c.creditAtElectionOfMaximal hp hMax hg hRole hLeader) (by omega)

end PTX.Kernels.TmlFa4Fwd.Progress

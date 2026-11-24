-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSecondQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondScoreIssue
import Kernels.TmlFa4Fwd.Proof.Progress.Async
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreOrdinal
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialScoreNotification

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier Prologue Thread.Output
open Thread.Scores (ScoreCommit OpeningScoreCommit scoreCommitOrdinal scoreReadyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

/-- The active MMA warp issues its complete second QK packet and matching score commit. -/
theorem openingSecondScoreAndKeyReturnOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ shuffles votes ends,
      Mma.OpeningInitialKeyReturnReached l X g shuffles votes ends ∧
      ∃ issuer first,
      SameWarp l g issuer ∧
      (∀ j : Fin 8, Thread.Mma.InitialQueryFragment X 1 (issuer,first+j.val) ∧
        X.MmaIssue (issuer,first+j.val) (scoreColumn 1) (Mma.qkOperands l issuer 1 j 0)
          (decide (j.val ≠ 0)) (List.replicate 4 0)) ∧
        ScoreCommit l X (issuer,first+9) (issuer/l.block) 1
          (Mma.commitSpec l issuer (l.sharedBase+88)) 0 ∧
        OpeningScoreCommit X (issuer,first+9) 1 (Mma.commitSpec l issuer (l.sharedBase+88)) := by
  obtain ⟨_,_,_,hReached,_⟩ :=
    openingScoreCommitAndQueryOperandsOfMaximal hp hMax hFrame hg hw hb hLo hHi
  have hReady := openingSecondQueryReadyPhaseOfMaximal hp hMax hFrame
    (NamedBar.cta_lt hg) hb hLo hHi
  exact ⟨_,_,_,Mma.openingSecondScoreAndKeyReturnFromReadyWarp hp hMax hg hReached hReady⟩

/-- The active MMA warp issues its complete second QK packet and matching score commit. -/
theorem openingSecondScoreIssueOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ issuer first,
      SameWarp l g issuer ∧
      (∀ j : Fin 8, Thread.Mma.InitialQueryFragment X 1 (issuer,first+j.val) ∧
        X.MmaIssue (issuer,first+j.val) (scoreColumn 1) (Mma.qkOperands l issuer 1 j 0)
          (decide (j.val ≠ 0)) (List.replicate 4 0)) ∧
        ScoreCommit l X (issuer,first+9) (issuer/l.block) 1
          (Mma.commitSpec l issuer (l.sharedBase+88)) 0 ∧
        OpeningScoreCommit X (issuer,first+9) 1 (Mma.commitSpec l issuer (l.sharedBase+88)) := by
  obtain ⟨_,_,_,_,hScore⟩ :=
    openingSecondScoreAndKeyReturnOfMaximal hp hMax hFrame hg hw hb hLo hHi
  exact hScore

/-- The second opening QK packet completes and delivers its actual stage-one score arrival. -/
theorem openingSecondScoreNotifiedOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ (issuer first : Nat) (spec : TcCommit.Spec), SameWarp l g issuer ∧
      (∀ i : Fin 8, Thread.Mma.InitialQueryFragment X 1 (issuer,first+i.val) ∧
        X.async.mmaDone (issuer,first+i.val) = true) ∧
      ScoreCommit l X (issuer,first+9) (g/l.block) 1 spec 0 ∧
      scoreCommitOrdinal l X (g/l.block) 1 (issuer,first+9) = 0 ∧
      ∃ r ∈ X.objects (scoreReadyObject l (g/l.block) 1),
        r.id = .async (issuer,first+9) (.tcNotify 0) ∧ r.action = .arrive 1 0 ∧ r.fault = none := by
  obtain ⟨issuer,first,hWarp,hPacket,hScore,hOpening⟩ :=
    openingSecondScoreIssueOfMaximal hp hMax hFrame hg hw hb hLo hHi
  rw [← hWarp.1.2.2] at hScore
  obtain ⟨hDone,hNotify⟩ := mmaAndCommitsDrained hp hMax hFrame
  have hOrdinal := Thread.Scores.openingScoreOrdinal hp hMax.1 hOpening
  rw [← hWarp.1.2.2] at hOrdinal
  refine ⟨issuer,first,_,hWarp,?_,hScore,hOrdinal,?_⟩
  · intro i
    exact ⟨(hPacket i).1,hDone _ (.inl ⟨_,_,_,_,(hPacket i).2⟩)⟩
  · let obj := scoreReadyObject l (g/l.block) 1
    have hArrived := hNotify _ _ 0 obj hScore.1 hScore.2
    obtain ⟨_,he⟩ := hScore.1
    have hAction : objectAction X X.async obj (.async (issuer,first+9) (.tcNotify 0)) =
        some (.arrive 1 0) := by
      simp [objectAction,he,hScore.2,hArrived,obj]
    obtain ⟨r,hr,hId⟩ := (hMax.1.tma.2.2.1 obj).2.2 _ _ hAction
    have hMatch := ((hMax.1.tma.2.2.1 obj).2.1 r hr).1
    rw [hId,hAction] at hMatch
    obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp hr
    exact ⟨r,hr,hId,(Option.some.inj hMatch).symm,
      Protocol.Scores.initialScoreNotificationClean hp hMax.1 1 hn hId hScore hOrdinal⟩

/-- A pending stage-one softmax lane sees the completed generation of its first score. -/
theorem openingSecondScoreReadyPhaseForPendingLane {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g/4 = 1) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hMissing : ¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (g,j) 1) :
    let log := X.objects (scoreReadyObject l (g/l.block) 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  let mma := g/l.block*l.block+384
  have hLane : 384 < l.block := by rw [hp.block]; decide
  have hm : mma < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
  obtain ⟨hMmaCta,hMmaLane⟩ := NamedBar.lane_cta (c := g/l.block)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  have hMmaWarp : warpIndex l mma = 12 := by unfold warpIndex mma; rw [hMmaLane]
  obtain ⟨_,_,_,_,_,hCommit,hOrdinal,_,hr,hId,hAction,_⟩ :=
    openingSecondScoreNotifiedOfMaximal hp hMax hFrame hm hMmaWarp hb
      (hMmaCta.symm ▸ hLo) (hMmaCta.symm ▸ hHi)
  rw [show mma/l.block = g/l.block from hMmaCta] at hCommit hOrdinal hr
  obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp hr
  exact Protocol.Scores.initialScoreReadyPhaseForPendingLane hp hMax.1 hg 1 hw
    hn hId hAction hCommit hOrdinal hMissing

end PTX.Kernels.TmlFa4Fwd.Progress

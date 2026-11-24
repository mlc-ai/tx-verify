-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Async
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningQK
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreOrdinal
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialScoreNotification

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier Prologue
open Thread.Scores (ScoreCommit scoreCommitOrdinal scoreReadyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
include hp hMax hFrame

/-- In every active request group, the eight opening QK fragments complete and
their score commit delivers a unit arrival to the stage-zero score object. -/
theorem openingScoreNotifiedOfMaximal (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ (issuer first : Nat) (spec : TcCommit.Spec), SameWarp l g issuer ∧
      (∀ i : Fin 8, Thread.Mma.InitialQueryFragment X 0 (issuer,first+i.val) ∧
        X.async.mmaDone (issuer,first+i.val) = true) ∧
      ScoreCommit l X (issuer,first+9) (g/l.block) 0 spec 0 ∧
      scoreCommitOrdinal l X (g/l.block) 0 (issuer,first+9) = 0 ∧
      ∃ r ∈ X.objects (scoreReadyObject l (g/l.block) 0),
        r.id = .async (issuer,first+9) (.tcNotify 0) ∧ r.action = .arrive 1 0 ∧
          r.fault = none := by
  obtain ⟨issuer, first, hWarp, hPacket, hScore, hOpening⟩ :=
    openingScoreCommitOfMaximal hp hMax hFrame hg hw hb hLo hHi
  rw [← hWarp.1.2.2] at hScore
  obtain ⟨hDone, hNotify⟩ := mmaAndCommitsDrained hp hMax hFrame
  have hOrdinal := Thread.Scores.openingScoreOrdinal hp hMax.1 hOpening
  rw [← hWarp.1.2.2] at hOrdinal
  refine ⟨issuer, first, _, hWarp, ?_, hScore, hOrdinal, ?_⟩
  · intro i
    have hi := (hPacket i).2
    exact ⟨(hPacket i).1, hDone _ (.inl ⟨_, _, _, _, hi⟩)⟩
  · let obj := scoreReadyObject l (g/l.block) 0
    have hArrived := hNotify _ _ 0 obj hScore.1 hScore.2
    obtain ⟨_, he⟩ := hScore.1
    have hAction : objectAction X X.async obj (.async (issuer,first+9) (.tcNotify 0)) =
        some (.arrive 1 0) := by
      simp [objectAction, he, hScore.2, hArrived, obj]
    obtain ⟨r, hr, hid⟩ := (hMax.1.tma.2.2.1 obj).2.2 _ _ hAction
    have hMatch := ((hMax.1.tma.2.2.1 obj).2.1 r hr).1
    rw [hid, hAction] at hMatch
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hr
    exact ⟨r, hr, hid, (Option.some.inj hMatch).symm,
      Protocol.Scores.initialScoreNotificationClean hp hMax.1 0 hn hid hScore hOrdinal⟩

/-- The first score is ready for each pending lane of the stage-zero softmax group. -/
theorem openingScoreReadyPhaseForPendingLane (hg : g < l.threads) (hw : warpIndex l g < 4)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMissing : ¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (g,j) 0) :
    let log := X.objects (scoreReadyObject l (g/l.block) 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  let mma := g/l.block*l.block+384
  have hLane : 384 < l.block := by rw [hp.block]; decide
  have hm : mma < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
  obtain ⟨hMmaCta, hMmaLane⟩ := NamedBar.lane_cta (c := g/l.block)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  have hMmaWarp : warpIndex l mma = 12 := by
    unfold warpIndex mma
    rw [hMmaLane]
  obtain ⟨issuer, first, spec, _, _, hCommit, hOrdinal, r, hr, hId, hAction, _⟩ :=
    openingScoreNotifiedOfMaximal hp hMax hFrame hm hMmaWarp hb
      (hMmaCta.symm ▸ hLo) (hMmaCta.symm ▸ hHi)
  rw [show mma/l.block = g/l.block from hMmaCta] at hCommit hOrdinal hr
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hr
  exact Protocol.Scores.initialScoreReadyPhaseForPendingLane hp hMax.1 hg 0 (by omega)
    hn hId hAction hCommit hOrdinal hMissing

end PTX.Kernels.TmlFa4Fwd.Progress

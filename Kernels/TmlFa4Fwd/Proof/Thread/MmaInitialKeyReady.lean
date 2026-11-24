-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyAcquire
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreSource
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (initialQkBlock qkPc slotWait slotElect pendingReadyOrdinal
  initialReadyPollOperands commitSite qkCommitSite scoreCommitLeader secondOutputCommitLeader)

/-- The initial score commit and final second output commit use the same elected lane. -/
theorem firstQkSecondOutputIssuer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer commit wait : Nat}
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit wait)
    {final : EvId} {s : TcCommit.Spec} (hFinal : SecondOutputCommit X final s)
    (hOwner : producer / l.block = final.1 / l.block) : producer = final.1 := by
  let block := Softmax.firstQkBlock stage
  let pc := (commitSite (qkCommitSite block)).pc
  have hLate : 173 < pc := by fin_cases stage <;> decide
  have hHint : pc ∉ registerHintSites := by fin_cases stage <;> decide
  have hRole := roleBodyPcOfEvent hp hX hPhase.commitEvent hLate hHint
  have hBound : 2197 ≤ pc ∧ pc < 2768 := by fin_cases stage <;> decide
  have hScoreWarp : warpIndex l producer = 12 := by
    change roleBodyPc (warpIndex l producer) pc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  have hWarp : SameWarp l producer final.1 :=
    ⟨⟨hPhase.sameCta.1, event_thread_lt hX hFinal.decoded, hOwner⟩,
      hScoreWarp.trans (hFinal.issuerWarp hp hX).symm⟩
  obtain ⟨_, _, _, he, hl⟩ := scoreCommitLeader hp hX block hPhase.commitEvent
  obtain ⟨_, _, _, he', hl'⟩ := secondOutputCommitLeader hp hX hFinal.decoded
  exact sameWarp_eq_of_lane_eq hWarp
    (hl.trans ((PTX.Kernels.TmlFa4Fwd.Mma.sameLeader hX hWarp he he').trans hl'.symm))

/-- An actual initial fragment on the output issuer's lane follows its phase-zero K acquire. -/
theorem InitialQueryFragment.keyReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {mma final : EvId} {spec : TcCommit.Spec}
    (hIssue : InitialQueryFragment X stage mma) (hFinal : SecondOutputCommit X final spec)
    (hLane : mma.1 = final.1) :
    ∃ wait, ReadyPoll l X mma.1 wait 0 0 true .cta ∧
      TraceBefore X (mma.1, wait) mma ∧ (atPrefix l X mma.1 wait).kvAcquires 0 = 0 := by
  obtain ⟨g, j⟩ := mma
  obtain ⟨f, n⟩ := final
  change g = f at hLane
  subst f
  obtain ⟨step, d, op, accum, mask, he⟩ := hIssue
  have hGate : (slotWait 0).pc + 3 ≤ qkPc (initialQkBlock stage) + step.val ∧
      qkPc (initialQkBlock stage) + step.val ≤ (slotElect 0).pc := by
    fin_cases stage <;> fin_cases step <;> decide
  obtain ⟨wait, hBefore, _, _, _, _, hKey, _⟩ := pendingReadyOrdinal hp hX 0 he hGate
  obtain ⟨rfl, rfl, rfl, rfl⟩ := initialReadyPollOperands hp hX hKey
  exact ⟨wait, ⟨_, hKey, rfl⟩, ⟨rfl, hBefore, len_of_get he⟩,
    initialKeyWaitOrdinal hp hX hFinal hKey⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma

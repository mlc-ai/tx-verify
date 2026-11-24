-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalProbabilityGate
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy Scores
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem earlierScoresBoundAtTailWait {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {g i wait parity : Nat}
    (hWait : X.get (g,wait) = some ⟨terminalProbabilityHead stage packet,
      .wait (probabilityObject l (g/l.block) stage packet) parity true true .cta⟩) :
    scoreCommitOrdinal l X (g/l.block) stage (g,i) ≤
      okPolls (probabilityObject l (g/l.block) stage packet) ((X.tr g).take wait)+1 := by
  let cta := g/l.block
  let mark := scoreCommitOn (scoreReadyObject l cta stage)
  let n := ((X.tr g).take i).countP mark
  change n ≤ _
  by_cases hN : n = 0
  · omega
  obtain ⟨j,_,⟨site,kind⟩,he,hMark,hOrdinal⟩ :=
    Flow.exists_nth mark (X.tr g) (k := i) (n := n-1) (by change n-1+1 ≤ n; omega)
  cases kind <;> simp [mark,scoreCommitOn] at hMark
  case tc op =>
    cases op <;> simp at hMark
    rename_i spec
    have hScore : ScoreCommit l X (g,j) cta stage spec 0 := ⟨⟨_,he⟩,hMark⟩
    have hBound := terminalProbabilityPollCoversScore hp hX packet hScore hWait
    change scoreCommitOrdinal l X cta stage (g,j) = n-1 at hOrdinal
    rw [hOrdinal] at hBound
    change n ≤ okPolls (probabilityObject l cta stage packet) ((X.tr g).take wait)+1
    omega

/-- The matching terminal packet acquire for an actual tail PV fragment covers
all earlier same-stage score commits. -/
theorem PvInstruction.tailPacketProbabilityAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {i : EvId} {frag : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hIssue : PvInstruction X i (firstPvBlock false stage) frag d op acc mask)
    (hPacket : packet.val = 0 ∨ 6 ≤ frag.val) :
    ∃ wait, MmaProbabilityAcquire l X i stage packet wait := by
  obtain ⟨g,j⟩ := i
  let select : Fin 4 := ⟨2*stage.val+packet.val,by
    have := stage.isLt
    have := packet.isLt
    omega⟩
  have hBounds : probabilityPc select true+3 ≤ pvPc (firstPvBlock false stage) frag ∧
      pvPc (firstPvBlock false stage) frag ≤ if select.val < 2 then 2594 else 2634 := by
    revert hPacket
    fin_cases stage <;> fin_cases packet <;> fin_cases frag <;> decide
  obtain ⟨k,_,loc,parity,hPoll,hResume⟩ :=
    tailProbabilityWaitBeforeGate hp hX select hIssue.decoded hBounds.1 hBounds.2
  have hHead : probabilityPc select true ∈
      [2141,2145,2210,2297,2335,2419,2450,2548,2586,2595,2626] := by
    fin_cases stage <;> fin_cases packet <;> decide
  have hAddr := mmaFixedWaitAddress hp hX hPoll hHead
  have hOff : fixedMmaWaitOffset (probabilityPc select true) = 96+8*stage.val+16*packet.val := by
    fin_cases stage <;> fin_cases packet <;> decide
  rw [hOff] at hAddr
  change loc = probabilityObject l (g/l.block) stage packet at hAddr
  subst loc
  have hSite : probabilityPc select true = terminalProbabilityHead stage packet := by
    fin_cases stage <;> fin_cases packet <;> decide
  have hPoll' : X.get (g,k) = some ⟨terminalProbabilityHead stage packet,
      .wait (probabilityObject l (g/l.block) stage packet) parity true true .cta⟩ := by
    simpa only [hSite] using hPoll
  exact ⟨(g,k),⟨_,parity,hPoll,rfl⟩,hResume,earlierScoresBoundAtTailWait hp hX stage packet hPoll'⟩

/-- The terminal joint probability acquire of an actual tail PV fragment. -/
theorem PvInstruction.tailJointProbabilityAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {i : EvId} {frag : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hIssue : PvInstruction X i (firstPvBlock false stage) frag d op acc mask) :
    ∃ wait, MmaProbabilityAcquire l X i stage 0 wait :=
  hIssue.tailPacketProbabilityAcquire hp hX stage 0 (.inl rfl)

end PTX.Kernels.TmlFa4Fwd.Thread

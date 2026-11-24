-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
public import Lemmas.Protocol.PollIndex
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Kernels.TmlFa4Fwd.Proof.CtaMemoryOrder
import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy
open _root_.PTX.Kernels.TmlFa4Fwd.Mma
open Scores (probabilityObject scoreCommitOrdinal scoreCommitBudgetAtProbabilityGate)

private def packetIndex (stage packet : Fin 2) : Fin 4 :=
  ⟨2*stage.val+packet.val, by have := stage.isLt; have := packet.isLt; omega⟩

/-- The MMA lane has a returning acquire of the selected physical probability packet. -/
structure MmaProbabilityAcquire (l : Launch) (X : Execution) (i : EvId)
    (stage packet : Fin 2) (wait : EvId) : Prop where
  event : ∃ e parity, X.get wait = some e ∧
    e.kind = .wait (probabilityObject l (i.1/l.block) stage packet) parity true true .cta
  resume : Resumes kernel X wait i
  coversScores : scoreCommitOrdinal l X (i.1/l.block) stage i ≤
    okPolls (probabilityObject l (i.1/l.block) stage packet) ((X.tr wait.1).take wait.2) + 1

private theorem acquireBeforeGateEvent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hLo : probabilityPc (packetIndex stage packet) false + 3 ≤ e.pc)
    (hHi : e.pc ≤ probabilityScoreElection (packetIndex stage packet)) :
    ∃ wait, MmaProbabilityAcquire l X (g,j) stage packet wait := by
  let select := packetIndex stage packet
  obtain ⟨k,hK,loc,parity,acq,scope,hGet,hLocalOrdinal⟩ :=
    probabilityWaitAtGateEvent hp hX select he ⟨hLo,hHi⟩
  have hSite : probabilityPc select false ∈
      [2141,2145,2210,2297,2335,2419,2450,2548,2586,2595,2626] := by
    fin_cases stage <;> fin_cases packet <;> decide
  have hOff : fixedMmaWaitOffset (probabilityPc select false) =
      96+8*stage.val+16*packet.val := by fin_cases stage <;> fin_cases packet <;> decide
  have hAddress := mmaFixedWaitAddress hp hX hGet hSite
  rw [hOff] at hAddress
  change loc = probabilityObject l (g/l.block) stage packet at hAddress
  subst loc
  have hCode : ∃ pr base reg, kernel.code[probabilityPc select false]? =
      some ⟨none,.mbarWait pr base 0 (.reg reg) true .cta⟩ := by
    have audit : ∀ slot : Fin 4, ∃ pr base reg, kernel.code[probabilityPc slot false]? =
        some ⟨none,.mbarWait pr base 0 (.reg reg) true .cta⟩ := by
      intro slot
      fin_cases slot
      · exact ⟨_,_,_,Flow.code_2297⟩
      · exact ⟨_,_,_,Flow.code_2335⟩
      · exact ⟨_,_,_,Flow.code_2419⟩
      · exact ⟨_,_,_,Flow.code_2450⟩
    exact audit select
  have hScope := actualPollScope hX hGet
  have hAcquire : acq = true := by
    obtain ⟨_,_,_,hCode⟩ := hCode
    rcases get_source hX hGet with ⟨_,hBad⟩ | ⟨s,ins,u,_,hs,hFire⟩
    · cases hBad
    change kernel.code[probabilityPc select false]? = some ins at hs
    rw [hCode] at hs
    obtain rfl := Option.some.inj hs.symm
    obtain ⟨_,_,_,_,_,hFlags,_⟩ := fires_wait_flags hFire
      (show (⟨probabilityPc select false,.wait (probabilityObject l (g/l.block) stage packet)
        parity true acq scope⟩ : Event).kind = _ from rfl)
    exact (Op.mbarWait.inj hFlags).2.2.2.2.1.symm
  subst acq
  subst scope
  obtain ⟨exit,hSpin⟩ := actualCanonicalPoll hX hGet
  have hTrace : TraceBefore X (g,k) (g,j) := ⟨rfl,hK,len_of_get he⟩
  have hOrdinal : scoreCommitOrdinal l X (g/l.block) stage (g,j) ≤
      1 + okPolls (probabilityObject l (g/l.block) stage packet) ((X.tr g).take k) := by
    apply (scoreCommitBudgetAtProbabilityGate hp hX stage packet select rfl).trans
    apply Nat.add_le_add_left
    rw [← hLocalOrdinal]
    apply List.countP_mono_left
    intro ev hMem hMark
    obtain ⟨pos,hEv⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
    obtain ⟨src,kind⟩ := ev
    cases kind <;> simp at hMark
    case wait target q ok a sc =>
      cases ok <;> simp at hMark
      subst src
      have h := mmaFixedWaitAddress hp hX (g := g) (index := pos) hEv hSite
      rw [hOff] at h
      change target = probabilityObject l (g/l.block) stage packet at h
      subst target
      simp [okPoll, sourceWaitSuccess]
  refine ⟨(g,k),⟨_,parity,hGet,rfl⟩,⟨hTrace,?_⟩,?_⟩
  · simp only [hGet,Option.map_some,Kind.resume]
    exact ⟨_,exit,_,parity,true,.cta,hGet,hSpin,hTrace⟩
  · simpa only [Nat.add_comm 1] using hOrdinal

/-- An actual repeated QK fragment has acquired both probability packets of its stage. -/
theorem QkInstruction.recurringProbabilityAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {block : Fin 4} {frag : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X i block frag d op accum mask)
    (hRepeat : 2 ≤ block.val) (packet : Fin 2) :
    ∃ wait, MmaProbabilityAcquire l X i (qkStage block) packet wait := by
  have hBounds : probabilityPc (packetIndex (qkStage block) packet) false + 3 ≤
      qkPc block+frag.val ∧
      qkPc block+frag.val ≤ probabilityScoreElection (packetIndex (qkStage block) packet) := by
    revert hRepeat
    fin_cases block <;> fin_cases packet <;> fin_cases frag <;> decide
  obtain ⟨g,j⟩ := i
  exact acquireBeforeGateEvent hp hX (qkStage block) packet hIssue.decoded
    hBounds.1 hBounds.2

/-- An actual steady PV fragment has acquired the early packet, and each of its
last two fragments has additionally acquired the late packet. -/
theorem PvInstruction.steadyProbabilityAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {i : EvId} {frag : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : PvInstruction X i (firstPvBlock true stage) frag d op accum mask)
    (hPacket : packet.val = 0 ∨ 6 ≤ frag.val) :
    ∃ wait, MmaProbabilityAcquire l X i stage packet wait := by
  have hBounds : probabilityPc (packetIndex stage packet) false + 3 ≤
      pvPc (firstPvBlock true stage) frag ∧
      pvPc (firstPvBlock true stage) frag ≤ probabilityScoreElection (packetIndex stage packet) :=
    by
      revert hPacket
      fin_cases stage <;> fin_cases packet <;> fin_cases frag <;> decide
  obtain ⟨g,j⟩ := i
  exact acquireBeforeGateEvent hp hX stage packet hIssue.decoded hBounds.1 hBounds.2

end PTX.Kernels.TmlFa4Fwd.Thread

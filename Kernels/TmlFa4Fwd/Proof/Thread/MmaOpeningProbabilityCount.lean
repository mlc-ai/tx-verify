-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyCursor
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow Epilogue Prologue
open Thread.Scores (probabilityObject)

/-- Opening QK setup has not consumed any of the four probability generations. -/
theorem openingProbabilityCountsAtKeyReturn {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g n shuffles votes : Nat} {ends : Nat → Option TState}
    (c : OpeningKeyReturnedWithTrip l X g n shuffles votes ends)
    {lane : Nat} (hl : lane < 32) (stage packet : Fin 2) :
    okPolls (probabilityObject l (warpLane l g lane/l.block) stage packet)
      ((X.tr (warpLane l g lane)).take (c.pos lane)) = 0 := by
  apply List.countP_eq_zero.mpr
  intro ev hMem hPoll
  let peer := warpLane l g lane
  obtain ⟨j,he⟩ := List.mem_iff_getElem?.mp hMem
  have hj := (List.getElem?_eq_some_iff.mp he).1
  rw [List.length_take] at hj
  have hEarlier : j < c.pos lane := by omega
  have hEvent : X.get (peer,j) = some ev := by
    rwa [List.getElem?_take_of_lt hEarlier] at he
  obtain ⟨pc,kind⟩ := ev
  cases kind <;> simp only [okPoll,sourceWaitSuccess,Bool.false_eq_true] at hPoll
  case wait loc q ok acq scope =>
    cases ok <;> simp at hPoll
    subst loc
    have hSite := (probabilityWaitSite hp hX stage packet hEvent).2
    have hFloor : ∀ (s b : Fin 2), ∀ k ∈ probabilityWaitSites s b, 2285 ≤ k := by decide
    have h0 := (c.recorded lane hl).returning_reach
    have hPath := h0.append (TraceReach.of_local (c.localSteps lane hl))
    rw [List.append_nil] at hPath
    have hHigh := eventReachesFloor (by decide : 2285 ∈ [2285,2534]) hPath
      ⟨_,hMem,hFloor stage packet pc hSite⟩
    have hPc := (c.checkpoint lane hl).1
    omega

end PTX.Kernels.TmlFa4Fwd.Mma

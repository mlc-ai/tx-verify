-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Assumption Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (initialQueryOperandsBeforeFinalCommit initialQkBlock
  qkPc slotWait slotElect pendingReadyOrdinal readyHead readyEvent ReadyUseSite
  tailValueWaitBeforeGate)

private theorem valueFloorCode :
    (kernel.code.drop 2545).all (fun i => staysPastEvent 2545 i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem valueFloorSegments : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (2545 ≤ seg.stop)
    | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem markValuePoll {pc : Nat} (h : pc = 2145 ∨ pc = 2545)
    (loc : Loc) (parity : Nat) :
    readyEvent ⟨pc, .wait loc parity true true .cta⟩ = some (loc, parity) := by
  have hm : (List.finRange 4).any (fun i => readyHead i == pc) = true := by
    rcases h with rfl | rfl <;> decide
  simp [readyEvent, hm]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem tailReadyUseOdd {g j parity : Nat} {loc : Loc} (hw : warpIndex l g = 12)
    (he : X.get (g,j) = some ⟨2545, .wait loc parity true true .cta⟩) :
    (((X.tr g).take j).filterMap readyEvent).length % 2 = 1 := by
  obtain ⟨slot,hLoc⟩ := Mma.readySlotOfProjection hp hX hw he (markValuePoll (.inr rfl) loc parity)
  subst loc
  have hPoll : Mma.ReadyPoll l X g j slot parity true .cta := ⟨_,he,rfl⟩
  obtain ⟨site,hGet,hUse⟩ := hPoll.useSite hp hX hw
  have hSite : site = 2545 := congrArg Event.pc (Option.some.inj (hGet.symm.trans he))
  simpa [hSite,ReadyUseSite,readyHead] using hUse

/-- The terminal V gate returns once. Two successful terminal observations would
require an intervening K acquire, whose earlier role position rules out that order. -/
theorem tailValueAcquireUnique {g a b pa pb : Nat} {la lb : Loc} (hw : warpIndex l g = 12)
    (ha : X.get (g,a) = some ⟨2545, .wait la pa true true .cta⟩)
    (hb : X.get (g,b) = some ⟨2545, .wait lb pb true true .cta⟩) : a = b := by
  let count := fun j => (((X.tr g).take j).filterMap readyEvent).length
  have mono {i j : Nat} (h : i ≤ j) : count i ≤ count j :=
    ((List.take_sublist_take_left (l := X.tr g) h).filterMap readyEvent).length_le
  have noEarlier {i j pi pj : Nat} {li lj : Loc}
      (hi : X.get (g,i) = some ⟨2545, .wait li pi true true .cta⟩)
      (hj : X.get (g,j) = some ⟨2545, .wait lj pj true true .cta⟩) : ¬ i < j := by
    intro hBefore
    have hOddI : count i % 2 = 1 := tailReadyUseOdd hp hX hw hi
    have hOddJ : count j % 2 = 1 := tailReadyUseOdd hp hX hw hj
    have hOne : count (i+1) = count i + 1 := by
      have hGet : (X.tr g)[i]? = some ⟨2545, .wait li pi true true .cta⟩ := hi
      simp [count,List.take_add_one,hGet,markValuePoll (.inr rfl) li pi]
    have hMon := mono (show i+1 ≤ j by omega)
    have hUse : count i + 1 < count j := by omega
    obtain ⟨k,_,hPoll,hRank⟩ := Mma.readyPollAtOrdinalBefore hp hX
      (event_thread_lt hX hi) hw hUse
    change count k = count i + 1 at hRank
    obtain ⟨site,hGet,hClass⟩ := hPoll.useSite hp hX hw
    change ReadyUseSite (count k) site at hClass
    have hEven : count k % 2 = 0 := by omega
    have hPos : 0 < count k := by omega
    have hSite : site = 2352 := by
      simpa [ReadyUseSite,readyHead,hEven,hPos,show count k ≠ 0 by omega] using hClass
    have hPrior := traceOrderOfPcFloor hX valueFloorCode valueFloorSegments hGet hi
      (show site < 2545 by omega) (show 2545 ≤ 2545 by decide)
    have hK := mono hPrior.le
    omega
  exact le_antisymm (Nat.le_of_not_gt (noEarlier hb ha)) (Nat.le_of_not_gt (noEarlier ha hb))

/-- The final output identifies the initial V acquire before any reached tail event. -/
theorem initialValueAcquireBeforeTailEvent {g target commit : Nat} {e : Event}
    {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X (g,commit) spec)
    (he : X.get (g,target) = some e) (hLo : 2548 ≤ e.pc) (hHi : e.pc ≤ 2646) :
    ∃ j, Mma.ReadyPoll l X g j 1 0 true .cta ∧
      TraceBefore X (g,j) (g,target) ∧
      (((X.tr g).take j).filterMap readyEvent).length = 1 := by
  have hCommitGet : X.get (g,commit) = some ⟨2646, .tc (.commit spec)⟩ := hCommit.decoded
  have hg := event_thread_lt hX hCommitGet
  have hw : warpIndex l g = 12 := by
    have hBody := roleBodyPcOfEvent hp hX hCommitGet (show 173 < 2646 by decide)
      (show 2646 ∉ registerHintSites by decide)
    change roleBodyPc (warpIndex l g) 2646 at hBody
    unfold roleBodyPc at hBody
    rcases hBody with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨tail, hTail, vl, vp, hValue, _⟩ := tailValueWaitBeforeGate hp hX he hLo hHi
  obtain ⟨base, hGroup⟩ :=
    initialQueryOperandsBeforeFinalCommit hp hX (.inr rfl) hCommitGet 0
  obtain ⟨_, _, _, _, _, hFirst, _⟩ := hGroup 0
  have hGate : (slotWait 0).pc + 3 ≤ qkPc (initialQkBlock 0) + (0 : Fin 8).val ∧
      qkPc (initialQkBlock 0) + (0 : Fin 8).val ≤ (slotElect 0).pc := by decide
  obtain ⟨key, _, kl, kp, acq, scope, hKey, _⟩ := pendingReadyOrdinal hp hX 0 hFirst hGate
  obtain ⟨rfl, rfl⟩ := PTX.Kernels.TmlFa4Fwd.Mma.readyGateAcquireFlags hX 0 hKey
  have hKeyGet : X.get (g,key) = some ⟨2145, .wait kl kp true true .cta⟩ := hKey
  have hk := traceOrderOfPcFloor hX valueFloorCode valueFloorSegments hKeyGet hValue
    (show 2145 < 2545 by decide) (show 2545 ≤ 2545 by decide)
  have hKeyMem : (kl, kp) ∈ ((X.tr g).take tail).filterMap readyEvent := by
    apply List.mem_filterMap.mpr
    refine ⟨⟨2145, .wait kl kp true true .cta⟩, ?_, markValuePoll (.inl rfl) kl kp⟩
    apply List.mem_of_getElem? (i := key)
    rw [List.getElem?_take_of_lt hk]
    exact hKeyGet
  have hTake : (X.tr g).take (tail + 1) =
      (X.tr g).take tail ++ [⟨2545, .wait vl vp true true .cta⟩] := by
    change (X.tr g)[tail]? = some ⟨2545, .wait vl vp true true .cta⟩ at hValue
    simp [List.take_add_one, hValue]
  have hTwo : 1 < (((X.tr g).take (tail + 1)).filterMap readyEvent).length := by
    have hNonempty := List.length_pos_of_mem hKeyMem
    rw [hTake, List.filterMap_append]
    simp only [List.filterMap_cons, markValuePoll (.inr rfl) vl vp, List.filterMap_nil,
      List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨index, hIndex, hPoll, hUse⟩ := Mma.readyPollAtOrdinalBefore hp hX hg hw hTwo
  exact ⟨index, hPoll, ⟨rfl, by omega, (List.getElem?_eq_some_iff.mp he).1⟩, hUse⟩

/-- An actual final O1 commit follows the initial slot-one V acquire, on either
control path. The returned acquire is the second successful K/V poll of that lane. -/
theorem initialValueAcquireBeforeSecondOutputCommit {commit : EvId} {spec : TcCommit.Spec}
    (hCommit : SecondOutputCommit X commit spec) :
    ∃ j, Mma.ReadyPoll l X commit.1 j 1 0 true .cta ∧
      TraceBefore X (commit.1, j) commit ∧
      (((X.tr commit.1).take j).filterMap readyEvent).length = 1 := by
  obtain ⟨g,j⟩ := commit
  exact initialValueAcquireBeforeTailEvent hp hX hCommit hCommit.decoded
    (show 2548 ≤ 2646 by decide) (Nat.le_refl _)

end PTX.Kernels.TmlFa4Fwd.Thread

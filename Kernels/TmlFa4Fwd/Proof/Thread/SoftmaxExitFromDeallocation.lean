-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalRetire
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierRelease
import all Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import all Kernels.TmlFa4Fwd.Proof.Thread.IdleParticipantExit
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry
import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Thread

private theorem roleFinalArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {mode : BarMode} (hw : warpIndex l g < 8)
    (he : FinalAllocationArrival X (g,j) mode) :
    X.get (g,j) = some ⟨7741,.bar 2 (some 416) .arrive⟩ := by
  obtain ⟨site,hSite,hGet⟩ := he.decoded
  have hLate : 173 < site ∧ site ∉ registerHintSites :=
    (by decide : ∀ k ∈ [2764,7741,9204], 173 < k ∧ k ∉ registerHintSites) site hSite
  have hPC := roleBodyPcOfEvent hp hX hGet hLate.1 hLate.2
  have hRole : roleBodyPc (warpIndex l g) site := hPC
  have hBand : site = 9205 ∨ 3103 ≤ site ∧ site ≤ 7742 := by
    simpa only [roleBodyPc,ite_eq_left hw,ite_eq_right (by omega : warpIndex l g ≠ 12),
      ite_eq_right (by omega : warpIndex l g ≠ 13),
      ite_eq_right (by omega : ¬ 14 ≤ warpIndex l g)] using hRole
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
  have hPc : site = 7741 := by omega
  subst site
  have hMode : mode = .arrive := (actualNamedBarrier hp hX hGet).2.2.1
  exact hMode ▸ hGet

/-- An actual final allocation arrival retains the live softmax register frame
in its original trace, even when that arrival is the last recorded event. -/
theorem finalArrivalCursorOfRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8) {mode : BarMode}
    (hArrival : FinalAllocationArrival X (g,j) mode) :
    ∃ t o, FinalAllocationArrival X (g,j) .arrive ∧
      At t 7742 (idleCarry l ⟨warpIndex l g,hw⟩) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  have he := roleFinalArrival hp hX hw hArrival
  obtain ⟨warp,hWarp,pos,s,ending,hIndex,hs,hOrigin,hRun⟩ :=
    softmaxRoleEntryRecorded hp hX he (by decide) (by decide) hw
  have hAt : ((X.tr g).drop pos)[j-pos]? = some ⟨7741,.bar 2 (some 416) .arrive⟩ := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  obtain ⟨_,hWalk⟩ := _root_.PTX.Kernels.TmlFa4Fwd.Mma.walkFromRun hRun
  obtain ⟨t,o,hPc,hFrame,hScratch,_,hStep,_,hPath⟩ :=
    softmaxAddressWalk hp hWalk hRun (by rw [hs.1]) (by rw [hs.1]; decide)
      (addressFrameAtRoleEntry hs) (scratchStateOfClear ⟨hs.2.1,hs.2.2.1⟩)
      (Q := fun _ => True) trivial (fun _ _ _ _ _ _ _ _ => trivial) hAt (by decide)
  change t.pc = 7741 at hPc
  have hTrace := hOrigin.append hPath
  rw [← List.take_add,Nat.add_sub_of_le hIndex] at hTrace
  have hF : t.fault = none := by
    cases hf : t.fault with
    | none => rfl
    | some f =>
      obtain ⟨tmpl,hOut,hFire⟩ := hStep
      simp only [out,hf,Out.ev.injEq] at hOut
      subst tmpl
      simp [Fires] at hFire
  have hc : kernel.code[t.pc]? = some ⟨none,.barArrive (.imm 2) (.imm 416) true⟩ := by
    rw [hPc]
    exact Flow.code_7741
  have hClear : ScoreScratchClear t := by
    simpa only [ScoreScratchState,hc,Op.isLocal,Bool.false_eq_true,ite_false,ScoreScratchReady]
      using hScratch
  have hWarpEq : warp = (⟨warpIndex l g,hw⟩ : Fin 8) := Fin.ext hWarp
  have hReady : At t 7741 (idleCarry l ⟨warpIndex l g,hw⟩) :=
    ⟨hPc,hClear.1,hClear.2,hF,hWarpEq ▸ ⟨hFrame.2.1,hFrame.2.2.1,trivial⟩⟩
  have hOut : out kernel Assumptions.all l g t = .ev (.bar 2 (next t) (some 416) .arrive) := by
    rw [out_event hF (by rw [hPc]; exact Flow.code_7741) rfl rfl]
    simp [eventTmpl,barTmpl,readBits,pure,Except.pure,hp.block,
      show (truncBits 32 2#64).toNat = 2 by decide,
      show (truncBits 32 416#64).toNat = 416 by decide]
  obtain ⟨before,hPrefix,hLocal⟩ := hTrace.returnedPrefix
  have hPre : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some (next t)) := by
    rw [List.take_add_one,show (X.tr g)[j]? = _ from he]
    exact hPrefix.snoc hLocal ⟨_,hOut,by rw [hPc],rfl⟩
  obtain ⟨endState,hWhole⟩ := hX.thr g hg
  rw [← List.take_append_drop (j+1) (X.tr g)] at hWhole
  exact ⟨next t,endState,FinalAllocationArrival.of_decoded (by decide) he,hReady.next,
    hPre,hPre.after_returned_prefix hWhole⟩

/-- Once the allocator actually attempts deallocation, every softmax lane of its CTA
records its exit in the same maximal trace. The deallocation already records the lane's arrival. -/
theorem exitOfObservedDeallocation {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    {d : EvId} (hCTA : g/l.block = d.1/l.block) (hDealloc : Deallocation X d) :
    Exited X g := by
  obtain ⟨j,mode,hArrival,_⟩ :=
    finalAllocationMemberBeforeDeallocation hp hMax.1 hg (by omega) hCTA hDealloc
  obtain ⟨t,o,he,hAt,hPrefix,hTail⟩ := finalArrivalCursorOfRecord hp hMax.1 hg hw hArrival
  exact idleSoftmaxExitFromArrival hp hMax hg hw hCTA hDealloc he hAt hPrefix hTail

end PTX.Kernels.TmlFa4Fwd.Softmax

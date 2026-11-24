-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxCounterEntry
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopOrdinal
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.CountTake
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread.Loader

private theorem biasedPublicationsBeforeExit {l : Launch} {g blocks cap past : Nat}
    {s : TState} {es : List Event} {vs : List Visit}
    (hBlocks : 0 < blocks) (hb : blocks < 2^31)
    (hCap : 0 < cap) (hc : cap < 2^31)
    (hs : At s 5006 (firstLoopGeometry blocks cap past))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : (⟨9205,.exit⟩ : Event) ∈ es) :
    firstBiasedRepeats blocks cap ≤ es.countP (barrierMark 5683) := by
  obtain ⟨u,_,hA,hWalk⟩ := firstCountEntryWalk hBlocks hb hCap hc hs hw he
  let split := firstPlainSplit blocks cap
  let biased := firstBiasedRepeats blocks cap
  change (if biased = 0 then At u 6654 (repeatCountLimits blocks split)
    else At u 5032 ((7248,b32 (2^32-(blocks-split))) :: repeatCountLimits blocks split)) at hA
  change biased ≤ _
  by_cases hz : biased = 0
  · simp [hz]
  rw [ite_eq_right hz] at hA
  have hMore : split+1 < blocks := by
    unfold biased firstBiasedRepeats at hz
    change blocks-1-split ≠ 0 at hz
    omega
  have hWord : u.regs 7248 = some (b32 (2^32-(blocks-split))) := hA.2.2.2.2.1
  have hSub : u.sub ≤ 3 := hA.2.1.symm ▸ Nat.zero_le _
  obtain ⟨_,pre,rest,_,hList,_,_,hCount,_,_,_,_,_,_⟩ :=
    loopPublicationCountBounds .biased hWalk hA.1 hSub hWord (by omega) he (by decide)
  have hMark : loopPublication .biased = barrierMark 5683 := by
    funext e
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun h => beq_iff_eq.mpr (loopPublicationPc .biased h),
      fun h => loopPublicationOfPc .biased (beq_iff_eq.mp h)⟩
  rw [hMark,initialBiasedDistance hb hMore] at hCount
  rw [hList,List.countP_append]
  unfold biased firstBiasedRepeats
  omega

private theorem markedWaitsOnBiasObject {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (stage : Fin 2) (hStage : warpIndex l g / 4 = stage.val) :
    ((X.tr g).take j).countP readSuccess ≤
      okPolls (biasReadyObject l (g/l.block) stage) ((X.tr g).take j) := by
  apply List.countP_mono_left
  intro e hMem hMark
  obtain ⟨i,hGet⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
  obtain ⟨site,kind⟩ := e
  cases kind <;> try cases hMark
  rename_i loc q ok acq scope
  cases ok
  · cases hMark
  have hSite : site ∈ [3498,5181] := by simpa [readSuccess] using hMark
  have hLoc := biasReadyWaitAddress hp hX hGet hSite
  rw [hLoc,hStage]
  simp [okPoll,sourceWaitSuccess,biasReadyObject]

/-- At exit an active softmax lane consumed one Bias-ready packet for every biased
visit, including the priming visit, using the protected tile geometry. -/
theorem biasAcquireExtentAtExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {g index : Nat} {stop : Event} (hWarp : warpIndex l g < 8)
    (hWork : g/l.block < tilePrefix p p.batch * p.heads)
    (he : X.get (g,index) = some stop) (hStop : stop.kind = .exit) :
    let stage := stageOf ⟨warpIndex l g,hWarp⟩
    ∃ batch, batch < p.batch ∧ tilePrefix p batch * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1) * p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let blocks := Mma.trips p batch tile
      let cap := blocks-stageGeometryBlocks p batch tile stage+10
      1 + firstBiasedRepeats blocks cap ≤
        okPolls (biasReadyObject l (g/l.block) stage) ((X.tr g).take index) := by
  obtain ⟨source,kind⟩ := stop
  change kind = .exit at hStop
  subst kind
  have hSrc := actualExitPc hX he
  subst source
  let lane := laneOf l g
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hg := event_thread_lt hX he
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨batch,hb,hLo,hHi,j,u,waits,first,rest,path,_,hList,hExit,hFirst,hA,hWalk,_⟩ :=
    activeCountersOfExit hp hX hg hWarp hl hWork hCuQ hUsedK (hLane.symm ▸ he)
  rw [hLane] at hList hWalk
  let stage := stageOf ⟨warpIndex l g,hWarp⟩
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  let cap := blocks-stageGeometryBlocks p batch tile stage+10
  have hT := (assignedCoordinates_valid hp hLo hHi).1
  have hBounds := firstGeometryBounds hp stage hb hT (lane := 0) (by decide)
  have hRep := biasedPublicationsBeforeExit hBounds.1 hBounds.2.1 hBounds.2.2.1
    hBounds.2.2.2.1 hA hWalk hExit
  change firstBiasedRepeats blocks cap ≤ rest.countP (barrierMark 5683) at hRep
  have whole (mark : Event → Bool) (hMark : mark ⟨9205,.exit⟩ = false) :
      ((X.tr g).take index).countP mark = (X.tr g).countP mark := by
    have hLen := Execution.exit_last hX hg he
    change index+1 = (X.tr g).length at hLen
    have hRead : (X.tr g)[index]? = some ⟨9205,.exit⟩ := he
    have hCount := countP_take_succ_false (p := mark) hRead hMark
    rwa [hLen,List.take_length,Eq.comm] at hCount
  have lower (mark : Event → Bool) :
      first.countP mark + rest.countP mark ≤ (X.tr g).countP mark := by
    have hSplit := congrArg (List.countP mark) (List.take_append_drop (j+3) (X.tr g))
    rw [List.countP_append,hList,List.countP_append,List.countP_append] at hSplit
    omega
  change first.countP (barrierMark 4397) = 1 at hFirst
  have h0 := lower (barrierMark 4397)
  have h1 := lower (barrierMark 5683)
  rw [← whole (barrierMark 4397) rfl] at h0
  rw [← whole (barrierMark 5683) rfl] at h1
  have hBudget := biasAcquiresCoverBiasedPublications hX he
  have hPoll := markedWaitsOnBiasObject hp hX (j := index) stage rfl
  refine ⟨batch,hb,hLo,hHi,?_⟩
  change 1 + firstBiasedRepeats blocks cap ≤
    okPolls (biasReadyObject l (g/l.block) stage) ((X.tr g).take index)
  exact (show 1 + firstBiasedRepeats blocks cap ≤ _ by omega).trans (hBudget.trans hPoll)

end PTX.Kernels.TmlFa4Fwd.Softmax

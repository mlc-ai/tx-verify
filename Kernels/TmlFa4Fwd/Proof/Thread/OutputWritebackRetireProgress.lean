-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputWritebackIssueProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputFree
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Lemmas.Step.BulkWaitReady
import Lemmas.Step.Object

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue AsyncCopy

noncomputable section

/-- A final writeback operation waits for a bulk read or releases its scratch stage. -/
def retireSite (stage : Fin 2) (release : Bool) : WritebackSite :=
  if release then .release stage else .readWait stage

private theorem retireRange (stage : Fin 2) (release : Bool) :
    let site := retireSite stage release
    WritebackPc (writebackPc (some site)) ∧
      (writebackSuccessor site true ≠ none → WritebackPc (writebackPc (some site)+1)) := by
  decide +revert

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch head tile shuffles votes : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hh : head < p.heads)
include hp hMax hg hb hh

/-- The physical bulk-read wait and release advance the actual output lane. -/
theorem WritebackReached.retireOfMaximal (ht : 256 * tile < p.qLength batch)
    (hStores : ∀ i a s, X.TensorStoreIssue i a s → X.AsyncPresent i .fullDone) (stage : Fin 2)
    (release : Bool) {F : List (Nat × Value)} (hF : ∀ item ∈ F, item.1 ∉ writebackWrites)
    {ending : Option TState}
    (cur : WritebackReached p l X g batch head tile F ending
      (some (retireSite stage release)) shuffles votes) :
    ∃ retired : WritebackReached p l X g batch head tile F ending
        (writebackSuccessor (retireSite stage release) true) shuffles votes,
      retired.pos = cur.pos+1 ∧
      X.get (g,cur.pos) = some ⟨writebackPc (some (retireSite stage release)),
        writebackKind p l g batch head tile (retireSite stage release) true⟩ := by
  let site := retireSite stage release
  let kind := writebackKind p l g batch head tile site true
  let mb := writebackFreeLoc l g stage
  let dest := if release then next (mbarStateDest cur.state (some (7870+stage.val)))
    else next cur.state
  let ev : Event := ⟨cur.state.pc,kind⟩
  have hPc := cur.checkpoint.1
  have hRange := retireRange stage release
  have hModel : ∀ {s : TState}, WritebackPc s.pc →
      out kernel Assumptions.all l g s = out kernel [] l g s :=
    fun h => epilogue_out_all_eq_nil (.inl ⟨by omega,by omega⟩)
  have hOut := (hModel (hPc.symm ▸ hRange.1)).trans
    (writebackOut hp g site cur.state hb hh ht cur.checkpoint)
  have hNext : Next kernel Assumptions.all l g cur.before cur.state
      (writebackTemplate p l g batch head tile site cur.state) := ⟨cur.localSteps,hOut⟩
  have hFire : ∀ (e : Event) (result : Option TState),
      Fires cur.state.pc (writebackTemplate p l g batch head tile site cur.state) e result ↔
        e = ev ∧ result = some dest := by
    intro e result
    cases e
    cases release <;> rfl
  have hFired := (hFire _ _).mpr ⟨rfl,rfl⟩
  have hEStep : EStep kernel Assumptions.all l g cur.state ev (some dest) := ⟨_,hOut,hFired⟩
  have hMore : cur.pos < (X.tr g).length := by
    by_contra! hNo
    have hEq := Nat.le_antisymm cur.bounded hNo
    have hNonempty : X.tr g ≠ [] := fun h => by
      have hPos := Nat.lt_of_lt_of_le cur.positive cur.bounded
      simp [h] at hPos
    have hPrefix := cur.recorded
    rw [List.take_of_length_le hNo] at hPrefix
    apply hMax.not_grows
    cases release
    · exact Step.BulkWait.bulk_wait_counted_extension hMax.1 hg hNonempty (cur.released hEq)
        (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
          (Execution.noNewRead_snoc rfl)) hPrefix cur.localSteps hEStep
    · refine Step.object_counted_extension_silent (e := ev) hMax.1 (by trivial) hg (.inl hNonempty)
        (cur.released hEq) hPrefix cur.localSteps hEStep ⟨trivial,fun _ h => by cases h⟩ trivial
        (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) rfl (mb := mb) (act := .arrive 1 0)
        (fun _ _ h => by cases h) ?_ ?_
      · intro loc
        by_cases h : loc = mb
        · subst loc
          simp [objectAction,snoc_get_new,ev,kind,site,retireSite,writebackKind,mb]
        · have hn : loc ≠ writebackFreeLoc l g stage := h
          simp [objectAction,snoc_get_new,ev,kind,site,retireSite,writebackKind,h,Ne.symm hn]
      · intro rec
        exact Assumptions.wfStep.quiet hMax.1
          (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  have hRun := cur.continuation
  have hSplit := List.drop_eq_getElem_cons hMore
  rw [hSplit] at hRun
  obtain ⟨v,hActual,hSuffix⟩ := hNext.continuing_event
    (fun h => by have := ((hFire _ _).mp h).2; cases this) hRun
  obtain ⟨hHead,hRet⟩ := (hFire _ _).mp hActual
  obtain rfl := Option.some.inj hRet
  have he : X.get (g,cur.pos) = some ev := by
    change (X.tr g)[cur.pos]? = _
    rw [List.getElem?_eq_getElem hMore,hHead]
  have hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take (cur.pos+1)) (some dest) := by
    rw [List.take_succ_eq_append_getElem hMore,hHead]
    exact cur.recorded.snoc cur.localSteps hEStep
  obtain ⟨_,w,steps,hStep,hAt,hFrame,hSame⟩ := writebackStep hp g site hb ht cur.checkpoint hFired
  have hTrue : writebackSucceeded kind = true := by cases release <;> rfl
  rw [hTrue] at hAt hSame
  have hSaved : Holds w.regs F := by
    apply holdsSchedulerFrame (regs := F.map Prod.fst) cur.saved
    · intro r hr
      obtain ⟨item,hm,rfl⟩ := List.mem_map.mp hr
      exact hFrame item.1 (hF item hm)
    · intro item hm
      exact List.mem_map_of_mem hm
  have hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) dest w := by
    by_cases hStop : writebackSuccessor site true = none
    · rw [hSame hStop]
    · have hDest : WritebackPc dest.pc := by
        have hNextPc : dest.pc = cur.state.pc+1 := by cases release <;> rfl
        rw [hNextPc,hPc]
        exact hRange.2 hStop
      exact writebackLiftLocal hModel hDest (run_rtg hStep)
  have hTake := List.take_succ_eq_append_getElem hMore
  rw [hHead] at hTake
  have hSh : ((X.tr g).take (cur.pos+1)).countP Execution.isShfl = shuffles := by
    rw [hTake,List.countP_append,cur.shuffleCount]
    cases release <;> rfl
  have hVote : ((X.tr g).take (cur.pos+1)).countP isFullWarpVote = votes := by
    rw [hTake,List.countP_append,cur.voteCount]
    cases release <;> rfl
  refine ⟨⟨cur.pos+1,dest,w,Nat.succ_pos _,len_of_get he,?_,hPrefix,hSuffix,hLocal,hAt,hSaved,
    hSh,hVote⟩,rfl,?_⟩
  · cases release
    · intro hEnd
      constructor
      intro _ _ _ _
      rw [← hEnd,Nat.add_sub_cancel]
      apply Step.BulkWait.ready_of_drained hMax.1 he
      · exact hStores
      · intro i s hs hBulk
        have hCompletion := (actualCopyShape hMax.1 hs).completion
        rw [hCompletion] at hBulk
        cases hBulk
    · exact releasedIfLast he (by intro h; cases h)
  · change X.get (g,cur.pos) = some ⟨writebackPc (some site),kind⟩
    simpa only [ev,hPc] using he

/-- Consume the stage's actual successful acquire and retain the recorded cursor. -/
theorem WritebackReached.readyOfPublications (ht : 256 * tile < p.qLength batch) (stage : Fin 2)
    (hPublished : ∀ lane < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) lane,j) stage)
    {F : List (Nat × Value)} (hF : ∀ item ∈ F, item.1 ∉ writebackWrites) {ending : Option TState}
    (cur : WritebackReached p l X g batch head tile F ending (some (.ready stage)) shuffles votes) :
    Nonempty (WritebackReached p l X g batch head tile F ending
      (some (.store stage 0)) shuffles votes) := by
  obtain ⟨j,hj,v,w,he,hAt,hFrame,hPrefix,hRest,hSteps,hTrace⟩ :=
    outputReadyPollOfMaximal hp hMax hg hb hh ht stage hPublished hF cur.positive cur.bounded
      cur.released cur.checkpoint cur.saved cur.recorded cur.continuation cur.localSteps
  have hFront : j+1 = cur.pos + ((j-cur.pos)+1) := by omega
  have hDrop : ((X.tr g).drop cur.pos).take ((j-cur.pos)+1) =
      List.replicate (j-cur.pos) ⟨pollPc stage,.wait (readyLoc l g stage) 0 false true .cta⟩ ++
      [⟨pollPc stage,.wait (readyLoc l g stage) 0 true true .cta⟩] := by
    rw [hTrace,List.take_append]
    simp
  have hTake : (X.tr g).take (j+1) = (X.tr g).take cur.pos ++
      List.replicate (j-cur.pos) ⟨pollPc stage,.wait (readyLoc l g stage) 0 false true .cta⟩ ++
      [⟨pollPc stage,.wait (readyLoc l g stage) 0 true true .cta⟩] := by
    rw [hFront,List.take_add,hDrop,List.append_assoc]
  have hSh : ((X.tr g).take (j+1)).countP Execution.isShfl = shuffles := by
    rw [hTake]
    simp [List.countP_append,List.countP_replicate,Execution.isShfl,cur.shuffleCount]
  have hVote : ((X.tr g).take (j+1)).countP isFullWarpVote = votes := by
    rw [hTake]
    rw [List.countP_append,List.countP_append,cur.voteCount]
    simp [List.countP_replicate,isFullWarpVote,isWarpVote,voteClass]
  exact ⟨⟨j+1,v,w,Nat.succ_pos _,len_of_get he,releasedIfLast he (by intro h; cases h),
    hPrefix,hRest,hSteps,hAt,hFrame,hSh,hVote⟩⟩

/-- Completed correction cohorts and the observed bulk reads take the lane through writeback. -/
theorem WritebackReached.finishWithCreditsOfPublications (ht : 256 * tile < p.qLength batch)
    (hPublished : ∀ stage : Fin 2, ∀ lane < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) lane,j) stage)
    (hStores : ∀ i a s, X.TensorStoreIssue i a s → X.AsyncPresent i .fullDone)
    {F : List (Nat × Value)} (hF : ∀ item ∈ F, item.1 ∉ writebackWrites) {ending : Option TState}
    (cur : WritebackReached p l X g batch head tile F ending (some (.ready 0)) shuffles votes) :
    Nonempty (WritebackReached p l X g batch head tile F ending none shuffles votes) ∧
      ∀ stage : Fin 2, ∃ j, Thread.Output.FreeCredit l X (g/l.block) stage (g,j) := by
  obtain ⟨store₀⟩ := cur.readyOfPublications hp hMax hg hb hh ht 0 (hPublished 0) hF
  obtain ⟨ready₁,_,_,_⟩ := store₀.stageIssueOfMaximal hp hMax hg hb hh ht 0 hF
  obtain ⟨store₁⟩ := ready₁.readyOfPublications hp hMax hg hb hh ht 1 (hPublished 1) hF
  obtain ⟨wait₀,_,_,_⟩ := store₁.stageIssueOfMaximal hp hMax hg hb hh ht 1 hF
  obtain ⟨release₀,_,_⟩ := wait₀.retireOfMaximal hp hMax hg hb hh ht hStores 0 false hF
  obtain ⟨wait₁,_,hFirst⟩ := release₀.retireOfMaximal hp hMax hg hb hh ht hStores 0 true hF
  obtain ⟨release₁,_,_⟩ := wait₁.retireOfMaximal hp hMax hg hb hh ht hStores 1 false hF
  obtain ⟨finished,_,hSecond⟩ := release₁.retireOfMaximal hp hMax hg hb hh ht hStores 1 true hF
  refine ⟨⟨finished⟩,fun stage => ?_⟩
  fin_cases stage
  · exact ⟨release₀.pos,_,hFirst,rfl,rfl⟩
  · exact ⟨release₁.pos,_,hSecond,rfl,rfl⟩
end

/-- The scheduler words carried through output writeback into its final request scan. -/
def outputDrainFrame (p : Params) (l : Launch) (g lane : Nat) : List (Nat × Value) :=
  [(307,.pred (decide (p.batch < lane))), (1201,b32 lane), (7506,b64 p.cuQBase),
    (268,.pred (!decide (laneHasRequest lane p.batch))), (7147,b32 p.batch), (7138,b32 p.heads)] ++
    schedulerStartupFrame p l (warpLane l g lane)

/-- Every lane has completed writeback and reached the output drain. -/
def OutputWritebackDrained (p : Params) (l : Launch) (X : Execution) (g : Nat) : Prop :=
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      ∃ (shuffles : Nat) (ends : Nat → Option TState), ∀ lane < 32,
      let co := assignedCoordinates p batch (g / l.block)
      Nonempty (WritebackReached p l X (warpLane l g lane) batch co.2 co.1
        (outputDrainFrame p l g lane) (ends lane) none shuffles 1)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hCuQ : DrainCuQProtected p X)
    (hActive : g / l.block < tilePrefix p p.batch * p.heads)
    (hPublished : ∀ stage : Fin 2, ∀ row < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) row,j) stage)
    (hStores : ∀ i a s, X.TensorStoreIssue i a s → X.AsyncPresent i .fullDone)
include hp hMax hg hw hCuQ hActive hPublished hStores

/-- All lanes of an active output warp reach its final scan once the correction cohorts
publish and the issued output stores have returned their source reads. -/
theorem outputWritebackDrainedWithCreditsOfMaximal :
    OutputWritebackDrained p l X g ∧
      ∀ stage : Fin 2, ∀ lane : Fin 32, ∃ j,
        Thread.Output.FreeCredit l X (g/l.block) stage
          (Thread.Output.outputLane l (g/l.block) lane,j) := by
  obtain ⟨batch,hb,hLo,hHi,shuffles,ends,⟨ready⟩⟩ :=
    selectedOutputReadyOfMaximal hp hMax hg hw hCuQ hActive
  let co := assignedCoordinates p batch (g / l.block)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨ht,hh⟩ := assignedCoordinates_valid hp hLo hHi
  have hResult (lane : Nat) (hl : lane < 32) :
      Nonempty (WritebackReached p l X (warpLane l g lane) batch co.2 co.1
        (outputDrainFrame p l g lane) (ends lane) none shuffles 1) ∧
      ∀ stage : Fin 2, ∃ j,
        Thread.Output.FreeCredit l X ((warpLane l g lane)/l.block) stage (warpLane l g lane,j) := by
    let thread := warpLane l g lane
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hPub : ∀ stage : Fin 2, ∀ row < 128, ∃ j,
        Thread.CorrectionReady X (Thread.Output.sourceLane l (thread,0) row,j) stage := by
      have hCta : thread / l.block = g / l.block := hSame.1.2.2.symm
      dsimp only [Thread.Output.sourceLane,Prod.fst] at hPublished ⊢
      rwa [hCta]
    have hFrame (item : Nat × Value) (hm : item ∈ outputDrainFrame p l g lane) :
        item.1 ∉ writebackWrites := by
      simp only [outputDrainFrame,schedulerStartupFrame,List.cons_append,List.nil_append,
        List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> exact of_decide_eq_true rfl
    let initial : WritebackReached p l X thread batch co.2 co.1 (outputDrainFrame p l g lane)
        (ends lane) (some (.ready 0)) shuffles 1 :=
      ⟨ready.pos lane,ready.before lane,ready.state lane,ready.positive lane hl,
        ready.bounded lane hl,
        ready.released lane hl,ready.recorded lane hl,ready.continuation lane hl,
        ready.localSteps lane hl,
        outputReady_writebackAt (ready.checkpoint lane hl),
        ((holds_append ..).mp (ready.checkpoint lane hl).2.2.2.2).2,
        ready.ordinals.shfl lane hl,ready.ordinals.vote lane hl⟩
    exact initial.finishWithCreditsOfPublications hp hMax hSame.1.2.1 hb hh ht hPub hStores hFrame
  refine ⟨⟨batch,hb,hLo,hHi,shuffles,ends,fun lane hl => (hResult lane hl).1⟩,fun stage lane => ?_⟩
  have hSame := (Step.sameWarp_lane hBlock hg lane.isLt).1
  obtain ⟨j,hCredit⟩ := (hResult lane lane.isLt).2 stage
  have hCta : (warpLane l g lane)/l.block = g/l.block := hSame.1.2.2.symm
  have hLane : warpLane l g lane = Thread.Output.outputLane l (g/l.block) lane := by
    have hWarp : g%l.block/32 = 13 := hw
    have hParts := Nat.div_add_mod g l.block
    have hLaneBase : laneOf l g + 416 = g%l.block := by
      change (g%l.block)%32+416 = _
      omega
    change g-laneOf l g+lane.val = (g/l.block)*l.block+416+lane.val
    rw [hp.block] at hParts hLaneBase ⊢
    omega
  rw [hCta,hLane] at hCredit
  exact ⟨j,hCredit⟩

/-- All lanes of an active output warp reach its final scan. -/
theorem outputWritebackDrainedOfMaximal :
    OutputWritebackDrained p l X g :=
  (outputWritebackDrainedWithCreditsOfMaximal hp hMax hg hw hCuQ hActive hPublished hStores).1

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

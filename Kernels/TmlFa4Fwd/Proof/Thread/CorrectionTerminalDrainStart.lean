-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseTailProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainRecordedKeep
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionScanProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Lemmas.Step.ProtectedReadProgress
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- The first endpoint lookup of the terminal scheduler reads the lane's own
protected CuQ word. The out-of-range branch leaves the initialized zero. -/
theorem terminalDrainFirstWordOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads)
    (c : OpeningTripCursor l X g RowDrainRole.correction.start
      (RowDrainRole.correction.frame p l g)) :
    ∃ d : OpeningTripCursor l X g 9090
        ((7279,b32 (drainCuQ p (laneOf l g)))::RowDrainRole.correction.roots p l g),
      ((X.tr g).take d.pos).countP Execution.isShfl =
        ((X.tr g).take c.pos).countP Execution.isShfl ∧
      ((X.tr g).take d.pos).countP isFullWarpVote =
        ((X.tr g).take c.pos).countP isFullWarpVote := by
  let role := RowDrainRole.correction
  let F := role.guarded p l g
  obtain ⟨s,hParameters,hS⟩ := role.batchParameter hp (g := g) c.checkpoint
  obtain ⟨t,hCompare,hT⟩ := role.initialCompare hp (g := g) hS
  let a := next (setReg t 7279 (b32 0))
  have hFirst : run kernel [] l g 1 t = some a := by
    apply run_local Flow.code_9085 rfl hT
    rw [execLocalA_nil,execLocal_move rfl]
    rfl
  have hMove := role.drainLocals (n := 1) (by decide) (by decide) hT.1 (by simp) hFirst
  have hAt : At a 9086 ((7279,b32 0)::F) := hT.set (by
    simp [role,RowDrainRole.guarded,RowDrainRole.guardReg,RowDrainRole.roots,
      RowDrainRole.batchReg,RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg])
  let flag := decide (p.batch < laneOf l g)
  have hFlag : a.regs 744 = some (.pred flag) := hAt.2.2.2.2.2.1
  obtain ⟨u,hBranch,hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_9086 flag hAt hFlag (by simp)
  have hTau := role.drainLocals (n := 1) (by decide) (by decide) hAt.1 (by simp) hBranch
  have hPath := ((c.localSteps.trans hParameters).trans hCompare).trans (hMove.trans hTau)
  by_cases hLane : laneOf l g ≤ p.batch
  · have hFalse : flag = false := decide_eq_false (by omega)
    have hu' : At u 9087 (role.roots p l g) := by
      rw [hFalse] at hu
      exact hu.mono hu.2.2.2.2.2.2
    obtain ⟨v,hV,hRead⟩ := role.firstTemplate hp hLane hu'
    let access : Acc := {loc := globalLoc (p.cuQBase+4*laneOf l g),size := 4}
    let value := b32 (p.qOffset (laneOf l g))
    let bytes := value.toBytes.map some
    have hValue : HasValue m access.loc value := by
      simpa [access,value,b32,HasValue,Value.bytes] using hp.cuQ (laneOf l g) hLane
    have hn : Next kernel Assumptions.all l g c.before v (.read access (afterLoad v [7279])) :=
      ⟨hPath.trans hRead.steps,hRead.stop⟩
    obtain ⟨he,hPre,hTail⟩ := Step.protected_read_of_maximal hMax hg
      (a := access) (value := value) rfl hValue (hCuQ _ hLane) hn c.recorded c.remaining c.positive
      c.bounded c.released (Assumptions.wf_snoc_initial hMax.1)
    have hRebuild := PTX.Proof.rebuild_scalar (v := value) (by decide : 0 < 4) rfl
    have hState : afterLoad v [7279] bytes = next (setReg v 7279 value) := by
      rw [afterLoad_ok hV.2.1 hV.2.2.1 hRebuild]
      simp [next,setReg,hV.2.1,hV.2.2.1]
    rw [hState] at hPre hTail
    have hFrame : At (next (setReg v 7279 value)) 9090 ((7279,value)::role.roots p l g) :=
      (hV.mono hV.2.2.2.2.2).set (by simp [role,RowDrainRole.roots,RowDrainRole.batchReg,
        RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg])
    exact ⟨⟨c.pos+1,_,_,c.ending,Nat.succ_pos _,len_of_get he,
      releasedIfLast he (by simp [Kind.resume]),by simpa only [drainCuQ,ite_eq_left hLane,value]
        using hFrame,hPre,hTail,.refl⟩,Flow.countP_take_succ_false he rfl,
          Flow.countP_take_succ_false he rfl⟩
  · have hTrue : flag = true := decide_eq_true (by omega)
    rw [hTrue] at hu
    have hFrame : At u 9090 ((7279,b32 (drainCuQ p (laneOf l g)))::role.roots p l g) := by
      simp only [drainCuQ,ite_eq_right hLane]
      exact hu.mono ⟨hu.2.2.2.2.1,hu.2.2.2.2.2.2⟩
    exact ⟨⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hFrame,
      c.recorded,c.remaining,hPath⟩,rfl,rfl⟩

private def withFrame {l : Launch} {X : Execution} {g pc : Nat}
    {F G : List (Nat × Value)} (c : OpeningTripCursor l X g pc F)
    (h : Holds c.ready.regs G) : OpeningTripCursor l X g pc G :=
  ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,
    c.checkpoint.mono h,c.recorded,c.remaining,c.localSteps⟩

private def laneCursor {l : Launch} {X : Execution} {g pc shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (c : SchedulerWarpReached l X g pc F shuffles votes ends) {lane : Nat} (hl : lane < 32) :
    OpeningTripCursor l X (warpLane l g lane) pc (F lane) :=
  ⟨c.pos lane,c.before lane,c.state lane,ends lane,c.positive lane hl,c.bounded lane hl,
    c.released lane hl,c.checkpoint lane hl,c.recorded lane hl,c.continuation lane hl,
    c.localSteps lane hl⟩

private theorem beforeCorrectionDrain {pc : Nat} (hm : pc ∈ Assumptions.swExp2Sites) :
    pc < 9083 := by
  simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
include hp hMax hCuQ

private theorem LseTailReached.drainRootsOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (c : LseTailReached p l X g batch) :
    Holds c.cursor.ready.regs (RowDrainRole.correction.frame p l g) := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨_,⟨entry⟩⟩ := firstGroupRouteOfMaximal hp hMax hg hw.1 hw.2 hCuQ
  have hPc := entry.checkpoint lane hl
  have hRoot := hPc.2.2.2.2
  let F := RowDrainRole.correction.frame p l g
  have hRegs : Holds (entry.state lane).regs F := by
    dsimp only [F,RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg]
    refine ⟨?_,?_,?_,trivial⟩
    · exact holds_mem hRoot (by
        simp [correctionFirstRouteFacts,firstCorrectionScanFacts,firstShuffleFacts,hSelf])
    · exact holds_mem hRoot (by
        simp [correctionFirstRouteFacts,firstCorrectionScanFacts,firstShuffleFacts,
          afterCreditFacts,creditFacts,entryFacts,nonzeroBarrierFacts,abiFacts])
    · have hc := holds_mem hRoot
        (show (1618,b32 (g/l.block)) ∈ correctionFirstRouteFacts p l g lane by
          simp [correctionFirstRouteFacts])
      simpa only [hSelf] using hc
  let pc := if g/l.block < tilePrefix p (min p.batch 31)*p.heads then 7864 else 7807
  have init : Nonempty (OpeningTripCursor l X g pc F) := by
    have d : OpeningTripCursor l X (warpLane l g lane) pc F :=
      withFrame (laneCursor entry hl) hRegs
    exact ⟨hSelf ▸ d⟩
  obtain ⟨d⟩ := init
  let span : RowDrainSpan := ⟨7807,9084,9084⟩
  refine span.recordedKeep hp (by dsimp [span,pc]; split_ifs <;> decide)
    (by dsimp [pc]; split_ifs <;> decide) (by decide) rfl
    (fun _ hm => beforeCorrectionDrain hm)
    (fun _ hm => (beforeCorrectionDrain hm).trans (by decide))
    ?_ ?_ ?_ ?_ d c.cursor
  · set_option maxRecDepth 100000 in kernel_rfl
  · apply span.segmentKeeps_of_audit
    set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

/-- The guarded LSE tail enters the terminal scheduler on the actual lane trace.
The initial scheduler's lane index, launch pointer and CTA index survive the work. -/
theorem LseTailReached.drainFirstWordOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (c : LseTailReached p l X g batch) :
    ∃ d : OpeningTripCursor l X g 9090
        ((7279,b32 (drainCuQ p (laneOf l g)))::RowDrainRole.correction.roots p l g),
      ((X.tr g).take d.pos).countP Execution.isShfl =
        ((X.tr g).take c.cursor.pos).countP Execution.isShfl ∧
      ((X.tr g).take d.pos).countP isFullWarpVote =
        ((X.tr g).take c.cursor.pos).countP isFullWarpVote :=
  terminalDrainFirstWordOfMaximal hp hMax hCuQ hg
    (withFrame c.cursor (c.drainRootsOfMaximal hp hMax hCuQ hg hw))

/-- The initial group's real scan predicate is unchanged by correction work
and by the first drain lookup. -/
theorem terminalDrainKeepsFirstGuard {g : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) {F : List (Nat × Value)}
    (d : OpeningTripCursor l X g 9090 F) :
    Holds d.ready.regs [(685,.pred (!decide (laneHasRequest (laneOf l g) p.batch)))] := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  let G : List (Nat × Value) := [(685,.pred (!decide (laneHasRequest lane p.batch)))]
  obtain ⟨_,⟨down⟩⟩ := firstGroupDownOfMaximal hp hMax hg hw.1 hw.2 hCuQ
  have ht := down.checkpoint lane hl
  have hLane : laneOf l (warpLane l g lane) = lane := congrArg (laneOf l) hSelf
  obtain ⟨_,u,hLocal,hAt⟩ := correctionFirstTilesWithGuard hp
    (g := warpLane l g lane) (by rw [hLane]; exact ht)
  let a := laneCursor down hl
  have hReady : At u 7781 G := hAt.mono ⟨by simpa only [hLane] using hAt.2.2.2.2.1,trivial⟩
  have seed : OpeningTripCursor l X (warpLane l g lane) 7781 G :=
    ⟨a.pos,a.before,u,a.ending,a.positive,a.bounded,a.released,hReady,
      a.recorded,a.remaining,a.localSteps.trans (run_rtg hLocal)⟩
  let span : RowDrainSpan := ⟨7781,9091,9091⟩
  refine span.recordedKeep hp (by decide) (by decide) (by decide) rfl
    (fun _ hm => (beforeCorrectionDrain hm).trans (by decide))
    (fun _ hm => (beforeCorrectionDrain hm).trans (by decide))
    ?_ ?_ ?_ ?_ (hSelf ▸ seed) d
  · set_option maxRecDepth 100000 in kernel_rfl
  · apply span.segmentKeeps_of_audit
    set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl
  · set_option maxRecDepth 100000 in kernel_rfl

end PTX.Kernels.TmlFa4Fwd.Correction

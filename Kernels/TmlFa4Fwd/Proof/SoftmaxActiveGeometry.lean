-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxGroupCoordinates
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstGeometryReads
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Step.ExitLast
import Kernels.TmlFa4Fwd.Flow.Code.Part051
import Kernels.TmlFa4Fwd.Flow.Code.Part052

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

noncomputable section

private theorem activeSetup (p : Params) (l : Launch) (g batch tile : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 4 3284
      [(1062,b32 warp.val), (783,.pred true), (7247,b32 batch), (7246,b32 tile),
        (7502,b64 p.cuQBase), (7503,b64 p.usedKBase)]
      3288 [(7247,b32 batch), (7502,b64 p.cuQBase), (7503,b64 p.usedKBase),
        (7246,b32 tile), (2772,b32 (stageOf warp).val)] := by
  fin_cases warp <;> intro t ht <;>
    simp only [stageOf, Nat.reduceDiv] at ht ⊢ <;>
    seg_fp ht using norm_bits

private def setupLo (after : Bool) : Nat := if after then 3288 else 3274
private def setupHi (after : Bool) : Nat := if after then 3367 else 3284

private def setupRegs (after : Bool) : List Nat :=
  if after then [7247,7502,7503,7246,2772] else [1062,783,7247,7246,7502,7503]

private def geometrySetupCode (after : Bool) (ins : Instr) : Bool :=
  ins.op.isLocal && Assumptions.coreOp ins.op && schedulerFallsThrough ins.op &&
    (setupRegs after).all (fun r => !(writesRegs ins.op).contains r)

set_option maxRecDepth 100000 in
private theorem geometrySetupSlice (after : Bool) :
    ((kernel.code.drop (setupLo after)).take (setupHi after-setupLo after)).all
      (geometrySetupCode after) = true := by cases after <;> kernel_rfl

private theorem geometrySetupAt (after : Bool) {pc : Nat} {ins : Instr}
    (hLo : setupLo after ≤ pc) (hHi : pc < setupHi after) (hc : kernel.code[pc]? = some ins) :
    geometrySetupCode after ins = true := by
  apply List.all_eq_true.mp (geometrySetupSlice after) ins
  apply List.mem_of_getElem? (i := pc-setupLo after)
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]

private theorem geometrySetupOut (after : Bool) {l : Launch} {g : Nat} {s : TState}
    (hLo : setupLo after ≤ s.pc) (hHi : s.pc < setupHi after) :
    out kernel Assumptions.all l g s = out kernel [] l g s := by
  cases hc : kernel.code[s.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have ha := geometrySetupAt after hLo hHi hc
    simp only [geometrySetupCode, Bool.and_eq_true] at ha
    apply Assumptions.out_all_eq_nil _ _ _ hc ha.1.1.2
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      cases after <;> simp only [setupLo, setupHi, Bool.false_eq_true, ite_false, ite_true]
        at hLo hHi <;> omega

private theorem geometrySetupWalk (after : Bool) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    {i : Nat} {target : Event} (hevent : es[i]? = some target)
    (hTarget : setupHi after ≤ target.pc)
    (hLo : setupLo after ≤ s.pc) (hHi : s.pc ≤ setupHi after) (hSub : s.sub = 0) (hAcc : s.acc = [])
    (hf : s.fault = none) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      u.pc = setupHi after ∧ u.sub = 0 ∧ u.acc = [] ∧ u.fault = none ∧
      ∀ r ∈ setupRegs after, u.regs r = s.regs r := by
  induction hw with
  | stop => simp at hevent
  | @tau s t es vs hTau hw ih =>
    rcases hHi.eq_or_lt with h | h
    · exact ⟨s,.refl,h,hSub,hAcc,hf,fun _ _ => rfl⟩
    have ht : Tau kernel [] l g s t := by
      unfold Tau at hTau ⊢
      rwa [← geometrySetupOut after hLo h]
    obtain ⟨ins,hc⟩ := tau_core_has_code ht
    have hc' := geometrySetupAt after hLo h hc
    simp only [geometrySetupCode, Bool.and_eq_true] at hc'
    have hLocal : t.pc = s.pc + 1 ∧ t.sub = 0 ∧ t.acc = [] ∧ t.fault = none := by
      rcases tau_core_frame hc ht with rfl | hT
      · exact ⟨rfl,rfl,rfl,hf⟩
      · have hp := hT.pc
        have hNext : t.pc = s.pc+1 := by
          cases ho : ins.op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]
        exact ⟨hNext,hT.sub.trans hSub,hT.acc.trans hAcc,hT.fault.trans hf⟩
    obtain ⟨u,hu,hPc,hs,ha,hF,hRegs⟩ := ih hevent (by omega) (by omega)
      hLocal.2.1 hLocal.2.2.1 hLocal.2.2.2
    refine ⟨u,.head hTau hu,hPc,hs,ha,hF,fun r hr => (hRegs r hr).trans ?_⟩
    apply tau_core_regs hc ht
    have hReg := List.all_eq_true.mp hc'.2 r hr
    simpa using hReg
  | @ev s t e es vs he hw ih =>
    rcases hHi.eq_or_lt with h | h
    · exact ⟨s,.refl,h,hSub,hAcc,hf,fun _ _ => rfl⟩
    obtain ⟨ins,hc,hl,_⟩ := estep_event_source he
    have hCode := geometrySetupAt after hLo h hc
    simp only [geometrySetupCode, Bool.and_eq_true] at hCode
    rw [hCode.1.1.1] at hl
    cases hl
  | @last s e he =>
    have hPc := estep_source_pc he
    have hEq : target = e := by cases i <;> simp_all
    subst e
    exact ⟨s,.refl,by omega,hSub,hAcc,hf,fun _ _ => rfl⟩

private theorem setupContinuation (after : Bool) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {result : Option TState} {i : Nat} {target : Event}
    {F : List (Nat × Value)} (hr : Run kernel Assumptions.all l g s es result)
    (hs : At s (setupLo after) F) (he : es[i]? = some target)
    (hTarget : setupHi after ≤ target.pc) (hKeep : ∀ x ∈ F, x.1 ∈ setupRegs after) :
    ∃ u, At u (setupHi after) F ∧ Run kernel Assumptions.all l g u es result := by
  obtain ⟨_,hw⟩ := Mma.walkFromRun hr
  obtain ⟨u,hu,hPc,hSub,hAcc,hf,hF⟩ := geometrySetupWalk after hw he hTarget
    hs.1.ge (hs.1.le.trans (by cases after <;> decide)) (hs.2.1) (hs.2.2.1) (hs.2.2.2.1)
  exact ⟨u,⟨hPc,hSub,hAcc,hf,holdsSchedulerFrame hs.2.2.2.2 hF hKeep⟩,
    hr.after_local_nonempty hu (by intro hz; simp [hz] at he)⟩

/-- The selected softmax tile follows the active branch and supplies the geometry read operands. -/
theorem activeGeometryInputs {p : Params} {l : Launch} {g thread batch : Nat} {warp : Fin 8}
    {es : List Event} {s : TState} {result : Option TState} {i : Nat} {target : Event}
    (hs : At s 3274 (firstActiveTileFacts p l g warp batch))
    (hr : Run kernel Assumptions.all l thread s es result)
    (he : es[i]? = some target) (hTarget : 3367 ≤ target.pc) :
    ∃ u, At u 3367 (geometryAddressInputs p batch
      (assignedCoordinates p batch (g/l.block)).1 (stageOf warp)) ∧
      Run kernel Assumptions.all l thread u es result := by
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let F := [(1062,b32 warp.val), (783,.pred true), (7247,b32 batch), (7246,b32 tile),
    (7502,b64 p.cuQBase), (7503,b64 p.usedKBase)]
  have hF : At s (setupLo false) F := hs.mono (by
    refine ⟨?_,?_,?_,?_,?_,?_,trivial⟩ <;>
      exact holds_mem hs.2.2.2.2 (by simp [firstActiveTileFacts, dispatchInput, tile]))
  have hRegs : ∀ x ∈ F, x.1 ∈ setupRegs false := by
    intro x hx
    simp only [F, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
  obtain ⟨v,hV,hv⟩ := setupContinuation false hr hF he (by change 3284 ≤ _; omega) hRegs
  obtain ⟨w,hw,hW⟩ := (activeSetup p l thread batch tile warp).apply hV
  refine setupContinuation true (hv.after_local_nonempty (run_rtg hw) ?_) hW he hTarget ?_
  · intro hz
    simp [hz] at he
  · intro x hx
    simp only [geometryAddressInputs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src index : Nat} {target : Event}
    (hg : g < l.threads) (hWarp : warpIndex l g < 8) (hSrc : src < 32)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4*i)).at k))
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    (he : X.get (warpLane l g src,index) = some target)
include hp hX hg hWarp hSrc hWork hCuQ hUsedK he

/-- A late active lane reads the request selected for its CTA and computes the
same full-tile block limit used by the MMA role. -/
theorem activeGeometryOfEventPastReads (hLate : 3374 ≤ target.pc) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    ∃ batch, batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      ∃ j u result, FirstGeometryReads p X (warpLane l g src) j batch ∧
        At u 3418 (firstGeometryFacts p batch tile (stageOf warp)) ∧
        Run kernel Assumptions.all l (warpLane l g src) u
          ((X.tr (warpLane l g src)).drop (j+3)) result ∧
        j+3 ≤ index ∧ target ∈ (X.tr (warpLane l g src)).drop (j+3) := by
  dsimp only
  obtain ⟨batch,_,hb,hLo,hHi,ends,cur,hFollow⟩ :=
    activeTileOfEvent hp hX hg hWarp hSrc hWork hCuQ he (by omega)
  have ht := cur.checkpoint src hSrc
  have hR := cur.continuation src hSrc
  have hEvent : ((X.tr (warpLane l g src)).drop (cur.pos src))[index-cur.pos src]? =
      some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hFollow.before]
    exact he
  obtain ⟨t,ht,hR⟩ := activeGeometryInputs ht
    (hR.after_local_nonempty (cur.localSteps src hSrc) hFollow.nonempty)
    hEvent (by omega)
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨u,hU,hu,hReads⟩ :=
    geometryLengthTraceBeforeEvent hp hX (stageOf ⟨warpIndex l g,hWarp⟩) hb hTile
      he hLate hFollow.before ht (fun off hOff => hCuQ (batch+off) (by omega)) (hUsedK batch hb) hR
  let j := cur.pos src
  have hBefore : j ≤ index := hFollow.before
  have hNe {k pc : Nat} {kind : Kind} (hGet : X.get (warpLane l g src,k) = some ⟨pc,kind⟩)
      (hPc : pc < 3374) : index ≠ k := by
    intro h
    have hSource := congrArg Event.pc (Option.some.inj ((h ▸ he).symm.trans hGet))
    change target.pc = pc at hSource
    omega
  have h0 := hNe hReads.1 (by decide)
  have h1 := hNe hReads.2.1 (by decide)
  have h2 := hNe hReads.2.2 (by decide)
  have hRel : j + 3 ≤ index := by
    change index ≠ j at h0
    change index ≠ j+1 at h1
    change index ≠ j+2 at h2
    omega
  have hMem : target ∈ (X.tr (warpLane l g src)).drop (j+3) := by
    apply List.mem_of_getElem? (i := index-(j+3))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hRel]
  exact ⟨batch,hb,hLo,hHi,j,u,_,hReads,hU,hu,hRel,hMem⟩

/-- A late active lane reads the request selected for its CTA and computes the
same full-tile block limit used by the MMA role. -/
theorem activeGeometryOfLateEvent (hLate : 7605 ≤ target.pc) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    ∃ batch, batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      ∃ j u result, FirstGeometryReads p X (warpLane l g src) j batch ∧
        At u 3418 (firstGeometryFacts p batch tile (stageOf warp)) ∧
        Run kernel Assumptions.all l (warpLane l g src) u
          ((X.tr (warpLane l g src)).drop (j+3)) result ∧
        j+3 ≤ index ∧ target ∈ (X.tr (warpLane l g src)).drop (j+3) :=
  activeGeometryOfEventPastReads hp hX hg hWarp hSrc hWork hCuQ hUsedK he (by omega)
end

/-- An exited active lane reads the request selected for its CTA and computes the
same full-tile block limit used by the MMA role. -/
theorem activeGeometryOfExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index pc : Nat} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hSrc : src < 32) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4*i)).at k))
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    (he : X.get (warpLane l g src,index) = some ⟨pc,.exit⟩) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    ∃ batch, batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      ∃ j u, FirstGeometryReads p X (warpLane l g src) j batch ∧
        At u 3418 (firstGeometryFacts p batch tile (stageOf warp)) ∧
        Run kernel Assumptions.all l (warpLane l g src) u
          ((X.tr (warpLane l g src)).drop (j+3)) none := by
  dsimp only
  have hpExit := actualExitPc hX he
  obtain ⟨batch,_,hb,hLo,hHi,ends,cur,hFollow⟩ :=
    activeTileOfEvent hp hX hg hWarp hSrc hWork hCuQ he (by simp [hpExit])
  have ht := cur.checkpoint src hSrc
  have hR := cur.continuation src hSrc
  have hEvent : ((X.tr (warpLane l g src)).drop (cur.pos src))[index-cur.pos src]? =
      some ⟨pc,.exit⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hFollow.before]
    exact he
  have hEnd : ends src = none := by
    cases he' : ends src with
    | none => rfl
    | some last =>
      rw [he'] at hR
      exact (hR.no_exit hEvent).elim
  rw [hEnd] at hR
  obtain ⟨t,ht,hR⟩ := activeGeometryInputs ht
    (hR.after_local_nonempty (cur.localSteps src hSrc) hFollow.nonempty)
    hEvent (by simp [hpExit])
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨u,hU,hu,hReads⟩ :=
    geometryLengthTrace hp hX (stageOf ⟨warpIndex l g,hWarp⟩) hb hTile ht
      (fun off hOff => hCuQ (batch+off) (by omega)) (hUsedK batch hb) hR
  exact ⟨batch,hb,hLo,hHi,cur.pos src,u,hReads,hU,hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax

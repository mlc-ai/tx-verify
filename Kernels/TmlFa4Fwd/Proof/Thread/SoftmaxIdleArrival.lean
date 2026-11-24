-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxIdleProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierExit
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Lemmas.Step.BarArrival
import Lemmas.Step.Released

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.MBarrier AsyncCopy Prologue Epilogue Correction

noncomputable section

private def idleWaitFrame (l : Launch) (g : Nat) (warp : Fin 8) : List (Nat × Value) :=
  (5864,b32 (waitLoc l g (stageOf warp) 9).addr) :: (7258,b32 1) :: idleCarry l warp

private theorem idleWaitReleased {l : Launch} {X : Execution} {g j : Nat}
    {loc : Loc} {ok : Bool} (he : X.get (g,j) = some ⟨7738,.wait loc 1 ok true .cta⟩)
    (hLast : j+1 = (X.tr g).length) : Step.Released l X g := by
  constructor
  intro site kind hGet _
  have hPos : (X.tr g).length-1 = j := by omega
  rw [hPos] at hGet ⊢
  rw [he] at hGet
  cases hGet
  exact Step.ready_of_wait he

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

private theorem idleWaitRecorded (warp : Fin 8) {current : State}
    (hObject : stateBefore (X.objects (waitLoc l g (stageOf warp) 9))
        (X.objects (waitLoc l g (stageOf warp) 9)).length = some current)
    (hZero : current.phase = 0) :
    ∀ (fuel pos : Nat) {t u : TState} {o : Option TState},
      (X.tr g).length-pos = fuel → 0 < pos → pos ≤ (X.tr g).length →
      (pos = (X.tr g).length → Step.Released l X g) →
      At u 7738 (idleWaitFrame l g warp) →
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) →
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u →
      ∃ j v w, X.get (g,j) = some ⟨7738,.wait (waitLoc l g (stageOf warp) 9) 1 true true .cta⟩ ∧
        At w 7741 (idleWaitFrame l g warp) ∧
        Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
        Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) o ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) v w := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro pos t u o hFuel hPos hBound hRelease hu hPrefix hTail hLocal
    let loc := waitLoc l g (stageOf warp) 9
    let post := fun ok => next (setReg u 9887 (.pred ok))
    have hOut : out kernel Assumptions.all l g u =
        .ev (.wait loc 1 post true .cta) :=
      waitTemplate hp (stageOf warp) 9 g u 1 hu.1 hu.2.2.2.1 (by decide)
        hu.2.2.2.2.1 hu.2.2.2.2.2.1
    have hn : Next kernel Assumptions.all l g t u (.wait loc 1 post true .cta) := ⟨hLocal,hOut⟩
    have hMore : pos < (X.tr g).length := by
      by_contra! hNo
      have hEq := Nat.le_antisymm hBound hNo
      have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
      have hFull : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
        rw [← List.take_of_length_le hNo]
        exact hPrefix
      have hES : EStep kernel Assumptions.all l g u
          ⟨u.pc,.wait loc 1 true true .cta⟩ (some (post true)) :=
        ⟨_,hOut,true,rfl,rfl⟩
      exact hMax.not_grows (Step.poll_counted_extension hMax.1 hg hStarted (hRelease hEq)
        (fun a ha _ _ => Assumptions.wfStep.quiet hMax.1
          (Execution.le_trans le_snoc (Execution.le_appendObject ..)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl)) a ha)
        hFull hLocal hES hObject (by rw [hZero]; decide))
    obtain ⟨_, _, hGet, ⟨ok,rfl,hRet⟩, hRest⟩ := hn.continuing_at_nonempty
      (by rintro _ ⟨_,_,hBad⟩; cases hBad) hTail
      (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
    obtain rfl := Option.some.inj hRet
    have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (post ok)) := by
      rw [List.take_succ_eq_append_getElem hMore, (List.getElem?_eq_some_iff.mp hGet).2]
      exact hPrefix.snoc hLocal ⟨_,hOut,ok,rfl,rfl⟩
    have hFrame := hu.set (v := .pred ok)
      (show ∀ pair ∈ idleWaitFrame l g warp, pair.1 ≠ 9887 from by
        simp [idleWaitFrame,idleCarry])
    obtain ⟨w,hw,hW⟩ := waitBranch 9 ok (hFrame.mono hFrame.2.2.2.2.2) hFrame.2.2.2.2.1
    rw [hu.1] at hGet
    cases ok with
    | true => exact ⟨pos,_,w,hGet,hW,hPast,hRest,run_rtg hw⟩
    | false =>
      exact ih ((X.tr g).length-(pos+1)) (by omega) (pos+1) rfl (by omega)
        (len_of_get hGet) (idleWaitReleased hGet) hW hPast hRest (run_rtg hw)

private theorem idleFinalArrivalFromTerminalCursor (hw : warpIndex l g < 8) {count : Nat}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7738 (fun lane =>
      idleWaitFrame l (warpLane l g lane) ⟨warpIndex l g,hw⟩) count 0 ends)
    (hReady : ∀ stage : Fin 2,
      let log := X.objects (statsCreditLoc l (g/l.block) stage)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    ∃ j t o, Thread.FinalAllocationArrival X (g,j) .arrive ∧
      At t 7742 (idleCarry l ⟨warpIndex l g,hw⟩) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨s,hs,hZero⟩ := hReady (stageOf warp)
  let pos := cur.pos lane
  let t := cur.before lane
  let u := cur.state lane
  have hAt : At u 7738 (idleWaitFrame l g warp) := by
    have ht : At u 7738 (idleWaitFrame l (warpLane l g lane) warp) := cur.checkpoint lane hl
    rwa [hSelf] at ht
  have hBound : pos ≤ (X.tr g).length := by simpa only [pos,hSelf] using cur.bounded lane hl
  have hRelease : pos = (X.tr g).length → Step.Released l X g := by
    simpa only [pos,hSelf] using cur.released lane hl
  have hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) := by
    simpa only [pos,t,hSelf] using cur.recorded lane hl
  have hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) (ends lane) := by
    simpa only [pos,t,hSelf] using cur.continuation lane hl
  have hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
    simpa only [t,u,hSelf] using cur.localSteps lane hl
  obtain ⟨j,v,w,he,hW,hPast,hRun,hwLocal⟩ := idleWaitRecorded hp hMax hg warp
    (show stateBefore (X.objects (waitLoc l g (stageOf warp) 9))
        (X.objects (waitLoc l g (stageOf warp) 9)).length = some s from hs)
    hZero ((X.tr g).length-pos) pos rfl (cur.positive lane hl) hBound hRelease
    hAt hPrefix hTail hLocal
  have hOut : out kernel Assumptions.all l g w = .ev (.bar 2 (next w) (some 416) .arrive) := by
    rw [out_event hW.2.2.2.1 (by rw [hW.1]; exact Flow.code_7741) rfl rfl]
    simp [eventTmpl, barTmpl, readBits, pure, Except.pure, hp.block,
      show (truncBits 32 2#64).toNat = 2 by decide,
      show (truncBits 32 416#64).toNat = 416 by decide]
  have hj : j+1 < (X.tr g).length := by
    by_contra! hLe
    have hLen : j+1 = (X.tr g).length := Nat.le_antisymm (len_of_get he) hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hLen; omega
    rw [List.take_of_length_le hLe] at hPast
    exact hMax.not_grows (Step.barArrival_counted_extension hMax.1 hg (.inl hStarted)
      (idleWaitReleased he hLen) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl))
      hPast hwLocal ⟨_,hOut,rfl,rfl⟩)
  have hn : Next kernel Assumptions.all l g v w (.bar 2 (next w) (some 416) .arrive) :=
    ⟨hwLocal,hOut⟩
  obtain ⟨_, _, hGet, ⟨rfl,hRet⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) hRun
    (fun h => (Nat.not_le_of_lt hj) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  have hPre : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1+1))
      (some (next w)) := by
    rw [List.take_succ_eq_append_getElem hj, (List.getElem?_eq_some_iff.mp hGet).2]
    exact hPast.snoc hwLocal ⟨_,hOut,rfl,rfl⟩
  have hAt' := hW.next.mono hW.2.2.2.2.2.2
  exact ⟨j+1,next w,ends lane,Thread.FinalAllocationArrival.of_decoded (by decide) (hW.1 ▸ hGet),
    hAt',hPre,hRest⟩

/-- Every idle softmax lane records the final allocation arrival once its statistics
object is in the initialization phase. -/
theorem idleFinalArrivalPrefixOfAllGroups (hw : warpIndex l g < 8)
    (hProtected : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hReady : ∀ stage : Fin 2,
      let log := X.objects (statsCreditLoc l (g/l.block) stage)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    ∃ j t o, Thread.FinalAllocationArrival X (g,j) .arrive ∧
      At t 7742 (idleCarry l ⟨warpIndex l g,hw⟩) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  obtain ⟨_,_,⟨cur⟩⟩ := idleTerminalPollCursorOfAllGroups hp hMax hg hw hProtected hIdle
  exact idleFinalArrivalFromTerminalCursor hp hMax hg hw cur hReady

end
end PTX.Kernels.TmlFa4Fwd.Softmax

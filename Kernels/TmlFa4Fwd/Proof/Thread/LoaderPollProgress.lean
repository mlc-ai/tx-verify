-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
import Lemmas.Step.Released
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.DrainInOrder
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Epilogue

noncomputable section

private theorem pollReleased {l : Launch} {X : Execution} {g j phase : Nat}
    {site : DrainWaitSite} {loc : Loc} {ok : Bool}
    (he : X.get (g,j) = some ⟨site.pc,.wait loc phase ok true .cta⟩)
    (hLast : j+1 = (X.tr g).length) : Step.Released l X g := by
  constructor
  intro pc kind hGet _
  have hPos : (X.tr g).length-1 = j := by omega
  rw [hPos] at hGet ⊢
  rw [he] at hGet
  cases hGet
  exact Step.ready_of_wait he

private theorem pollRecorded {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    {site : DrainWaitSite} (hCode : LoaderWaitCode site)
    (hRange : 174 ≤ site.pc ∧ site.pc + 3 < 1906) {addr phase : Nat}
    (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0)
    (hPhase : phase < 2) {F : List (Nat × Value)}
    (hFresh : ∀ pair ∈ F, pair.1 ≠ site.result) (hBase : (site.base,b32 addr) ∈ F)
    (hPar : (site.phase,b32 phase) ∈ F)
    {origin : Nat}
    (hReady : ∀ {t u : TState},
      Run kernel Assumptions.all l g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u → At u site.pc F →
      (∀ e ∈ (X.tr g).drop origin,
        e = ⟨site.pc,.wait ⟨.shared,g/l.block,addr⟩ phase false true .cta⟩) →
      ∃ current, stateBefore (X.objects ⟨.shared,g/l.block,addr⟩)
        (X.objects ⟨.shared,g/l.block,addr⟩).length = some current ∧ current.phase % 2 ≠ phase % 2)
    {shuffles votes : Nat} :
    ∀ (fuel pos : Nat) {t u : TState} {o : Option TState},
      (X.tr g).length-pos = fuel → origin ≤ pos →
      (∀ e ∈ ((X.tr g).drop origin).take (pos-origin),
        e = ⟨site.pc,.wait ⟨.shared,g/l.block,addr⟩ phase false true .cta⟩) →
      0 < pos → pos ≤ (X.tr g).length →
      (pos = (X.tr g).length → Step.Released l X g) →
      ((X.tr g).take pos).countP Execution.isShfl = shuffles →
      ((X.tr g).take pos).countP isFullWarpVote = votes →
      At u site.pc F →
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) →
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u →
      ∃ n j v w, X.get (g,j) = some ⟨site.pc,.wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ ∧
        At w (site.pc+3) F ∧
        Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
        Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) o ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) v w ∧
        ((X.tr g).take (j+1)).countP Execution.isShfl = shuffles ∧
        ((X.tr g).take (j+1)).countP isFullWarpVote = votes ∧ j = pos+n ∧
        (X.tr g).drop pos = List.replicate n ⟨site.pc,.wait ⟨.shared,g/l.block,addr⟩
          phase false true .cta⟩ ++
          (⟨site.pc,.wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ ::
            (X.tr g).drop (j+1)) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro pos t u o hFuel hOrigin hPastWait hPos hBound hRelease hS hV hu hPrefix hTail hLocal
    let loc : Loc := ⟨.shared,g/l.block,addr⟩
    let post := fun ok => next (setReg u site.result (.pred ok))
    have hOut : out kernel Assumptions.all l g u = .ev (.wait loc phase post true .cta) :=
      loaderWaitTemplate site hCode hRange hAddr hAlign hPhase hu.1 hu.2.2.2.1
        (holds_mem hu.2.2.2.2 hBase) (holds_mem hu.2.2.2.2 hPar)
    have hn : Next kernel Assumptions.all l g t u (.wait loc phase post true .cta) := ⟨hLocal,hOut⟩
    have hMore : pos < (X.tr g).length := by
      by_contra! hNo
      have hEq := Nat.le_antisymm hBound hNo
      have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
      have hFull : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
        rw [← List.take_of_length_le hNo]
        exact hPrefix
      have hES : EStep kernel Assumptions.all l g u
          ⟨u.pc,.wait loc phase true true .cta⟩ (some (post true)) :=
        ⟨_,hOut,true,rfl,rfl⟩
      have hBlocked : ∀ e ∈ (X.tr g).drop origin,
          e = ⟨site.pc,.wait loc phase false true .cta⟩ := by
        rw [hEq,List.take_of_length_le (by simp)] at hPastWait
        exact hPastWait
      obtain ⟨current,hObject,hZero⟩ := hReady hFull hLocal hu hBlocked
      exact hMax.not_grows (Step.poll_counted_extension hMax.1 hg hStarted (hRelease hEq)
        (fun a ha _ _ => Assumptions.wfStep.quiet hMax.1
          (Execution.le_trans le_snoc (Execution.le_appendObject ..)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl)) a ha)
        hFull hLocal hES hObject hZero)
    obtain ⟨_,_,hGet,⟨ok,rfl,hRet⟩,hRest⟩ := hn.continuing_at_nonempty
      (by rintro _ ⟨_,_,hBad⟩; cases hBad) hTail
      (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
    obtain rfl := Option.some.inj hRet
    have hCut := List.take_succ_eq_append_getElem hMore
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hCut
    have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (post ok)) := by
      rw [hCut]
      exact hPrefix.snoc hLocal ⟨_,hOut,ok,rfl,rfl⟩
    have hS' : ((X.tr g).take (pos+1)).countP Execution.isShfl = shuffles := by
      rw [hCut,List.countP_append,hS]
      rfl
    have hV' : ((X.tr g).take (pos+1)).countP isFullWarpVote = votes := by
      rw [hCut,List.countP_append,hV]
      rfl
    obtain ⟨w,hw,hW⟩ := loaderAfterWait site hCode hRange ok (hu.set hFresh)
    rw [hu.1] at hGet
    have hSkip := List.drop_eq_getElem_cons hMore
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hSkip
    cases ok with
    | true => exact ⟨0,pos,_,w,hGet,hW,hPast,hRest,hw,hS',hV',rfl,hSkip⟩
    | false =>
      have hWaits : ∀ e ∈ ((X.tr g).drop origin).take (pos+1-origin),
          e = ⟨site.pc,.wait loc phase false true .cta⟩ := by
        rw [show pos+1-origin = (pos-origin)+1 by omega,List.take_add,
          List.drop_drop,Nat.add_sub_of_le hOrigin,hSkip,List.take_succ_cons,List.take_zero]
        intro e hm
        rcases List.mem_append.mp hm with h | h
        · exact hPastWait e h
        · simpa only [List.mem_singleton] using h
      obtain ⟨n,j,v,z,he,hAt,hDone,hRest,hLocal,hS,hV,hIndex,hTrace⟩ :=
        ih ((X.tr g).length-(pos+1)) (by omega) (pos+1) rfl (by omega) hWaits (by omega)
          (len_of_get hGet) (pollReleased hGet) hS' hV' hW hPast hRest hw
      exact ⟨n+1,j,v,z,he,hAt,hDone,hRest,hLocal,hS,hV,by omega,by
        rw [hSkip,hTrace,List.replicate_succ,List.cons_append]⟩

section
variable {l : Launch} {m : Mem0} {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hBlock : l.block % 32 = 0) {site : DrainWaitSite}
    (hCode : LoaderWaitCode site) (hRange : 174 ≤ site.pc ∧ site.pc+3 < 1906) {addr phase : Nat}
    (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0) (hPhase : phase < 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g site.pc F shuffles votes ends)
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ site.result)
    (hBase : ∀ lane < 32, (site.base,b32 addr) ∈ F lane)
include hMax hg hBlock hCode hRange hAddr hAlign hPhase cur hFresh hBase

/-- A maximal loader warp crosses a parity wait when a lane stopped there
leaves the object in the opposite phase. The readiness callback knows that this
lane’s whole suffix from the incoming cursor consists of failed polls. -/
theorem loaderWarpWaitOfBlockedPhaseTrace (hPar : ∀ lane < 32, (site.phase,b32 phase) ∈ F lane)
    (hReady : ∀ (lane : Nat), lane < 32 → ∀ {t u : TState},
      Run kernel Assumptions.all l (warpLane l g lane) {} (X.tr (warpLane l g lane)) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u →
      At u site.pc (F lane) →
      (∀ e ∈ (X.tr (warpLane l g lane)).drop (cur.pos lane),
        e = ⟨site.pc,.wait ⟨.shared,warpLane l g lane/l.block,addr⟩ phase false true .cta⟩) →
      ∃ current, stateBefore (X.objects ⟨.shared,g/l.block,addr⟩)
        (X.objects ⟨.shared,g/l.block,addr⟩).length = some current ∧
          current.phase % 2 ≠ phase % 2) :
    ∃ done : SchedulerWarpReached l X g (site.pc+3) F shuffles votes ends,
      ∀ lane < 32, ∃ n,
        let thread := warpLane l g lane
        let wait := fun ok =>
          Event.mk site.pc (.wait ⟨.shared,thread/l.block,addr⟩ phase ok true .cta)
        done.pos lane = cur.pos lane+n+1 ∧
          (X.tr thread).drop (cur.pos lane) =
            List.replicate n (wait false) ++ (wait true :: (X.tr thread).drop (done.pos lane)) := by
  classical
  let thread := warpLane l g
  have hLane (lane : Nat) (hl : lane < 32) : ∃ n j v w,
      X.get (thread lane,j) = some ⟨site.pc,.wait ⟨.shared,thread lane/l.block,addr⟩
        phase true true .cta⟩ ∧ At w (site.pc+3) (F lane) ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take (j+1)) (some v) ∧
      Run kernel Assumptions.all l (thread lane) v ((X.tr (thread lane)).drop (j+1)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) v w ∧
      ((X.tr (thread lane)).take (j+1)).countP Execution.isShfl = shuffles ∧
      ((X.tr (thread lane)).take (j+1)).countP isFullWarpVote = votes ∧
      j = cur.pos lane+n ∧
      (X.tr (thread lane)).drop (cur.pos lane) = List.replicate n
        ⟨site.pc,.wait ⟨.shared,thread lane/l.block,addr⟩ phase false true .cta⟩ ++
        (⟨site.pc,.wait ⟨.shared,thread lane/l.block,addr⟩ phase true true .cta⟩ ::
          (X.tr (thread lane)).drop (j+1)) := by
    have hs := (Step.sameWarp_lane hBlock hg hl).1.1
    have hCta : thread lane/l.block = g/l.block := hs.2.2.symm
    have hCanPoll {t u : TState}
        (hRun : Run kernel Assumptions.all l (thread lane) {} (X.tr (thread lane)) (some t))
        (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) t u)
        (hAt : At u site.pc (F lane))
        (hFailed : ∀ e ∈ (X.tr (thread lane)).drop (cur.pos lane),
          e = ⟨site.pc,.wait ⟨.shared,thread lane/l.block,addr⟩ phase false true .cta⟩) :
        ∃ current, stateBefore (X.objects ⟨.shared,thread lane/l.block,addr⟩)
          (X.objects ⟨.shared,thread lane/l.block,addr⟩).length = some current ∧
          current.phase % 2 ≠ phase % 2 := hCta.symm ▸ hReady lane hl hRun hLocal hAt hFailed
    exact pollRecorded hMax hs.2.1 hCode hRange hAddr hAlign hPhase (hFresh lane hl)
      (hBase lane hl) (hPar lane hl) (origin := cur.pos lane)
      hCanPoll _ (cur.pos lane) rfl le_rfl (by simp)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
      (cur.ordinals.shfl lane hl) (cur.ordinals.vote lane hl) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.continuation lane hl) (cur.localSteps lane hl)
  let _ : Inhabited TState := ⟨{}⟩
  choose! n j before state he hAt hPrefix hTail hLocal hS hVote hIndex hTrace using hLane
  refine ⟨⟨⟨fun lane => j lane+1,before,state,⟨hS,hVote⟩,hTail,hLocal,hAt⟩,
    fun _ _ => Nat.succ_pos _,fun lane hl => len_of_get (he lane hl),
    fun lane hl => pollReleased (he lane hl),hPrefix⟩,fun lane hl => ⟨n lane,?_,hTrace lane hl⟩⟩
  simp only
  rw [hIndex lane hl]

/-- A maximal loader warp crosses a parity wait when a lane stopped there
leaves the object in the opposite phase. -/
theorem loaderWarpWaitOfOppositePhaseTrace (hPar : ∀ lane < 32, (site.phase,b32 phase) ∈ F lane)
    (hReady : ∀ (lane : Nat), lane < 32 → ∀ {t u : TState},
      Run kernel Assumptions.all l (warpLane l g lane) {} (X.tr (warpLane l g lane)) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u →
      At u site.pc (F lane) →
      ∃ current, stateBefore (X.objects ⟨.shared,g/l.block,addr⟩)
        (X.objects ⟨.shared,g/l.block,addr⟩).length = some current ∧
          current.phase % 2 ≠ phase % 2) :
    ∃ done : SchedulerWarpReached l X g (site.pc+3) F shuffles votes ends,
      ∀ lane < 32, ∃ n,
        let thread := warpLane l g lane
        let wait := fun ok =>
          Event.mk site.pc (.wait ⟨.shared,thread/l.block,addr⟩ phase ok true .cta)
        done.pos lane = cur.pos lane+n+1 ∧
          (X.tr thread).drop (cur.pos lane) =
            List.replicate n (wait false) ++ (wait true :: (X.tr thread).drop (done.pos lane)) :=
  loaderWarpWaitOfBlockedPhaseTrace hMax hg hBlock hCode hRange hAddr hAlign hPhase
    cur hFresh hBase hPar (fun lane hl {_ _} hRun hLocal hAt _ => hReady lane hl hRun hLocal hAt)
end

variable {l : Launch} {m : Mem0} {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hBlock : l.block % 32 = 0) {site : DrainWaitSite}
    (hCode : LoaderWaitCode site) (hRange : 174 ≤ site.pc ∧ site.pc+3 < 1906) {addr : Nat}
    (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g site.pc F shuffles votes ends)
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ site.result)
    (hBase : ∀ lane < 32, (site.base,b32 addr) ∈ F lane)
include hMax hg hBlock hCode hRange hAddr hAlign cur hFresh hBase

/-- A maximal loader warp crosses a parity-one wait when a lane stopped there
always leaves a phase-zero object. -/
theorem loaderWarpWaitOfReadyLastTrace (hPar : ∀ lane < 32, (site.phase,b32 1) ∈ F lane)
    (hReady : ∀ (lane : Nat), lane < 32 → ∀ {t u : TState},
      Run kernel Assumptions.all l (warpLane l g lane) {} (X.tr (warpLane l g lane)) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u →
      At u site.pc (F lane) →
      ∃ current, stateBefore (X.objects ⟨.shared,g/l.block,addr⟩)
        (X.objects ⟨.shared,g/l.block,addr⟩).length = some current ∧ current.phase = 0) :
    ∃ done : SchedulerWarpReached l X g (site.pc+3) F shuffles votes ends,
      ∀ lane < 32, ∃ n,
        let thread := warpLane l g lane
        let wait := fun ok => Event.mk site.pc (.wait ⟨.shared,thread/l.block,addr⟩ 1 ok true .cta)
        done.pos lane = cur.pos lane+n+1 ∧
          (X.tr thread).drop (cur.pos lane) =
            List.replicate n (wait false) ++ (wait true :: (X.tr thread).drop (done.pos lane)) :=
  loaderWarpWaitOfOppositePhaseTrace hMax hg hBlock hCode hRange hAddr hAlign (by decide)
    cur hFresh hBase hPar (fun lane hl {_ _} hr hs ht => by
      obtain ⟨current,hObject,hZero⟩ := hReady lane hl hr hs ht
      exact ⟨current,hObject,by rw [hZero]; decide⟩)

/-- A maximal loader warp crosses a parity-one wait when a lane stopped there
always leaves a phase-zero object. -/
theorem loaderWarpWaitOfReadyLast (hPar : ∀ lane < 32, (site.phase,b32 1) ∈ F lane)
    (hReady : ∀ (lane : Nat), lane < 32 → ∀ {t u : TState},
      Run kernel Assumptions.all l (warpLane l g lane) {} (X.tr (warpLane l g lane)) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u →
      At u site.pc (F lane) →
      ∃ current, stateBefore (X.objects ⟨.shared,g/l.block,addr⟩)
        (X.objects ⟨.shared,g/l.block,addr⟩).length = some current ∧ current.phase = 0) :
    Nonempty (SchedulerWarpReached l X g (site.pc+3) F shuffles votes ends) := by
  obtain ⟨done,_⟩ := loaderWarpWaitOfReadyLastTrace hMax hg hBlock hCode hRange
    hAddr hAlign cur hFresh hBase hPar hReady
  exact ⟨done⟩

/-- A maximal loader warp crosses an initialized parity-one wait after finitely many retries. -/
theorem loaderWarpWaitOfPhaseZero (hPar : ∀ lane < 32, (site.phase,b32 1) ∈ F lane)
    {current : State}
    (hObject : stateBefore (X.objects ⟨.shared,g/l.block,addr⟩)
      (X.objects ⟨.shared,g/l.block,addr⟩).length = some current) (hZero : current.phase = 0) :
    Nonempty (SchedulerWarpReached l X g (site.pc+3) F shuffles votes ends) :=
  loaderWarpWaitOfReadyLast hMax hg hBlock hCode hRange hAddr hAlign cur hFresh hBase hPar
    (fun _ _ {_ _} _ _ _ => ⟨current,hObject,hZero⟩)

end
end PTX.Kernels.TmlFa4Fwd.Loader

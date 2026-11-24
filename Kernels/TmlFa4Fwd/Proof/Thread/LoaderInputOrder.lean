-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
public import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
public import Kernels.TmlFa4Fwd.Proof.ProxyFenceAudit
public import Lemmas.Flow.NotWarpBar
public import Lemmas.Flow.NotProxyFence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue
open PTX.Kernels.TmlFa4Fwd.Loader Epilogue

private theorem fullLoaderBranches (bound : Nat) :
    ((kernel.code.drop 174).take (1901 - 174)).all
      (fun i => loaderPipelineCutOp 174 1901 bound [2535, 1062] i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem afterFirstQBranches (bound : Nat) :
    ((kernel.code.drop 694).take (1901 - 694)).all
      (fun i => loaderPipelineCutOp 694 1901 bound [2535, 1062] i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem earlyPredecessorInWalk {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (warp : Fin 2) {cut : Nat}
    (hCut : 174 ≤ cut ∧ cut ≤ 1901)
    (hBranches : ∀ bound, ((kernel.code.drop cut).take (1901 - cut)).all
      (fun i => loaderPipelineCutOp cut 1901 bound [2535, 1062] i.op) = true)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hShape : RingShape s)
    (hRegs : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    {i j : Nat} {earlier later : Event} (hIndex : i ≤ j)
    (hEarly : events[i]? = some earlier) (hLate : events[j]? = some later)
    (hBound : later.pc < cut) : earlier.pc < cut := by
  let frame := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]
  induction hw generalizing i j with
  | stop => simp at hLate
  | @tau t u es vs ht hw ih =>
    by_cases hHigh : cut ≤ t.pc
    · have hB := Epilogue.loaderWalkEventRange warp hCut.1 ⟨hHigh, hPc.2⟩ hShape hRegs
        hBranches (.tau ht hw) later (List.mem_of_getElem? hLate)
      omega
    have hSource : t.pc < 1901 := by omega
    obtain ⟨hLo, hHi, huShape, huRegs⟩ :=
      pipelineCutStep (F := frame) (by decide) (by decide) ⟨hPc.1, hSource⟩
        (fullLoaderBranches u.pc) (.inl ⟨rfl, ht⟩) hShape hRegs
    exact ih ⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩ huShape huRegs hIndex hEarly hLate
  | @ev t u e es vs he hw ih =>
    by_cases hHigh : cut ≤ t.pc
    · have hB := Epilogue.loaderWalkEventRange warp hCut.1 ⟨hHigh, hPc.2⟩ hShape hRegs
        hBranches (.ev he hw) later (List.mem_of_getElem? hLate)
      omega
    cases i with
    | zero =>
      have hEq : e = earlier := Option.some.inj hEarly
      rw [← hEq, estep_source_pc he]
      omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have hSource : t.pc < 1901 := by omega
        obtain ⟨hLo, hHi, huShape, huRegs⟩ :=
          pipelineCutStep (F := frame) (by decide) (by decide) ⟨hPc.1, hSource⟩
            (fullLoaderBranches u.pc) (.inr ⟨_, rfl, he⟩) hShape hRegs
        exact ih ⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩ huShape huRegs
          (Nat.le_of_succ_le_succ hIndex) hEarly hLate
  | @last t e he =>
    have hi : i = 0 := by
      have hLt := (List.getElem?_eq_some_iff.mp hEarly).1
      simpa using hLt
    subst i
    have hj : j = 0 := by
      have hLt := (List.getElem?_eq_some_iff.mp hLate).1
      simpa using hLt
    subst j
    exact Option.some.inj (hEarly.symm.trans hLate) ▸ hBound

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An actual earlier event precedes the same closed loader cut as a later event. -/
theorem eventBeforeClosedCut (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j cut : Nat} (hWarp : 14 ≤ warpIndex l g) {e f : Event} (hCut : 174 ≤ cut ∧ cut ≤ 1901)
    (hBranches : ∀ bound, ((kernel.code.drop cut).take (1901 - cut)).all
      (fun ins => loaderPipelineCutOp cut 1901 bound [2535, 1062] ins.op) = true)
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f) (hij : i ≤ j) (hLate : 173 < f.pc)
    (hBound : f.pc < cut) : e.pc < cut := by
  have hg : g < l.threads := event_thread_lt hX hf
  have hNonzero : 0 < warpIndex l g := by omega
  obtain ⟨state, result, hj, hState, hRun⟩ :=
    nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero hf hLate
  by_cases hi : 5 ≤ i
  · let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
    have hIdentity : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
    have hAt : At state 174 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] :=
      hState.mono ⟨hState.2.2.2.2.2.1, hIdentity.symm ▸ hState.2.2.2.2.1, trivial⟩
    obtain ⟨visits, hw⟩ := Mma.walkFromRun hRun
    have he' : ((X.tr g).drop 5)[i - 5]? = some e := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hi]
      exact he
    have hf' : ((X.tr g).drop 5)[j - 5]? = some f := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hj]
      exact hf
    apply earlyPredecessorInWalk warp hCut hBranches hw (by rw [hAt.1]; decide) (ringShapeOfAt hAt)
      hAt.2.2.2.2 (by omega) he' hf' hBound
  · by_contra! h
    obtain ⟨_, _, hi', _, _⟩ :=
      nonzeroCommonPrefixOfLateEvent hp hX hg hNonzero he (by omega)
    exact hi hi'

private theorem earlierLoaderEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} (hWarp : 14 ≤ warpIndex l g) {e f : Event} (he : X.get (g, i) = some e)
    (hf : X.get (g, j) = some f) (hij : i ≤ j) (hLate : 173 < f.pc) (hBound : f.pc < 694)
    : e.pc < 694 :=
  eventBeforeClosedCut hp hX hWarp (by decide) afterFirstQBranches he hf hij hLate hBound

private def InitialInputPrefix (l : Launch) (X : Execution) (i : EvId) : Prop :=
  ∃ e, X.get i = some e ∧
    (e.pc < 174 ∨ 14 ≤ warpIndex l i.1 ∧ e.pc < 694)

private theorem initialPrefixEarlier (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {e : Event} (he : X.get (g, i) = some e) (hIndex : i ≤ j) :
    InitialInputPrefix l X (g, j) → InitialInputPrefix l X (g, i) := by
  rintro ⟨f, hf, hStart | ⟨hWarp, hBound⟩⟩
  · exact ⟨e, he, .inl (earlierStartupEvent hX he hf hIndex hStart)⟩
  by_cases h : f.pc < 174
  · exact ⟨e, he, .inl (earlierStartupEvent hX he hf hIndex h)⟩
  · exact ⟨e, he, .inr ⟨hWarp, earlierLoaderEvent hp hX hWarp he hf hIndex (by omega) hBound⟩⟩

private theorem earlyPollSites {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {site parity : Nat}
    {loc : Loc} {scope : MbarScope}
    (he : X.get i = some ⟨site, .wait loc parity true true scope⟩) (hSite : site < 694) :
    site = 517 ∨ site = 679 := by
  have hOnly : OpPcsFast (kernel.code.take 694) isMbarPoll [517, 679] = true := by
    decide +kernel
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hCode, hFire⟩
  · cases hBad
  have hTake : (kernel.code.take 694)[site]? = some ins := by
    rw [List.getElem?_take_of_lt hSite]
    exact hCode
  obtain ⟨_, _, _, _, _, hOp, _⟩ := fires_wait_flags hFire rfl
  have hChosen := OpPcsFast.mem hOnly hTake (show isMbarPoll ins.op = true by rw [hOp]; rfl)
  simpa using hChosen

private def notWarpBar (op : Op) : Bool :=
  match op with
  | .warp w => match w.kind with
    | .barWarp => false
    | _ => true
  | _ => true

private theorem noEarlyWarpBar {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {site mask inst : Nat}
    (he : X.get i = some ⟨site, .warpBar mask inst⟩) (hEarly : site < 694) : False := by
  have hCode : (kernel.code.take 694).all (fun i => notWarpBar i.op) = true := by decide +kernel
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hGet, hFires⟩
  · cases hBad
  have hTake : (kernel.code.take 694)[site]? = some ins := by
    rw [List.getElem?_take_of_lt hEarly]
    exact hGet
  have hChecked := List.all_eq_true.mp hCode _ (List.mem_of_getElem? hTake)
  apply fires_notWarpBar_op (op := ins.op) _ hFires mask inst rfl
  intro w hOp hKind
  simp [hOp, notWarpBar, hKind] at hChecked

private theorem initialPrefixClosed (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} (hOrder : baseCausality l X i j) :
    InitialInputPrefix l X j → InitialInputPrefix l X i := by
  have step {u v : EvId} (hStep : po X u v ∨ CtaBarSync l X u v ∨ MSync l X u v ∨
      ClusterSync l X u v ∨ WarpBarSync l X u v ∨ synchronizesWith l X u v ∨
      FenceSync l X u v) (hv : InitialInputPrefix l X v) : InitialInputPrefix l X u := by
    rcases hStep with h | h | h | h | h | h | h
    · obtain ⟨hLane, hBefore, _, _⟩ := h
      have hId : u = (v.1, u.2) := Prod.ext hLane rfl
      rw [hId]
      have hLen : u.2 < (X.tr v.1).length := by
        obtain ⟨e, he, _⟩ := hv
        exact hBefore.trans (List.getElem?_eq_some_iff.mp he).1
      exact initialPrefixEarlier hp hX (List.getElem?_eq_getElem hLen) hBefore.le hv
    · obtain ⟨_, key, a, b, hA, hB, ha, hb, _⟩ := h
      obtain ⟨count, site, hGet⟩ := hB.2.1
      have hEarly := initialPrefixEarlier hp hX hGet hb.le hv
      have hBound : site < 694 := by
        obtain ⟨ev, he, hPc | ⟨_, hPc⟩⟩ := hEarly <;>
          have hEq := congrArg Event.pc (Option.some.inj (hGet.symm.trans he)) <;>
          change site = ev.pc at hEq <;> omega
      obtain ⟨hSites, _, _, _, _, hId, _⟩ := actualNamedBarrier hp hX hGet
      have hSite : site = 173 := by
        simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSites
        omega
      obtain ⟨count', site', mode, hSource⟩ := hA.2.1
      have hCount := actualNamedBarrierCountById hp hX hSource
      rw [hId hSite] at hCount
      have hOrigin := ((actualNamedBarrier hp hX hSource).2.2.2.2.1).mp hCount
      have hLen : u.2 < (X.tr u.1).length := ha.trans (List.getElem?_eq_some_iff.mp hSource).1
      have hU : X.get u = some (X.tr u.1)[u.2] := List.getElem?_eq_getElem hLen
      have hStart := earlierStartupEvent hX hU hSource ha.le (by simp [hOrigin])
      exact ⟨_, hU, .inl hStart⟩
    · obtain ⟨release, ⟨g, index⟩, target, _, scope, ⟨tx, count, hRel⟩,
        ⟨⟨site, parity, hWait⟩, _⟩, _, hThread, hBefore, _⟩ := h
      cases v
      change g = _ at hThread
      subst g
      obtain ⟨_, he, hPc | ⟨_, hPc⟩⟩ := initialPrefixEarlier hp hX hWait hBefore.le hv
      · have hSite : site < 174 := by simpa [← Option.some.inj (hWait.symm.trans he)] using hPc
        rcases earlyPollSites hX hWait (by omega) with h | h <;> omega
      · have hSite : site < 694 := by simpa [← Option.some.inj (hWait.symm.trans he)] using hPc
        obtain ⟨offset, hOff, rfl⟩ :=
          initialLoaderWaitAddress hp hX hWait (earlyPollSites hX hWait hSite)
        exact (noOrdinaryInitialInputCredit hp hX hOff hRel).elim
    · obtain ⟨_, _, _, hSync, _⟩ := h
      obtain ⟨_, hArrival, _⟩ := hSync
      obtain ⟨_, _, he⟩ := hX.cluster.arrival_present hArrival
      exact (noClusterEvent hX he).elim
    · obtain ⟨_, idx, ⟨_, mask, inst, _, site, he⟩, _, hBefore, _⟩ := h
      obtain ⟨ev, hf, hPc | ⟨_, hPc⟩⟩ := initialPrefixEarlier hp hX he hBefore.le hv <;>
        have hEq := congrArg Event.pc (Option.some.inj (he.symm.trans hf)) <;>
        change site = ev.pc at hEq <;>
        exact (noEarlyWarpBar hX he (by omega)).elim
    · exact (noSynchronizesWith_of (fun _ _ _ _ he => noReleasingStore hX he)
        (fun _ _ _ _ _ he => (noAtomicEvent hX he).elim) _ _ h).elim
    · exact (not_fenceSync_of_noFence (fun _ _ _ => noThreadFence hX) _ _ h).elim
  induction hOrder with
  | single h => exact step h
  | tail _ h ih => exact fun hj => ih (step h hj)

/-- No proxy fence precedes a tensor issue at the first query load site. -/
theorem noProxyBeforeFirstQuery (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i writer : EvId} {addr : Nat} {s : TensorCopy.Spec} {loc : Loc}
    (hi : X.get i = some ⟨693, .tensorIssue addr s⟩) : ¬ ProxyBefore l X writer i loc := by
  have hRole : roleBodyPc (warpIndex l i.1) 693 :=
    roleBodyPcOfEvent hp hX hi (by change 173 < 693; decide)
      (by change 693 ∉ registerHintSites; decide)
  have hWarp : 14 ≤ warpIndex l i.1 := by
    simpa [roleBodyPc] using hRole
  rintro ⟨fence, mode, scope, ⟨site, he⟩, _, _, _, _, hBefore⟩
  obtain ⟨e, hf, hPc | ⟨_, hPc⟩⟩ := initialPrefixClosed hp hX hBefore
    ⟨_, hi, .inr ⟨hWarp, by change 693 < 694; decide⟩⟩
  all_goals
    have hs : site < 694 := by
      rw [← Option.some.inj (he.symm.trans hf)] at hPc
      first | exact hPc | exact (Nat.lt_trans hPc (by decide))
    have hNo : OpPcsFast (kernel.code.take 694) proxyFenceOp [] = true := by decide +kernel
    rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hCode, hFire⟩
    · cases hBad
    have hTake : (kernel.code.take 694)[site]? = some ins := by
      rw [List.getElem?_take_of_lt hs]
      exact hCode
    exact List.not_mem_nil (OpPcsFast.mem hNo hTake (fires_proxyFence_op hFire rfl))

/-- The input role issued its first query subbox. -/
def FirstQueryIssue (X : Execution) (i : EvId) (address : Nat) (s : TensorCopy.Spec) : Prop :=
  X.get i = some ⟨693, .tensorIssue address s⟩

theorem FirstQueryIssue.issue {X : Execution} {i : EvId} {address : Nat} {s : TensorCopy.Spec}
    (h : FirstQueryIssue X i address s) : X.TensorIssue i address s := ⟨_, h⟩

/-- No ordinary thread access is visible to a destination write of the first query subbox. -/
theorem noThreadBeforeFirstQuery (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i writer : EvId} {address : Nat} {s : TensorCopy.Spec} {loc : Loc} {qx qy k : Nat}
    (hi : FirstQueryIssue X i address s) :
    ¬ modelCausality l X loc (.thread writer) (.async i (.write (.load qx qy k))) := by
  have hNo : ¬ GenericCopy X i := by
    rintro ⟨_, ⟨site, he⟩, _⟩
    change X.get i = some ⟨693, .tensorIssue address s⟩ at hi
    rw [hi] at he
    cases he
  rw [modelCausality_thread_async_of_not_generic l hNo]
  exact fun h => noProxyBeforeFirstQuery hp hX hi h.2

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

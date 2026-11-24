-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderIdleDrainProgress
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
import Lemmas.Step.WarpElect
import Lemmas.Order.ElectOrdinal
import Lemmas.Protocol.ElectCount
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.DrainInOrder
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.Object
import Lemmas.Flow.ReturningPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption AsyncCopy Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem afterIdleElectionCode :
    (kernel.code.drop 1897).all (fun i => Thread.staysPastEvent 1897 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterIdleElectionSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (1897 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 3000 in
private theorem afterIdleElection {l : Launch} {g : Nat} {t u : TState}
    {events : List Event} (hTrace : TraceReach kernel Assumptions.all l g t events u)
    (ht : 1897 ≤ t.pc) : 1897 ≤ u.pc := by
  induction hTrace with
  | refl => exact ht
  | tau ht' _ ih => exact ih (Thread.eventTailStepOfAudit afterIdleElectionCode
      afterIdleElectionSegments ht (.inl ⟨rfl,ht'⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit afterIdleElectionCode
      afterIdleElectionSegments ht (.inr ⟨_,rfl,he⟩))

private theorem noEarlierIdleElection {l : Launch} {g : Nat} {t u : TState} {events : List Event}
    (hTrace : TraceReach kernel Assumptions.all l g t events u) (hu : u.pc ≤ 1896) :
    ∀ e ∈ events, e.pc ≠ 1896 := by
  induction hTrace with
  | refl => simp
  | tau _ _ ih => exact ih hu
  | @event t v u es e he hTail ih =>
    intro ev hMem hPc
    rcases List.mem_cons.mp hMem with rfl | hMem
    · have hSite : t.pc = 1896 := (EventFrame.estep_source_pc he).symm.trans hPc
      obtain ⟨ins,hCode,_,hFires⟩ := EventFrame.estep_event_source he
      rw [hSite,Flow.code_1896] at hCode
      obtain rfl := Option.some.inj hCode.symm
      change Fires t.pc (electTmpl l g t (some 2306) 261 (.imm (-1))) ev (some v) at hFires
      have hMask : readBits l g t 32 (.imm (-1)) = .ok 4294967295#64 := rfl
      have hMember : electMember (4294967295#64).toNat (laneOf l g) := PTX.electMember_full l g
      simp only [electTmpl,hMask,ite_eq_left hMember] at hFires
      obtain ⟨_,leader,_,hRet⟩ := hFires
      have hNext := congrArg TState.pc (Option.some.inj hRet)
      change v.pc = t.pc + 1 at hNext
      have hFloor := afterIdleElection hTail (show 1897 ≤ v.pc by omega)
      omega
    · exact ih hu ev hMem hPc

private theorem electionAtWarpCursor {l : Launch} {X : Execution} {g shuffles votes : Nat}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1896 (fun _ => idleQCarry l) shuffles votes ends)
    {lane : Nat} (hl : lane < 32) (hMore : cur.pos lane < (X.tr (warpLane l g lane)).length) :
    ∃ inst leader, X.Elect (warpLane l g lane,cur.pos lane) 1896 4294967295 inst leader ∧
      Run kernel Assumptions.all l (warpLane l g lane) {}
        ((X.tr (warpLane l g lane)).take (cur.pos lane+1))
        (some (idleElectionReturn l (warpLane l g lane) (cur.state lane) leader)) ∧
      Run kernel Assumptions.all l (warpLane l g lane)
        (idleElectionReturn l (warpLane l g lane) (cur.state lane) leader)
        ((X.tr (warpLane l g lane)).drop (cur.pos lane+1)) (ends lane) := by
  let g' := warpLane l g lane
  let post := idleElectionReturn l g' (cur.state lane)
  have hn : Next kernel Assumptions.all l g' (cur.before lane) (cur.state lane)
      (.elect (2 ^ 32 - 1) post) :=
    ⟨cur.localSteps lane hl,idleElectionOut (cur.checkpoint lane hl)⟩
  obtain ⟨_,_,he,⟨inst,leader,rfl,hRet⟩,hRun⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,_,_,h⟩; cases h) (cur.continuation lane hl)
    (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  refine ⟨inst,leader,?_,?_,hRun⟩
  · change X.get (g',cur.pos lane) = some ⟨1896,.elect 4294967295 inst leader⟩
    rw [(cur.checkpoint lane hl).1] at he
    exact he
  · rw [List.take_succ_eq_append_getElem hMore, (List.getElem?_eq_some_iff.mp he).2]
    exact (cur.recorded lane hl).snoc hn.steps ⟨_,hn.stop,inst,leader,rfl,rfl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

/-- If the idle query loader reaches its final election, every lane records it. -/
private theorem idleElectionOccursAtOrdinal {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1896 (fun _ => idleQCarry l) shuffles votes ends) :
    ∀ lane < 32, cur.pos lane < (X.tr (warpLane l g lane)).length := by
  intro lane hl
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame (q : Nat) (hq : q < 32) : SameWarp l g (thread q) :=
    (Step.sameWarp_lane hBlock hg hq).1
  by_contra! hFull
  have hLen := Nat.le_antisymm (cur.bounded lane hl) hFull
  have hAll (q : Nat) (hq : q < 32) : cur.pos q = (X.tr (thread q)).length := by
    apply Nat.le_antisymm (cur.bounded q hq)
    by_contra! hMore
    obtain ⟨inst,leader,he,_,_⟩ := electionAtWarpCursor cur hq hMore
    have hPeers := Step.sameWarp_trans (sameWarp_symm (hSame q hq)) (hSame lane hl)
    obtain ⟨j,pc,site,mask,mask',tag,a,b,hOld,hPeer⟩ :=
      ElectOrd.partner hMax.1 hPeers he (PTX.electMember_full l (thread lane))
    have hSite := (hMax.1.elect.2.1 _ _ _ _ _ _ _ _ _ hOld hPeer hPeers).1
    have hPc := congrArg Event.pc (Option.some.inj (he.symm.trans hOld))
    have hJ : j < cur.pos lane := by rw [hLen]; exact len_of_get hPeer
    have hGet : ((X.tr (thread lane)).take (cur.pos lane))[j]? =
        some ⟨site,.elect mask' tag b⟩ := by rwa [List.getElem?_take_of_lt hJ]
    have hTrace := (cur.recorded lane hl).returning_reach.append
      (TraceReach.of_local (cur.localSteps lane hl))
    have hMem := List.mem_of_getElem? hGet
    have hNo := noEarlierIdleElection hTrace (cur.checkpoint lane hl).1.le
      ⟨site,.elect mask' tag b⟩ (List.mem_append_left [] hMem)
    exact hNo (hSite.symm.trans hPc.symm)
  obtain ⟨leader,hLeader,hDet⟩ :=
    Step.exists_leader hMax.1 (g := g) (PTX.electMember_full l g)
  apply hMax.not_grows
  refine Step.elect_counted_extension (pc := 1896) hMax.1 hg
    (fun lane hMem => ⟨_,Step.sameWarp_lane hBlock hg hMem.1⟩)
    (fun h _ => PTX.electMember_full l h) hLeader hDet ?_ ?_ ?_ ?_
  · intro h hh
    let k := laneOf l h
    have hk : k < 32 := Nat.mod_lt _ (by decide)
    have hEq : thread k = h := Step.warpLane_of_sameWarp hh
    apply Or.inl
    intro hNil
    have hL := hAll k hk
    rw [hEq,hNil,List.length_nil] at hL
    exact (Nat.ne_of_gt (cur.positive k hk)) hL
  · intro h hh
    let k := laneOf l h
    have hk : k < 32 := Nat.mod_lt _ (by decide)
    have hEq : thread k = h := Step.warpLane_of_sameWarp hh
    exact hEq ▸ cur.released k hk (hAll k hk)
  · intro h hh inst
    let k := laneOf l h
    have hk : k < 32 := Nat.mod_lt _ (by decide)
    have hEq : thread k = h := Step.warpLane_of_sameWarp hh
    rw [← hEq]
    have hRun := cur.recorded k hk
    rw [List.take_of_length_le (hAll k hk).ge] at hRun
    exact ⟨cur.before k,cur.state k,_,hRun,cur.localSteps k hk,
      ⟨_,idleElectionOut (cur.checkpoint k hk),inst,leader,
        by rw [(cur.checkpoint k hk).1]; rfl,rfl⟩⟩
  · intro inst
    exact Assumptions.wfStep.quiet hMax.1 le_appendLanes rfl (noNewRead_appendLanes fun _ => by rfl)

private theorem notifyOfMaximal {g j : Nat} (hg : g < l.threads) {t w : TState} {o : Option TState}
    (hPositive : 0 < j) (hBound : j ≤ (X.tr g).length)
    (hReleased : j = (X.tr g).length → Step.Released l X g)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop j) o)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t w)
    (hAt : At w 1899 (idleQCarry l)) :
    ∃ u, X.get (g,j) = some (idleQArrive l g) ∧ At u 1901 (idleQCarry l) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+1)) o := by
  obtain ⟨s,u,hPc,hu,hr⟩ := idleNotifyNext hp hAt
  let addr : Loc := ⟨.shared,g/l.block,l.sharedBase+8⟩
  let event := Event.mk s.pc (.arrive addr 32768 1 true .cta)
  have hl := hLocal.trans hr.steps
  have he : EStep kernel Assumptions.all l g s event (some u) := ⟨_,hr.stop,rfl,rfl⟩
  have hMore : j < (X.tr g).length := by
    by_contra! hLe
    have hEq := Nat.le_antisymm hBound hLe
    have hStarted : X.tr g ≠ [] := fun h => by rw [h,List.length_nil] at hEq; omega
    rw [List.take_of_length_le hLe] at hPrefix
    apply hMax.not_grows
    refine Step.object_counted_extension_silent hMax.1 (by trivial) hg (.inl hStarted)
      (hReleased hEq) hPrefix hl he ⟨trivial,fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := addr) (act := .arrive 1 32768)
      (fun _ _ h => by cases h) ?_ ?_
    · intro loc
      by_cases h : loc = addr
      · subst loc
        simp [objectAction,snoc_get_new,event]
      · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hMax.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  have hn : Next kernel Assumptions.all l g t s (.arrive addr 32768 u 1 true .cta) :=
    ⟨hl,hr.stop⟩
  obtain ⟨_,_,hGet,⟨rfl,hRet⟩,hRest⟩ := hn.continuing_at_nonempty (pos := j)
    (by rintro _ ⟨_,h⟩; cases h) hTail
    (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  refine ⟨_,by rw [idleQArrive,← hPc]; exact hGet,hu,?_,hRest⟩
  rw [List.take_succ_eq_append_getElem hMore,(List.getElem?_eq_some_iff.mp hGet).2]
  exact hPrefix.snoc hl he

/-- The query loader elects one arrival lane and every lane reaches its actual exit. -/
theorem queryLoaderExitOfDrained {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1896 (fun _ => idleQCarry l) shuffles votes ends) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  let j := cur.pos lane+1
  let v := cur.state lane
  obtain ⟨inst,leader,he,hPrefix,hTail⟩ :=
    electionAtWarpCursor cur hl (idleElectionOccursAtOrdinal hp hMax hg cur lane hl)
  have hElect : X.Elect (g,cur.pos lane) 1896 4294967295 inst leader := by
    simpa only [hSelf] using he
  have hBound : j ≤ (X.tr g).length := len_of_get hElect
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take j)
      (some (idleElectionReturn l g v leader)) := by
    simpa only [hSelf,j,v] using hPrefix
  have hRun : Run kernel Assumptions.all l g (idleElectionReturn l g v leader)
      ((X.tr g).drop j) (ends lane) := by
    simpa only [hSelf,j,v] using hTail
  have hRelease : j = (X.tr g).length → Step.Released l X g := by
    intro hLen
    constructor
    intro pc kind hLast _
    have hPos : (X.tr g).length-1 = cur.pos lane := by dsimp [j] at hLen; omega
    rw [hPos]
    exact elect_ready hMax.1 hElect
  obtain ⟨w,hw,hW⟩ := idleAfterElection (l := l) (g := g) (leader := leader)
    (cur.checkpoint lane hl)
  have hPos : 0 < j := Nat.succ_pos _
  by_cases hLeader : lane = leader
  · have hL : laneOf l g = leader := hLeader
    have hAt : At w 1899 (idleQCarry l) := by simpa only [ite_eq_left hL] using hW
    obtain ⟨u,hGet,hu,hPast',hRun'⟩ :=
      notifyOfMaximal hp hMax hg hPos hBound hRelease hPast hRun hw hAt
    obtain ⟨s,_,hNext⟩ := loaderRoleExit (g := g) 0 hu
    exact ⟨j+1,_,Thread.exitAtMaximalCursor hMax hg (Nat.succ_pos _) (len_of_get hGet)
      hPast' hRun' hNext (releasedIfLast hGet (by intro h; cases h)),rfl⟩
  · have hL : laneOf l g ≠ leader := hLeader
    have hAt : At w 1901 (idleQCarry l) := by simpa only [ite_eq_right hL] using hW
    obtain ⟨s,_,hn⟩ := loaderRoleExit (g := g) 0 hAt
    have hn' : Next kernel Assumptions.all l g (idleElectionReturn l g v leader) s .exit :=
      ⟨hw.trans hn.steps,hn.stop⟩
    exact ⟨j,_,Thread.exitAtMaximalCursor hMax hg hPos hBound hPast hRun hn' hRelease,rfl⟩

private theorem idleExitFromCacheDrain {g shuffles : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hReady : IdleDrainReady l X (g / l.block))
    {ends : Nat → Option TState}
    (cache : SchedulerWarpReached l X g 1891 (fun _ => idleDrainCarry l (warpIndex l g))
      shuffles 0 ends) : ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  by_cases hQ : warpIndex l g = 14
  · rw [hQ] at cache
    obtain ⟨query⟩ := idleQueryDrainedAtOrdinal hp hMax hg hReady cache
    exact queryLoaderExitOfDrained hp hMax hg query
  · have hV : warpIndex l g = 15 := by have := warpIndex_lt hp g; omega
    rw [hV] at cache
    exact idleWarp15ExitsAtOrdinal hMax hg cache

/-- The two idle loader roles exit after their complete search and release drain. -/
theorem idleLoaderExitForBatchesOfPhaseZero {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hReady : IdleDrainReady l X (g/l.block)) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  obtain ⟨_,_,⟨cache⟩⟩ := idleCacheDrainedForBatchesOfMaximal hp hMax hg hw hCuQ
    hIdle hReady
  exact idleExitFromCacheDrain hp hMax hg hw hReady cache

end
end PTX.Kernels.TmlFa4Fwd.Loader

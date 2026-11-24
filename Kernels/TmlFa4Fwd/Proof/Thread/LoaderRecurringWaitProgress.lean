-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.LoaderReadyCycle

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.MBarrier PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (kvUseStage kvEmptyPhase recurringBarrierFacts recurringEmptyWait recurringEmptyWaitCode
    recurringPacketSite copyArrivalAddress emptySlot_address loaderWarpWaitOfBlockedPhaseTrace)

def cacheEmptyParity (use : Nat) : Nat := if kvEmptyPhase use then 1 else 0

/-- The slot's current generation has passed the incoming reuse parity. -/
def CacheEmptyReady (l : Launch) (X : Execution) (g use : Nat) : Prop :=
  let log := X.objects (emptyObject l g (kvUseStage use))
  ∃ current, stateBefore log log.length = some current ∧ current.phase%2 ≠ cacheEmptyParity use

abbrev RecurringCacheGate (l : Launch) (X : Execution) (g : Nat) (site : Fin 4)
    (use : Nat) (F : Nat → List (Nat × Value)) (shuffles votes : Nat)
    (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g (recurringEmptyWait site).pc
    (fun lane => recurringBarrierFacts l site (kvUseStage use) (cacheEmptyParity use) ++ F lane)
    shuffles votes ends

abbrev RecurringCacheAcquired (l : Launch) (X : Execution) (g : Nat) (site : Fin 4)
    (use : Nat) (F : Nat → List (Nat × Value)) (shuffles votes : Nat)
    (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g ((recurringEmptyWait site).pc+3)
    (fun lane => recurringBarrierFacts l site (kvUseStage use) (cacheEmptyParity use) ++ F lane)
    shuffles votes ends

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g use shuffles votes : Nat} (hg : g < l.threads)
    (site : Fin 4) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : RecurringCacheGate l X g site use F shuffles votes ends)
    (hFresh : ∀ lane < 32, (recurringEmptyWait site).result ∉ (F lane).map Prod.fst)
include hp hMax hg site cur hFresh

/-- The next warm or steady packet consumes its actual successful empty acquire once the
protocol supplies the released generation. The ready-address operands survive the poll. -/
theorem RecurringCacheGate.acquirePreservingLocalOfBlockedMaximal
    (hReady : ∀ lane < 32,
      (∀ j ≥ cur.pos lane, ∀ loc, ¬ X.AsyncArrive (warpLane l g lane,j) loc true) →
        CacheEmptyReady l X g use) :
    ∃ done : RecurringCacheAcquired l X g site use F shuffles votes ends,
      ∀ lane < 32, (∃ index, cur.pos lane ≤ index ∧
        index+1 = done.pos lane ∧
        EmptyAcquire l X (warpLane l g lane,index) (kvUseStage use) (cacheEmptyParity use)) ∧
        ∀ i, cur.pos lane ≤ i → i < done.pos lane →
          ∀ a, ¬ X.Access (warpLane l g lane,i) a true := by
  let slot := kvUseStage use
  let phase := cacheEmptyParity use
  let addr := l.sharedBase+8*slot.val+56
  have hRange : 174 ≤ (recurringEmptyWait site).pc ∧
      (recurringEmptyWait site).pc+3 < 1906 := by fin_cases site <;> decide
  have hAddr : addr < 2^32 := by have := hp.shared.2.1; have := slot.isLt; dsimp [addr]; omega
  have hAlign : addr%8 = 0 := by have := hp.shared.1; dsimp [addr]; omega
  have hPhase : phase < 2 := by dsimp only [phase,cacheEmptyParity]; split <;> decide
  have hLoc (tid : Nat) : emptyObject l tid slot = ⟨.shared,tid/l.block,addr⟩ := by
    simpa only [addr,emptyObject] using emptySlot_address l (tid/l.block) slot
  have hNo : ∀ pair ∈ recurringBarrierFacts l site slot phase,
      pair.1 ≠ (recurringEmptyWait site).result := by
    fin_cases site <;> simp [recurringBarrierFacts,recurringEmptyWait,recurringPacketSite,
      copyArrivalAddress]
  obtain ⟨done,hTrace⟩ := loaderWarpWaitOfBlockedPhaseTrace
    hMax hg (by rw [hp.block]) (recurringEmptyWaitCode site) hRange hAddr hAlign hPhase cur
    (by
      intro lane hl pair hm hEq
      rcases List.mem_append.mp hm with h | h
      · exact hNo pair h hEq
      · exact hFresh lane hl (hEq ▸ List.mem_map_of_mem h))
    (fun _ _ => List.mem_append_left _ (by simp [recurringBarrierFacts,addr,slot]))
    (fun _ _ => List.mem_append_left _ (by simp [recurringBarrierFacts,phase]))
    (fun lane hl {_ _} _ _ _ failed => by
      have hQuiet : ∀ j ≥ cur.pos lane, ∀ target,
          ¬ X.AsyncArrive (warpLane l g lane,j) target true := by
        intro j hJ target hIssue
        obtain ⟨pc,he⟩ := hIssue
        have hx :
            ⟨pc,.asyncArrive target true⟩ ∈ (X.tr (warpLane l g lane)).drop (cur.pos lane) := by
          apply List.mem_of_getElem? (i := j-cur.pos lane)
          rw [List.getElem?_drop,Nat.add_sub_of_le hJ]
          exact he
        cases congrArg Event.kind (failed _ hx)
      obtain ⟨current,hState,hPhase'⟩ := hReady lane hl hQuiet
      rw [hLoc g] at hState
      exact ⟨current,hState,by rwa [Nat.mod_eq_of_lt hPhase]⟩)
  refine ⟨done,fun lane hl => ?_⟩
  obtain ⟨n,hP,hTr⟩ := hTrace lane hl
  let t := warpLane l g lane
  let index := cur.pos lane+n
  let event : Event :=
    ⟨(recurringEmptyWait site).pc,.wait ⟨.shared,t/l.block,addr⟩ phase true true .cta⟩
  have hRead : X.get (t,index) = some event := by
    have hx := congrArg (fun es : List Event => es[n]?) hTr
    rw [List.getElem?_drop,List.getElem?_append_right (by simp),
      List.length_replicate,Nat.sub_self] at hx
    exact hx
  refine ⟨⟨index,Nat.le_add_right ..,hP.symm,event,hRead,by rw [hLoc t]⟩,?_⟩
  intro i hLo hHi a hAccess
  have hNoWrite {pc : Nat} {kind : Kind} (he : X.get (t,i) = some ⟨pc,kind⟩)
      (hBad : ∀ v, kind ≠ .wait ⟨.shared,t/l.block,addr⟩ phase v true .cta) : False := by
    have hx : ((X.tr t).drop (cur.pos lane))[i-cur.pos lane]? = some ⟨pc,kind⟩ := by
      rwa [List.getElem?_drop,Nat.add_sub_of_le hLo]
    rw [hTr] at hx
    by_cases hFirst : i-cur.pos lane < n
    · rw [List.getElem?_append_left (by simpa using hFirst),
        List.getElem?_replicate,ite_eq_left hFirst] at hx
      exact hBad false (congrArg Event.kind (Option.some.inj hx).symm)
    · have hEq : i-cur.pos lane = n := by omega
      rw [hEq,List.getElem?_append_right (by simp),List.length_replicate,Nat.sub_self] at hx
      exact hBad true (congrArg Event.kind (Option.some.inj hx).symm)
  rcases hAccess with ⟨_,_,h⟩ | ⟨_,⟨pc,h⟩,_⟩ | ⟨_,_,pc,h⟩
  · cases h
  · exact hNoWrite h (by intro v he; cases he)
  · exact hNoWrite h (by intro v he; cases he)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

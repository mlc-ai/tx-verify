-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRingDrain
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderIdleElection
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue MBarrier Prologue
open PTX.Kernels.TmlFa4Fwd.Loader
  (terminalLoaderFrame idleQCarry queryDrainReadyWithPhase loaderWarpWaitOfOppositePhaseTrace
    drainWaitCode drainWaitSite valueLoaderExitOfDrained queryLoaderExitOfDrained)

/-- The query ring is ready for the terminal drain when its second slot has
entered the generation opposite to the loader's indicated parity. -/
def QueryDrainReady (l : Launch) (X : Execution) (g phase : Nat) : Prop :=
  let log := X.objects ⟨.shared,g/l.block,l.sharedBase+24⟩
  ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2

private theorem queryDrainOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes phase : Nat} (hg : g < l.threads) (hPhase : phase < 2)
    (hReady : QueryDrainReady l X g phase) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1891 (fun _ => terminalLoaderFrame l 14 phase)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1896 (fun _ => idleQCarry l) shuffles votes ends) := by
  obtain ⟨start⟩ := cur.advanceLocal (pc' := 1893)
    (G := fun _ => (2305,b32 (l.sharedBase+24)) :: (7192,b32 phase) :: idleQCarry l) (by
      intro lane hl
      obtain ⟨u,hu,hAt⟩ := queryDrainReadyWithPhase hp (cur.checkpoint lane hl)
      exact ⟨u,run_rtg hu,hAt⟩)
  obtain ⟨s,hs,hPhaseReady⟩ := hReady
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSize : l.sharedBase+24 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+24) % 8 = 0 := by have := hp.shared.1; omega
  obtain ⟨done,_⟩ := loaderWarpWaitOfOppositePhaseTrace hMax hg hBlock (drainWaitCode 3)
    (by decide) hSize hAlign hPhase start
    (by simp [drainWaitSite,idleQCarry]) (by simp [drainWaitSite]) (by simp [drainWaitSite])
    (fun _ _ {_ _} _ _ _ => ⟨s,hs,hPhaseReady⟩)
  exact done.advanceLocal (fun lane hl =>
    ⟨_,.refl,(done.checkpoint lane hl).mono (done.checkpoint lane hl).2.2.2.2.2.2⟩)

/-- At the final scheduler checkpoint, the actual cache and query release
generations allow both loader roles to complete their recorded suffixes. -/
theorem activeLoaderExitOfDrainReached {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use phase shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hPhase : phase < 2) (hCache : CacheDrainReady l X g use)
    (hQuery : warpIndex l g = 14 → QueryDrainReady l X g phase) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1863
      (fun _ => drainCarry l use ++ (terminalLoaderFrame l (warpIndex l g) phase).tail)
      shuffles votes ends) :
    Thread.Exited X g := by
  obtain ⟨cache⟩ := cacheDrainOfMaximal hp hMax hg hCache cur (by
    intro lane _ pair hm
    simp only [terminalLoaderFrame,List.tail_cons,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp)
  have cache' : SchedulerWarpReached l X g 1891
      (fun _ => terminalLoaderFrame l (warpIndex l g) phase) shuffles votes ends := cache
  by_cases hKey : warpIndex l g = 14
  · rw [hKey] at cache'
    obtain ⟨query⟩ := queryDrainOfMaximal hp hMax hg hPhase (hQuery hKey) cache'
    exact queryLoaderExitOfDrained hp hMax hg query
  · have hValue : warpIndex l g = 15 := by have := warpIndex_lt hp g; omega
    rw [hValue] at cache'
    exact valueLoaderExitOfDrained hMax hg cache'

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

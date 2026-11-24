-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.MmaPoll

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Epilogue Prologue

/-- Every lane consumes its actual successful MMA poll without changing either warp ordinal. -/
theorem mmaWarpPollOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g addr phase shuffles votes : Nat} (hg : g < l.threads) (site : Fin 14)
    (hAddr : addr < 2^32) (hAlign : addr%8 = 0) (hPhase : phase < 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (waitSite site).pc F shuffles votes ends)
    (hOperands : ∀ lane < 32, (∀ pair ∈ F lane, pair.1 ≠ (waitSite site).result) ∧
      ((waitSite site).base,b32 addr) ∈ F lane ∧ ((waitSite site).phase,b32 phase) ∈ F lane)
    (hReady : ∀ lane < 32, ∀ {t u},
      Run kernel Assumptions.all l (warpLane l g lane) {} (X.tr (warpLane l g lane)) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u →
      At u (waitSite site).pc (F lane) →
      let log := X.objects ⟨.shared, g/l.block, addr⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) :
    ∃ next : SchedulerWarpReached l X g ((waitSite site).pc+3) F shuffles votes ends,
      ∀ lane < 32, cur.pos lane < next.pos lane ∧
        X.get (warpLane l g lane,next.pos lane-1) =
          some ⟨(waitSite site).pc,.wait ⟨.shared,g/l.block,addr⟩ phase true true .cta⟩ := by
  classical
  let thread := warpLane l g
  let ev (ok : Bool) : Event :=
    ⟨(waitSite site).pc,.wait ⟨.shared,g/l.block,addr⟩ phase ok true .cta⟩
  let _ : Nonempty TState := ⟨cur.state 0⟩
  have hEach (lane : Nat) (hl : lane < 32) : ∃ n before state,
      X.get (thread lane,cur.pos lane+n) = some (ev true) ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (cur.pos lane+n+1)) (some before) ∧
      Run kernel Assumptions.all l (thread lane) before
        ((X.tr (thread lane)).drop (cur.pos lane+n+1)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before state ∧
      At state ((waitSite site).pc+3) (F lane) ∧
      (X.tr (thread lane)).drop (cur.pos lane) =
        List.replicate n (ev false) ++
          (ev true :: (X.tr (thread lane)).drop (cur.pos lane+n+1)) := by
    have hs := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
    have hCta : (warpLane l g lane)/l.block = g/l.block := hs.1.2.2.symm
    obtain ⟨hFresh,hBase,hPar⟩ := hOperands lane hl
    have hh := waitOfMaximalWithTrace hMax (g := warpLane l g lane) hs.1.2.1
      site hAddr hAlign hPhase hFresh hBase hPar (fun hRun hLocal hAt => by
        rw [hCta]
        exact hReady lane hl hRun hLocal hAt)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.continuation lane hl) (cur.localSteps lane hl)
    simpa only [hCta,ev] using hh
  choose! n before state hGet hPrefix hRun hLocal hAt hCut using hEach
  let pos := fun lane => cur.pos lane+n lane+1
  have hOrd : WarpOrdinals l X g pos shuffles votes := by
    have keep (test : Event → Bool) (ordinal : Nat)
        (hc : ∀ lane < 32, ((X.tr (thread lane)).take (cur.pos lane)).countP test = ordinal)
        (hf : test (ev false) = false) (ht : test (ev true) = false) :
        ∀ lane < 32, ((X.tr (thread lane)).take (pos lane)).countP test = ordinal := by
      intro lane hl
      let es := List.replicate (n lane) (ev false) ++ [ev true]
      have hLen : es.length = n lane+1 := by simp [es]
      have hEs : (X.tr (thread lane)).drop (cur.pos lane) =
          es ++ (X.tr (thread lane)).drop (pos lane) := by
        rw [hCut lane hl]
        simp [es,pos]
      have hNone : es.countP test = 0 := by simp [es,hf,ht]
      change ((X.tr (thread lane)).take (cur.pos lane+n lane+1)).countP test = ordinal
      rw [Nat.add_assoc,List.take_add,hEs,← hLen,List.take_append_length,List.countP_append,
        hNone,Nat.add_zero]
      exact hc lane hl
    exact ⟨keep _ _ cur.ordinals.shfl rfl rfl,keep _ _ cur.ordinals.vote rfl rfl⟩
  refine ⟨⟨⟨pos,before,state,hOrd,hRun,hLocal,hAt⟩,fun _ _ => Nat.succ_pos _,
    fun lane hl => len_of_get (hGet lane hl),?_,hPrefix⟩,?_⟩
  · intro lane hl hLast
    constructor
    intro pc kind hEvent _
    have hIdx : (X.tr (thread lane)).length-1 = cur.pos lane+n lane := by
      rw [← hLast]
      rfl
    rw [hIdx,hGet lane hl] at hEvent
    cases hEvent
    rw [hIdx]
    exact Step.ready_of_wait (hGet lane hl)
  · intro lane hl
    exact ⟨by dsimp [pos]; omega,by simpa only [pos,Nat.add_sub_cancel] using hGet lane hl⟩

end PTX.Kernels.TmlFa4Fwd.Mma

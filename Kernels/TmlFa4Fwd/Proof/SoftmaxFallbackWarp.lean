-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackRead
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerOptionalRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

namespace Epilogue

/-- Align a common shuffle after lane-dependent reads. The reads advance only the lanes that
execute them and leave the collective ordinals unchanged. -/
theorem SchedulerWarpAt.optionalReadBeforeShuffleRecorded {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pc readPc shflPc shuffles votes : Nat} (hg : g < l.threads)
    {F G : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g pc F shuffles votes ends)
    (fires : Nat → Prop) [DecidablePred fires] (acc : Nat → Acc) (bs : Nat → List (Option Byte))
    (hLane : ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) ≠ [] →
      ∃ before state, At state shflPc (G lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) before state ∧
        Run kernel Assumptions.all l (warpLane l g lane) before
          ((X.tr (warpLane l g lane)).drop (if fires lane then cur.pos lane + 1 else cur.pos lane))
          (ends lane) ∧
        (fires lane → X.get (warpLane l g lane, cur.pos lane) =
          some ⟨readPc, .rd (acc lane) (bs lane)⟩))
    {mode : ShflMode} {a : Nat → Value} {b c dst : Nat}
    (hOut : ∀ lane < 32, ∀ s, At s shflPc (G lane) →
      out kernel Assumptions.all l (warpLane l g lane) s =
        .ev (.shfl mode (a lane) b c (fun v _ => next (setReg s dst v))))
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨
      WarpFollowsEvent l X g cur.pos src index target) (hTarget : readPc < target.pc) :
    ∃ u : SchedulerWarpAt l X g shflPc G shuffles votes ends,
      u.pos = (fun lane => if fires lane then cur.pos lane + 1 else cur.pos lane) ∧
      (∀ lane < 32, fires lane → X.get (warpLane l g lane, cur.pos lane) =
        some ⟨readPc, .rd (acc lane) (bs lane)⟩) ∧
      (WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g u.pos src index target) := by
  let thread := warpLane l g
  let pos := fun lane => if fires lane then cur.pos lane + 1 else cur.pos lane
  let read := fun lane => Event.mk readPc (.rd (acc lane) (bs lane))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hBefore (h : WarpFollowsEvent l X g cur.pos src index target)
      (hr : fires src → X.get (thread src, cur.pos src) = some (read src)) : pos src ≤ index := by
    by_cases hs : fires src
    · simp only [pos, ite_eq_left hs]
      rcases Nat.eq_or_lt_of_le h.before with heq | hlt
      · have he := hr hs
        rw [heq] at he
        have hPc := congrArg Event.pc (Option.some.inj (he.symm.trans h.get))
        change readPc = target.pc at hPc
        omega
      · exact hlt
    · simpa only [pos, ite_eq_right hs] using h.before
  have hCount (test : Event → Bool) (lane n : Nat)
      (hc : ((X.tr (thread lane)).take (cur.pos lane)).countP test = n)
      (ht : test (read lane) = false)
      (hr : fires lane → X.get (thread lane, cur.pos lane) = some (read lane)) :
      ((X.tr (thread lane)).take (pos lane)).countP test = n := by
    by_cases hf : fires lane
    · simp only [pos, ite_eq_left hf, List.take_add_one]
      rw [show (X.tr (thread lane))[cur.pos lane]? = _ from hr hf]
      simp [hc, ht]
    · simpa only [pos, ite_eq_right hf] using hc
  have hNonempty (lane : Nat) (hl : lane < 32) :
      (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with he | h
    · intro hNil
      have hr := cur.continuation lane hl
      rw [hNil, he lane hl] at hr
      cases hr
    · obtain ⟨s₀, s, hs, ht, hr, hRead⟩ := hLane src h.lane h.nonempty
      have hRemain : (X.tr (thread src)).drop (pos src) ≠ [] := by
        intro hNil
        exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp h.get).1
          ((List.drop_eq_nil_iff.mp hNil).trans (hBefore h hRead))
      have hn : Next kernel Assumptions.all l (thread src) s₀ s
          (.shfl mode (a src) b c (fun v _ => next (setReg s dst v))) :=
        ⟨ht, hOut src h.lane s hs⟩
      obtain ⟨_, _, he, hk, _⟩ := hn.shuffle_at_nonempty hr hRemain
        (hCount _ src _ (cur.ordinals.shfl src h.lane) rfl hRead)
      have hNoExit : ∀ j < cur.pos lane, ∀ pc, X.get (thread lane, j) ≠ some ⟨pc, .exit⟩ :=
        h.noExit lane hl
      exact cur.ordinals.shuffle_suffix_nonempty hX hBlock hg h.lane he hk hl hNoExit
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! before state hAt hLocal hRun hRead using fun lane hl => hLane lane hl (hNonempty lane hl)
  have hOrd : WarpOrdinals l X g pos shuffles votes :=
    ⟨fun lane hl => hCount _ lane _ (cur.ordinals.shfl lane hl) rfl (hRead lane hl),
      fun lane hl => hCount _ lane _ (cur.ordinals.vote lane hl) rfl (hRead lane hl)⟩
  let u : SchedulerWarpAt l X g shflPc G shuffles votes ends :=
    ⟨pos, before, state, hOrd, hRun, hLocal, hAt⟩
  refine ⟨u, rfl, hRead, fun h => h.after (hBefore h (hRead src h.lane)) ?_⟩
  intro lane hl j hj hj' pc
  by_cases hf : fires lane
  · have he := hRead lane hl hf
    change j < pos lane at hj
    simp only [pos, ite_eq_left hf] at hj
    exact noExitThroughContinuingEvent hX (Step.sameWarp_lane hBlock hg hl).1.1.2.1
      he (by intro heq; cases heq) hj pc
  · change j < pos lane at hj
    simp only [pos, ite_eq_right hf] at hj
    omega

end Epilogue
namespace Softmax

/-- The optional reads supply the exact down-shuffle word for the next request group. -/
def fallbackDownFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (first cutoff : Nat) : List (Nat × Value) :=
  let lane := laneOf l g
  let index := first + 31 + lane
  [(453, .pred (decide (lane = 31))), (7239, b32 (drainCuQ p index)), (1219, b32 index)] ++
    fallbackAdvanceFacts p l g warp first cutoff

private theorem fallbackDownOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first cutoff : Nat} {warp : Fin 8} {t : TState}
    (ht : At t 3171 (fallbackDownFacts p l g warp first cutoff)) :
    let word := b32 (drainCuQ p (first + 31 + laneOf l g))
    out kernel Assumptions.all l g t =
      .ev (.shfl .down word 1 31 (fun v _ => next (setReg t 2704 v))) := by
  dsimp only
  have hRead := ht.2.2.2.2.2.1
  have hb : l.block % 32 = 0 := by rw [hp.block]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_3171) rfl rfl]
  change Out.ev (shflTmpl l g t .down 2704 none (.reg 7239) (.imm 1) (.imm 31) (.imm (-1))) = _
  simp [shflTmpl, readValue, readReg, hRead, hb, Value.bytes, b32, readBits, pure, Except.pure]
  rfl

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g first cutoff shuffles votes : Nat}
    {warp : Fin 8} (hg : g < l.threads) (hGroup : first + 31 < p.batch)
    (hCuQ : CuQReadsFromLaunch p X) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3163 (fun lane =>
      fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends)
    {src eventIndex : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨
      WarpFollowsEvent l X g cur.pos src eventIndex target)
include hp hX hg hGroup hCuQ cur hProgress

/-- Consume the real lane-dependent reads and the warp's next common down shuffle. -/
theorem warpFallbackDownRecorded (hTarget : 3171 < target.pc) :
    let facts := fun lane => fallbackDownFacts p l (warpLane l g lane) warp first cutoff
    let word := fun lane => b32 (drainCuQ p (first + 31 + lane))
    ∃ u : SchedulerWarpAt l X g 3172
        (fun lane => (2704, word (shflSource .down lane 1 31).1) :: facts lane)
        (shuffles + 1) votes ends,
      u.pos = (fun lane => (if first + 31 + lane ≤ p.batch then cur.pos lane + 1
        else cur.pos lane) + 1) ∧
      (∀ lane < 32, first + 31 + lane ≤ p.batch → X.get (warpLane l g lane, cur.pos lane) =
        some ⟨3169, .rd (fallbackReadAcc p (first + 31 + lane)) ((word lane).toBytes.map some)⟩) ∧
      (WarpFollowsEvent l X g cur.pos src eventIndex target →
        WarpFollowsEvent l X g u.pos src eventIndex target) := by
  dsimp only
  let t := warpLane l g
  let ix := fun lane => first + 31 + lane
  let word := fun lane => b32 (drainCuQ p (ix lane))
  let facts := fun lane => fallbackDownFacts p l (t lane) warp first cutoff
  let doesRead := fun lane => ix lane ≤ p.batch
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  obtain ⟨down, hDownPos, hRead, hd⟩ := cur.optionalReadBeforeShuffleRecorded hp hX hg
    (shflPc := 3171) (G := facts) (fires := doesRead)
    (acc := fun lane => fallbackReadAcc p (ix lane))
    (bs := fun lane => (word lane).toBytes.map some)
    (readPc := 3169) (mode := .down) (a := word) (b := 1) (c := 31) (dst := 2704)
    (by
      intro lane hl hn
      have ht := cur.checkpoint lane hl
      have hr := (cur.continuation lane hl).after_local_nonempty (cur.localSteps lane hl) hn
      obtain ⟨s, hS, hRead, hTail⟩ := fallbackLaneRead hp hGroup ht hr hn hCuQ
      obtain ⟨u, hu, hU⟩ := fallbackLaneDown (l := l) (g := warpLane l g lane)
        (by simp [fallbackAdvanceFacts, fallbackBaseFrame, Mma.groupScanFacts, Mma.scanSite])
        (by set_option maxRecDepth 100000 in kernel_rfl) hS
      refine ⟨s, u, hU, run_rtg hu, ?_, ?_⟩
      · simpa only [hLane lane hl, doesRead, ix] using hTail
      · simpa only [hLane lane hl, doesRead, ix, word] using hRead)
    (by
      intro lane hl s hs
      simpa only [hLane lane hl, ix, word] using fallbackDownOut hp (g := warpLane l g lane) hs)
    hProgress (by omega)
  have hFresh : ∀ lane < 32, ∀ x ∈ facts lane, x.1 ≠ 2704 := by
    intro lane hl
    exact of_decide_eq_true rfl
  have hOut := fun lane hl => by
    have h := fallbackDownOut hp (g := warpLane l g lane) (down.checkpoint lane hl)
    simpa only [hLane lane hl, ix, word] using h
  obtain ⟨u, hPos, _, hu⟩ :=
    down.consumeShuffleToRecorded hp hX hg .down word (fun _ => 1) (fun _ => 31)
    hFresh hOut (hProgress.imp_right hd) hTarget
  exact ⟨u, by rw [hPos, hDownPos], hRead, hu ∘ hd⟩

theorem warpFallbackDown (hTarget : 3171 < target.pc) :
    let facts := fun lane => fallbackDownFacts p l (warpLane l g lane) warp first cutoff
    let word := fun lane => b32 (drainCuQ p (first + 31 + lane))
    ∃ u : SchedulerWarpAt l X g 3172
        (fun lane => (2704, word (shflSource .down lane 1 31).1) :: facts lane)
        (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src eventIndex target →
        WarpFollowsEvent l X g u.pos src eventIndex target := by
  obtain ⟨u, _, _, hFollow⟩ := warpFallbackDownRecorded hp hX hg hGroup hCuQ cur hProgress hTarget
  exact ⟨u, hFollow⟩
end

/-- The maximal softmax warp reaches the neighbor-offset exchange for the next group. -/
theorem warpFallbackDownOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first cutoff shuffles votes : Nat} {warp : Fin 8} (hg : g < l.threads)
    (hGroup : first + 31 < p.batch)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3163 (fun lane =>
      fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends) :
    let facts := fun lane => fallbackDownFacts p l (warpLane l g lane) warp first cutoff
    let word := fun lane => b32 (drainCuQ p (first + 31 + lane))
    Nonempty (SchedulerWarpReached l X g 3172
      (fun lane => (2704, word (shflSource .down lane 1 31).1) :: facts lane)
      (shuffles + 1) votes ends) := by
  dsimp only
  let thread := warpLane l g
  let ix := fun lane => first + 31 + lane
  let word := fun lane => b32 (drainCuQ p (ix lane))
  let facts := fun lane => fallbackDownFacts p l (thread lane) warp first cutoff
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  obtain ⟨down⟩ := cur.afterOptionalRead (nextSite := 3171) (readSite := 3169) (G := facts)
    (fun lane => ix lane ≤ p.batch) (fun lane => fallbackReadAcc p (ix lane))
    (fun lane => (word lane).toBytes.map some) (by
      intro lane hl
      let c := cur.checkpoint lane hl
      have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
      obtain ⟨s, t, hBound, hRelease, hAt, hPast, hLocal, hTail, hRead⟩ :=
        fallbackLaneReadOfMaximal hp hMax hThread hGroup hProtected c
          (cur.recorded lane hl) (cur.localSteps lane hl) (cur.continuation lane hl)
          (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
      obtain ⟨u, hu, hU⟩ := fallbackLaneDown (l := l) (g := thread lane)
        (by simp [thread, warpLane, fallbackAdvanceFacts, fallbackBaseFrame,
          Mma.groupScanFacts, Mma.scanSite])
        (by set_option maxRecDepth 100000 in kernel_rfl) hAt
      have hLane' : laneOf l (g - laneOf l g + lane) = lane := hLane lane hl
      refine ⟨s, u, ?_, ?_, hU, ?_, hLocal.trans (run_rtg hu), ?_, ?_⟩
      · simpa only [ix, warpLane, hLane'] using hBound
      · simpa only [ix, warpLane, hLane'] using hRelease
      · simpa only [ix, warpLane, hLane'] using hPast
      · simpa only [ix, warpLane, hLane'] using hTail
      · simpa only [ix, word, warpLane, hLane'] using hRead)
  exact down.consumeShuffle (dst := 2704) hp hMax hg .down word (fun _ => 1) (fun _ => 31)
    (fun _ _ => of_decide_eq_true rfl)
    (fun lane hl => by
      simpa only [thread, word, ix, hLane lane hl] using
        fallbackDownOut hp (down.checkpoint lane hl))

end Softmax

end
end PTX.Kernels.TmlFa4Fwd

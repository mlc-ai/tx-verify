-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Kernels.TmlFa4Fwd.Proof.EpilogueFirstPassEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- The first scheduler position cannot be beyond a later event of the same lane. -/
private theorem firstCursorOfEvent (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 13) (hReads : CuQReadsFromLaunchOnThread p X g)
    {j : Nat} {e : Event} (he : X.get (g, j) = some e)
    (hDemand : 2776 < e.pc ∨ e.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl e = true) :
    let lane := laneOf l g
    let pos := if p.batch < lane then 6 else 7
    ∃ s o, At s 2777 ((7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
        schedulerStartupFrame p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) o ∧
      ((X.tr g).take pos).countP Execution.isShfl = 3 ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 ∧
      (X.tr g).drop pos ≠ [] ∧ pos ≤ j := by
  have hBefore := warp13StartupBeforeEvent hp hX hg hw he
    (hDemand.imp_left (fun h => by omega))
  have hIndex := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, o, hs, hr, hShfl, hVote, _, hAdvance⟩ :=
    firstSchedulerCursorPrefixOnThread hp hX g hg hw (hBefore.trans_lt hIndex) (hReads _)
  have hx := hAdvance j e he hDemand
  exact ⟨s, o, hs, hr, hShfl, hVote, fun hn =>
    Nat.not_le_of_lt hIndex ((List.drop_eq_nil_iff.mp hn).trans hx), hx⟩

private theorem firstShuffleOfCursor {g pos : Nat} {s : TState} {o : Option TState}
    (hs : At s 2777
      ((7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p (laneOf l g))) ::
        schedulerStartupFrame p l g)) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) o)
    (hCount : ((X.tr g).take pos).countP Execution.isShfl = 3) (hNext : (X.tr g).drop pos ≠ []) :
    ∃ recv ok, X.get (g, pos) =
        some ⟨2777, .shfl .down (b32 (firstSchedulerWord p (laneOf l g))) 1 31 recv ok⟩ ∧
      X.ShflK (g, pos) 3 := by
  let step := fun x (_ : Bool) => next (setReg s 2308 x)
  have hn : Next kernel Assumptions.all l g s s
      (.shfl .down (b32 (firstSchedulerWord p (laneOf l g))) 1 31 step) :=
    ⟨.refl, startupOut (.inr (.inr (by rw [hs.1]; decide)))
      (schedulerFirstShuffle hp g s _ hs.1 hs.2.2.2.1 hs.2.2.2.2.2.1)⟩
  obtain ⟨r, ok, he, hk, _⟩ := hn.shuffle_at_nonempty hr hNext hCount
  exact ⟨r, ok, hs.1 ▸ he, hk⟩

omit hp in
private theorem shfl_index_ge {X : Execution} {g j : Nat} (h : X.ShflK (g, j) 3) :
    3 ≤ j :=
  h.2.symm.le.trans ((List.countP_le_length ..).trans (List.length_take_le ..))

/-- A late event in one warp-13 lane forces the whole warp's first scheduler shuffle.
All cursors are taken from the observed prefixes, with arbitrary terminal states. -/
theorem warp13FirstShuffleOfLateEventInWarp (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 13) (hReads : CuQReadsFromLaunchInWarp p l X g)
    {src j : Nat} (hSrc : src < 32) {target : Event}
    (hTarget : X.get (warpLane l g src, j) = some target) (hPc : 2777 < target.pc) :
    let pos := fun lane => if p.batch < lane then 6 else 7
    ∃ (state : Nat → TState) (o : Nat → Option TState),
      WarpOrdinals l X g (fun lane => pos lane + 1) 4 0 ∧
      pos src + 1 ≤ j ∧
      ∀ lane < 32,
        let thread := warpLane l g lane
        let source := if lane + 1 < 32 then lane + 1 else lane
        X.ShflK (thread, pos lane) 3 ∧
        Run kernel Assumptions.all l thread (state lane) ((X.tr thread).drop (pos lane + 1))
          (o lane) ∧
        At (state lane) 2778
          ([(7228, b32 p.batch), (7217, b32 (firstSchedulerWord p lane)),
            (2308, b32 (firstSchedulerWord p source))] ++ schedulerStartupFrame p l thread) := by
  classical
  dsimp only
  let pos : Nat → Nat := fun lane => if p.batch < lane then 6 else 7
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWarp (lane : Nat) (hl : lane < 32) : SameWarp l g (thread lane) :=
    (Step.sameWarp_lane hBlock hg hl).1
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hThread (lane : Nat) (hl : lane < 32) : thread lane < l.threads := (hWarp lane hl).1.2.1
  have hIndex (lane : Nat) (hl : lane < 32) : warpIndex l (thread lane) = 13 :=
    (hWarp lane hl).2.symm.trans hw
  obtain ⟨s, o, hs, hr, hCount, _, hNext, hBefore⟩ :=
    firstCursorOfEvent hp hX (hThread src hSrc) (hIndex src hSrc) (hReads src hSrc) hTarget
      (.inl (by omega))
  obtain ⟨recv, ok, he, hk⟩ := firstShuffleOfCursor hp hs hr hCount hNext
  rw [hLane src hSrc] at he hk hBefore
  have hLater : pos src + 1 ≤ j := by
    change pos src ≤ j at hBefore
    by_contra h
    have hEq : pos src = j := by omega
    change (if p.batch < src then 6 else 7) = j at hEq
    rw [hEq] at he
    have hAt := congrArg Event.pc (Option.some.inj (he.symm.trans hTarget))
    exact (Nat.ne_of_lt hPc) hAt
  have hCursors (lane : Nat) (hl : lane < 32) :
      ∃ s o, At s 2777 ((7228, b32 p.batch) :: (7217, b32 (firstSchedulerWord p lane)) ::
          schedulerStartupFrame p l (thread lane)) ∧
        Run kernel Assumptions.all l (thread lane) s ((X.tr (thread lane)).drop (pos lane)) o ∧
        ((X.tr (thread lane)).take (pos lane)).countP Execution.isShfl = 3 ∧
        ((X.tr (thread lane)).take (pos lane)).countP isFullWarpVote = 0 ∧
        (X.tr (thread lane)).drop (pos lane) ≠ [] := by
    have hSame := Step.sameWarp_trans (sameWarp_symm (hWarp src hSrc)) (hWarp lane hl)
    have hPeer := Step.shfl_lane_of_ready hX he hk hSame
    have hDemand : ∃ (k : Nat) (e : Event), X.get (thread lane, k) = some e ∧
        (2776 < e.pc ∨ e.kind = .exit ∨ 3 ≤ k ∧ Execution.isShfl e = true) := by
      rcases hPeer with ⟨k, hPeerOrdinal⟩ | ⟨k, pc, he, _⟩
      · have hBefore := shfl_index_ge hPeerOrdinal
        obtain ⟨⟨pc, mode, val, b, c, res, check, he⟩, _⟩ := hPeerOrdinal
        exact ⟨k, ⟨pc, .shfl mode val b c res check⟩, he, .inr (.inr ⟨hBefore, rfl⟩)⟩
      · exact ⟨k, ⟨pc, .exit⟩, he, .inr (.inl rfl)⟩
    obtain ⟨k, e, he, hDemand⟩ := hDemand
    obtain ⟨s, o, hs, hr, hShfl, hVote, hNext, _⟩ := firstCursorOfEvent hp hX
      (hThread lane hl) (hIndex lane hl) (hReads lane hl) he hDemand
    rw [hLane lane hl] at hs hr hShfl hVote hNext
    exact ⟨s, o, hs, hr, hShfl, hVote, hNext⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! states ends hs hr hShfl hVote hNext using hCursors
  obtain ⟨state, hOrd, hRes⟩ := warp13FirstShuffleOfCursors hp hX hg ends (fun lane hl =>
    ⟨states lane, hs lane hl, hr lane hl, hShfl lane hl, hVote lane hl, hNext lane hl⟩)
  exact ⟨state, ends, hOrd, hLater, hRes⟩

/-- Apply the scoped proof when every CuQ read agrees with the launch. -/
theorem warp13FirstShuffleOfLateEvent (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 13) (hReads : CuQReadsFromLaunch p X) {src j : Nat}
    (hSrc : src < 32) {target : Event} (hTarget : X.get (warpLane l g src, j) = some target)
    (hPc : 2777 < target.pc) :
    let pos := fun lane => if p.batch < lane then 6 else 7
    ∃ (state : Nat → TState) (o : Nat → Option TState),
      WarpOrdinals l X g (fun lane => pos lane + 1) 4 0 ∧
      pos src + 1 ≤ j ∧
      ∀ lane < 32,
        let thread := warpLane l g lane
        let source := if lane + 1 < 32 then lane + 1 else lane
        X.ShflK (thread, pos lane) 3 ∧
        Run kernel Assumptions.all l thread (state lane) ((X.tr thread).drop (pos lane + 1))
          (o lane) ∧
        At (state lane) 2778
          ([(7228, b32 p.batch), (7217, b32 (firstSchedulerWord p lane)),
            (2308, b32 (firstSchedulerWord p source))] ++ schedulerStartupFrame p l thread) :=
  warp13FirstShuffleOfLateEventInWarp hp hX hg hw
    (hReads.inWarp g) hSrc hTarget hPc

/-- A late scheduler event forces the actual first scan and its common group cutoff. -/
theorem warp13FirstGroupCutoffOfLateEventInWarp (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13)
    (hReads : CuQReadsFromLaunchInWarp p l X g) {src index : Nat} (hSrc : src < 32) {target : Event}
    (hTarget : X.get (warpLane l g src, index) = some target) (hPc : 2816 < target.pc) :
    ∃ (ends : Nat → Option TState)
      (cur : FirstGroupCutoff p l Assumptions.all X g (g / l.block)
        (fun lane => schedulerStartupFrame p l (warpLane l g lane)) 10 0 ends),
      WarpFollowsEvent l X g cur.pos src index target := by
  let F := fun lane => schedulerStartupFrame p l (warpLane l g lane)
  let pos := fun lane => (if p.batch < lane then 6 else 7) + 1
  obtain ⟨state, ends, hOrdinal, hBefore, hCheckpoint⟩ :=
    warp13FirstShuffleOfLateEventInWarp hp hX hg hw hReads hSrc hTarget (by omega)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hBlockPos : 0 < l.block := by rw [hp.block]; decide
  have hCta : g / l.block < 2 ^ 31 :=
    lt_trans ((Nat.div_lt_iff_lt_mul hBlockPos).2 (show g < l.grid * l.block from hg)) hp.grid.2.2
  have hReg : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs := by
    intro lane _ pair hm
    simp only [F, schedulerStartupFrame, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [firstPassRegs, schedulerFrameRegs]
  have hCtaFact (lane : Nat) (hl : lane < 32) : (1072, b32 (g / l.block)) ∈ F lane := by
    have h := (Step.sameWarp_lane hBlock hg hl).1.1.2.2
    simp [F, schedulerStartupFrame, warpLane, h]
  have hModel (thread : Nat) {s : TState} (hlo : 2778 ≤ s.pc) (hhi : s.pc < 2820) :
      out kernel Assumptions.all l thread s = out kernel [] l thread s :=
    epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)
  have hOffset (lane : Nat) : firstSchedulerWord p lane = firstPassOffset p lane := by
    by_cases h : lane ≤ p.batch
    · simp [firstSchedulerWord, firstPassOffset, h, Nat.not_lt_of_ge h]
    · simp [firstSchedulerWord, firstPassOffset, h, Nat.lt_of_not_ge h]
  have hAt (lane : Nat) (hl : lane < 32) : At (state lane) 2778
      ([(1201, b32 lane), (7228, b32 p.batch), (7217, b32 (firstPassOffset p lane)),
        (2308, b32 (firstPassOffset p (if lane < 31 then lane + 1 else lane)))] ++ F lane) := by
    have ht := (hCheckpoint lane hl).2.2
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hLaneReg : (1201, b32 lane) ∈ F lane := by simp [F, schedulerStartupFrame, hLane]
    have hSource : (if lane + 1 < 32 then lane + 1 else lane) =
        if lane < 31 then lane + 1 else lane := by
      split <;> split <;> omega
    rw [hSource, hOffset, hOffset] at ht
    have hs := ht.2.2.2.2
    exact ht.mono ⟨holds_mem hs.2.2.2 hLaneReg, hs⟩
  obtain ⟨s0, hPos⟩ := firstPassStartAt hp hg hModel hReg hOrdinal
    (fun lane hl => (hCheckpoint lane hl).2.1) hAt
  have h0 : WarpFollowsEvent l X g s0.pos src index target := by
    change s0.pos = pos at hPos
    rw [hPos]
    refine ⟨hSrc, hTarget, hBefore, ?_⟩
    intro lane hl j hj pc
    obtain ⟨⟨_, _, _, _, _, _, _, he⟩, _⟩ := (hCheckpoint lane hl).1
    exact noExitThroughContinuingEvent hX (Step.sameWarp_lane hBlock hg hl).1.1.2.1
      he (by intro h; cases h) hj pc
  obtain ⟨s1, h1⟩ := s0.advanceTo hp hX hg (by decide) hModel hReg (.inr h0)
    (by change 2796 < target.pc; omega)
  obtain ⟨s2, h2⟩ := s1.advanceTo hp hX hg (by decide) hModel hReg (.inr (h1 h0))
    (by change 2800 < target.pc; omega)
  obtain ⟨s3, h3⟩ := s2.advanceTo hp hX hg (by decide) hModel hReg (.inr (h2 (h1 h0)))
    (by change 2804 < target.pc; omega)
  have hThree := h3 (h2 (h1 h0))
  obtain ⟨s4, h4⟩ := s3.advanceTo hp hX hg (by decide) hModel hReg (.inr hThree)
    (by change 2808 < target.pc; omega)
  obtain ⟨s5, h5⟩ := s4.advanceTo hp hX hg (by decide) hModel hReg (.inr (h4 hThree))
    (by change 2812 < target.pc; omega)
  have hFive := h5 (h4 hThree)
  obtain ⟨cutoff, hc⟩ :=
    s5.groupCutoffTo hp hX hg hCta hModel hReg hCtaFact (.inr hFive) hPc
  exact ⟨ends, cutoff, hc hFive⟩

/-- Apply the scoped proof when every CuQ read agrees with the launch. -/
theorem warp13FirstGroupCutoffOfLateEvent (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 13) (hReads : CuQReadsFromLaunch p X)
    {src index : Nat} (hSrc : src < 32) {target : Event}
    (hTarget : X.get (warpLane l g src, index) = some target) (hPc : 2816 < target.pc) :
    ∃ (ends : Nat → Option TState)
      (cur : FirstGroupCutoff p l Assumptions.all X g (g / l.block)
        (fun lane => schedulerStartupFrame p l (warpLane l g lane)) 10 0 ends),
      WarpFollowsEvent l X g cur.pos src index target :=
  warp13FirstGroupCutoffOfLateEventInWarp hp hX hg hw
    (hReads.inWarp g) hSrc hTarget hPc

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WfBarFinal

@[expose] public section

/-!
# `Remaining.barSteps` from the `time` facts of the barriers and the barrier-0 thread facts

A blocked `bar.sync` of the kernel is on barrier 1 (`bar1_steps`) or on barrier 0 in one of its
three uses: the early generations, the loop, the last generation (`bar0_early_steps`,
`bar0_loop_steps`, `bar_steps_final`). `barSteps_of` assembles `Remaining.barSteps` from two
structures that say exactly what is still open:

* `Bar0Facts` (thread layer, rows of thread-layer gaps): the default partition's threads of a CTA
  agree on
  the count of each ordinal of barrier 0 (`Bar.AlphaAgree`, already a premise of `ctaBar`), a thread
  has at most one last-generation arrival, and the lanes of a warp agree on its source ordinal;
* `BarTime` (the `time` function): at a barrier event the state after is later than the state
  before, and every lane of the participants that has not yet made the arrival is pending
  (it has not exited) and no later than the state before the event.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 100000 in
/-- **Every named barrier of the kernel is barrier 0 or 1**: an audit of the program text. -/
theorem kernel_barIds : kernel.code.all (fun ins =>
    match ins.op with
    | .barSync (.imm i) _ => decide (i = 0 ∨ i = 1)
    | _ => true) = true := by
  decide +kernel

/-- **A barrier event is on barrier 0 or 1.** -/
theorem bar_id_le_one (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) : id ≤ 1 := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (fun pc' f h => by cases h)
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) ⟨pc, .bar id cnt mode⟩ o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  have hall := List.all_eq_true.mp kernel_barIds ins hmem
  rcases bar_kind_op hb hmem hf' (show (⟨pc, .bar id cnt mode⟩ : Event).kind = .bar id cnt mode
    from rfl) with ⟨al, hop⟩ | ⟨h0, -⟩
  · rw [hop] at hall
    simp only [decide_eq_true_eq] at hall
    omega
  · omega

/-- **The thread layer's facts about named barrier 0.** -/
structure Bar0Facts (L : Launch) (X : Execution) : Prop where
  /-- The default partition's threads of a CTA agree on the count of each source ordinal. -/
  alpha : Bar.AlphaAgree L X
  /-- A thread has at most one last-generation arrival. -/
  one : ∀ {g j j' : Nat}, g < L.threads → FinalArr X 0 2 g j → FinalArr X 0 2 g j' → j = j'
  /-- The lanes of a warp agree on the source ordinal of their last-generation arrival. -/
  lock : ∀ {y y' j j' : Nat}, y < L.threads → y' < L.threads → y / L.block = y' / L.block →
    y % L.block / 32 = y' % L.block / 32 → FinalArr X 0 2 y j → FinalArr X 0 2 y' j' →
    ((X.tr y).take j).countP (Execution.isBarId 0) = ((X.tr y').take j').countP
      (Execution.isBarId 0)

/-- **What the virtual time has to satisfy at the barriers.** -/
structure BarTime (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (X : Execution) : Prop where
  /-- After a barrier event the state is later than the one before it, or the machine stopped. -/
  after : ∀ {g k pc id : Nat} {cnt : Option Nat} {d : TSt}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar id cnt .sync⟩ → St Q L X g k = some (some d) →
    (∃ d', St Q L X g (k + 1) = some (some d') ∧ T g d < T g d') ∨ St Q L X g (k + 1) = none
  /-- Barrier 1: a lane of the CTA with at most as many barrier-1 events as precede the event has
  not exited and is no later than the state before it. -/
  lag1 : ∀ {g k pc y : Nat} {d : TSt}, g < L.threads → X.get (g, k) = some ⟨pc, .bar 1 none .sync⟩ →
    St Q L X g k = some (some d) → y < L.threads → y / L.block = g / L.block →
    (X.tr y).countP (Execution.isBarId 1) ≤ ((X.tr g).take k).countP (Execution.isBarId 1) →
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d
  /-- Barrier 0, early generations (source ordinal below 2). -/
  lag0e : ∀ {g k pc y : Nat} {d : TSt}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar 0 none .sync⟩ →
    ((X.tr g).take k).countP (Execution.isBarId 0) < 2 → St Q L X g k = some (some d) →
    y < L.threads → y / L.block = g / L.block →
    (X.tr y).countP (Execution.isBarId 0) ≤ ((X.tr g).take k).countP (Execution.isBarId 0) →
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d
  /-- Barrier 0, the loop (`bar.sync 0, 128`, the warps of the default partition). -/
  lag0l : ∀ {g k pc y : Nat} {d : TSt}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar 0 (some 128) .sync⟩ → St Q L X g k = some (some d) →
    y < L.threads → y / L.block = g / L.block → y % L.block < 128 →
    (X.tr y).countP (Execution.isBarId 0) ≤ ((X.tr g).take k).countP (Execution.isBarId 0) →
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d
  /-- Barrier 0, the last generation: a lane that has not made its last-generation arrival. -/
  lag0f : ∀ {g k pc y : Nat} {d : TSt}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar 0 none .sync⟩ →
    2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0) → St Q L X g k = some (some d) →
    y < L.threads → y / L.block = g / L.block → (∀ j, ¬ FinalArr X 0 2 y j) →
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed T Q L) X y ≤ T g d

/-- **A blocked `bar.sync 0` steps.** -/
theorem bar0_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hmax : Maximal L kernel asms mem0 X)
    (ht : Frame.Tracked (code L Q) X) (hF : Bar0Facts L X) (hT : BarTime T Q L X) {g pc : Nat}
    {cnt : Option Nat} (hp : Frame.Pending L X g) (hnr : ¬ Step.Released L X g)
    (hlen : 0 < (X.tr g).length) (hlast : X.IsBarrier (g, (X.tr g).length - 1) 0 cnt pc) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar 0 cnt .sync⟩ := by
    exact hlast
  obtain ⟨d, hd⟩ := Frame.event_state hS hX ht hget (fun pc' f h => by cases h)
  have hafter := hT.after hg hget hd
  rcases bar0_event_class hpre hX hS ht hget with hc | ⟨hc, -, -⟩
  · subst hc
    by_cases hG : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) < 2
    · exact bar0_early_steps hpre hs hS hmax ht hp hnr hlen hget hG hd hafter
        (fun y hy hdiv hle => hT.lag0e hg hget hG hd hy hdiv hle)
    · have hstartG : 2 ≤ ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId 0) := by
        omega
      refine bar_steps_final (D := Bar.loopGroup) (cD := some 128) (start := 2)
        (Bar.loopGroup_sub hpre) Bar.loopGroup_card (Bar.loopGroup_ne hpre)
        Bar.loopGroup_target (Bar.bar0_sources hpre hX hS ht) (bar0_shape hpre) hs hmax hp hnr hlen
        hget hstartG (fun j hj => hF.one hg hj ⟨pc, .sync, hget, hstartG⟩ ▸ rfl) ?_ hd hafter
        (fun y hy hdiv hno => hT.lag0f hg hget hstartG hd hy hdiv hno)
      intro y y' j j' hy hy' hdy hdy' hw hj hj'
      exact hF.lock hy hy' (hdy.trans hdy'.symm) hw hj hj'
  · subst hc
    exact bar0_loop_steps hpre hs hS hmax ht hF.alpha hp hnr hlen hget hd hafter
      (fun y hy hdiv hyD hle => hT.lag0l hg hget hd hy hdiv hyD hle)

/-- **`Remaining.barSteps`**, from the barrier-0 thread facts and the time facts of the barriers. -/
theorem barSteps_of (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (htr : ∀ X, Consistent L kernel asms mem0 X → Frame.Tracked (code L Q) X)
    (hF : ∀ X, Consistent L kernel asms mem0 X → Bar0Facts L X)
    (hT : ∀ X, Consistent L kernel asms mem0 X → BarTime T Q L X) : BarSteps T Q L mem0 := by
  intro X g hmax hp hnr hw
  obtain ⟨id, cnt, pc, hlen, hlast, -⟩ := hw
  have hX := hmax.1
  have hg := hp.1
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hget : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id cnt .sync⟩ := hlast
  have hid := bar_id_le_one hpre hX hS (htr X hX) hget
  have hid01 : id = 0 ∨ id = 1 := by omega
  rcases hid01 with rfl | rfl
  · exact bar0_steps hpre hs hS hmax (htr X hX) (hF X hX) (hT X hX) hp hnr hlen hlast
  · obtain ⟨hc, -⟩ := bar_one_static hX hb hget
    subst hc
    obtain ⟨d, hd⟩ := Frame.event_state hS hX (htr X hX) hget (fun pc' f h => by cases h)
    exact bar1_steps hpre hs hmax hp hnr hlen hlast hd ((hT X hX).after hg hget hd)
      (fun y hy hdiv hle => (hT X hX).lag1 hg hget hd hy hdiv hle)

end

end PTX.Kernels.InklingRelDecode.Proof.Progress

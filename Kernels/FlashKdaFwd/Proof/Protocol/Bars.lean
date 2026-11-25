-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Layout
public import Lemmas.Kernel.Safety.Schedule
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Lemmas.Execution.NoBarArrive
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The CTA barrier `bar.sync 0` and the named barrier `bar.sync 8, 128`

**What the thread layer exports** (`BarFacts`, facts about the events of one thread): every
barrier event is a `bar.sync` of barrier 0 without a thread count or, in a compute thread, of
barrier 8 with thread count 128; a thread executes at most nine `bar.sync 0` and exactly nine
before it exits; a compute thread executes at most `T` named barriers (`T` = the number of tiles
of its CTA) and exactly `T` before it exits; and the barrier of each ordinal among a thread's
barrier events is the one of the schedule `barSched`.

**What the library gives from them.**

* `shape0`, `sources0`, `shape8`, `sources8`: the library's descriptions of the two barrier
  groups (`NamedBar.Shape`, `NamedBar.Sources`).
* `handoff0`: the CTA barrier is a hand-off (`Frame.Handoff`, by `Frame.Handoff.of_bar`): an
  event of a thread with at most `q` `bar.sync 0` up to and including it happens before every
  event of a thread of the same CTA with more than `q` `bar.sync 0` before it. This is the only
  form in which the layers above use the nine barriers.
* `noCtaBarFault`: no barrier arrival faults (`not_ctaBarFault`).
* `noBarMismatch`: the lanes of a warp agree on every barrier (`noBarMismatch_of_schedule`).

The named barrier is not needed as a hand-off: every memory order it could give is given by
the mbarrier hand-offs of the two pipelines (see the plan). `Frame.Handoff.of_bar` would not
apply to it as stated, because its bound on the number of arrivals is one number for the whole
launch and the number of tiles differs between CTAs. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame

/-- The barrier of ordinal `k` among the barrier events of a thread: six `bar.sync 0`, then in
a compute thread one named barrier per tile, then three `bar.sync 0`. -/
def barSched (compute : Bool) (T k : Nat) : Nat × Option Nat × BarMode :=
  if compute = true ∧ 6 ≤ k ∧ k < 6 + T then (8, some 128, .sync) else (0, none, .sync)

/-- **Thread-layer facts about barrier events.** `T c` is the number of tiles of CTA `c`. -/
structure BarFacts (L : Launch) (X : Execution) (T : Nat → Nat) : Prop where
  /-- Every barrier event is `bar.sync 0` or a compute thread's `bar.sync 8, 128`. -/
  shape : ∀ {g k pc id : Nat} {cnt : Option Nat} {mode : BarMode}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ →
      mode = .sync ∧ ((id = 0 ∧ cnt = none) ∨ (id = 8 ∧ cnt = some 128 ∧ g % L.block < 128))
  /-- A thread executes at most nine `bar.sync 0`. -/
  bar0_le : ∀ {g : Nat}, g < L.threads → (X.tr g).countP (Execution.isBarId 0) ≤ 9
  /-- A thread that exits has executed nine `bar.sync 0`. -/
  bar0_exit : ∀ {g j pc : Nat}, g < L.threads → X.get (g, j) = some ⟨pc, .exit⟩ →
    (X.tr g).countP (Execution.isBarId 0) = 9
  /-- The `bar.sync 0` with `k` earlier ones is at the `k`-th of the nine positions. -/
  bar0_pc : ∀ {g k pc : Nat} {cnt : Option Nat} {mode : BarMode}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩ → bar0Pcs[bar0Before X (g, k)]? = some pc
  /-- A named barrier event is at the one `bar.sync %r1615, %r1616` (2913). -/
  bar8_pc : ∀ {g k pc : Nat} {cnt : Option Nat} {mode : BarMode}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar 8 cnt mode⟩ → pc = 2913
  /-- A compute thread executes at most one named barrier per tile. -/
  bar8_le : ∀ {g : Nat}, g < L.threads → g % L.block < 128 →
    (X.tr g).countP (Execution.isBarId 8) ≤ T (g / L.block)
  /-- A compute thread that exits has executed one named barrier per tile. -/
  bar8_exit : ∀ {g j pc : Nat}, g < L.threads → g % L.block < 128 →
    X.get (g, j) = some ⟨pc, .exit⟩ → (X.tr g).countP (Execution.isBarId 8) = T (g / L.block)
  /-- The barrier of each ordinal is the schedule's. -/
  sched : ∀ {g k pc id : Nat} {cnt : Option Nat} {mode : BarMode}, g < L.threads →
    X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ →
      (id, cnt, mode) = barSched (decide (g % L.block < 128)) (T (g / L.block))
        (((X.tr g).take k).countP Execution.isBar)

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

/-- The group of the CTA barrier: all six warps, no thread count. -/
theorem shape0 (hb : L.block = 192) : NamedBar.Shape L none (Finset.range 6) 0 where
  pos := by simp
  target := by rw [hb]; rfl
  bound := fun w hw => by rw [hb]; exact Finset.mem_range.mp hw
  id_lt := by decide

/-- The group of the named barrier: the four compute warps, thread count 128. -/
theorem shape8 (hb : L.block = 192) : NamedBar.Shape L (some 128) (Finset.range 4) 8 where
  pos := by simp
  target := by rw [hb]; rfl
  bound := fun w hw => by rw [hb]; have := Finset.mem_range.mp hw; omega
  id_lt := by decide

namespace BarFacts

/-- Every arrival on barrier 0 is a lane of one of the six warps, without a thread count. -/
theorem sources0 (hF : BarFacts L X T) (hb : L.block = 192) :
    NamedBar.Sources L X none (Finset.range 6) 0 := by
  rintro ⟨g, k⟩ pc cnt ⟨mode, he⟩ hg
  have hm : g % L.block < 192 := by rw [hb]; exact Nat.mod_lt _ (by decide)
  refine ⟨Finset.mem_range.mpr (show g % L.block / 32 < 6 by omega), ?_⟩
  rcases (hF.shape hg he).2 with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · cases h

/-- Every arrival on barrier 8 is a lane of a compute warp, with thread count 128. -/
theorem sources8 (hF : BarFacts L X T) : NamedBar.Sources L X (some 128) (Finset.range 4) 8 := by
  rintro ⟨g, k⟩ pc cnt ⟨mode, he⟩ hg
  rcases (hF.shape hg he).2 with ⟨h, -⟩ | ⟨-, hc, hw⟩
  · cases h
  · have hw' : g % L.block < 128 := hw
    exact ⟨Finset.mem_range.mpr (show g % L.block / 32 < 4 by omega), hc⟩

/-- **The CTA barrier as a hand-off.** In one CTA, an event with at most `q` `bar.sync 0` up to
and including it happens before an event with more than `q` `bar.sync 0` before it. -/
theorem handoff0 (hF : BarFacts L X T) (hX : Consistent L K A mem0 X) (hb : L.block = 192) :
    Handoff L X (fun g h => SameCta L g h) (bar0UpTo X) (bar0Before X) := by
  have H := Handoff.of_bar hX (hF.sources0 hb) (shape0 hb) (syncs := fun _ => True)
    (fun h j pc cnt mode _ he => (hF.shape (Frame.lt_of_get hX he) he).1) (N := 9)
    (fun g hg _ => hF.bar0_le hg) (fun g hg _ ⟨j, pc, hx⟩ => hF.bar0_exit hg hx)
  refine H.mono fun g h hs => ⟨hs, Finset.mem_range.mpr ?_, trivial⟩
  have : g % L.block < 192 := by rw [hb]; exact Nat.mod_lt _ (by decide)
  omega

/-- **No barrier arrival faults**: in a CTA, the arrivals on one barrier carry one count. -/
theorem noCtaBarFault [Fact K.NoBarArrive] (hF : BarFacts L X T)
    (hX : Consistent L K A mem0 X) : ¬ CtaBarFault L X := by
  refine not_ctaBarFault hX ?_
  rintro ⟨g, k⟩ ⟨h, j⟩ id cnt cnt' pc pc' - he hf
  rcases (hF.shape (Frame.lt_of_get hX he) he).2 with ⟨h0, hc⟩ | ⟨h8, hc, -⟩ <;>
    rcases (hF.shape (Frame.lt_of_get hX hf) hf).2 with ⟨h0', hc'⟩ | ⟨h8', hc', -⟩
  · rw [hc, hc']
  · omega
  · omega
  · rw [hc, hc']

/-- **The lanes of a warp agree on every barrier** (ERR-BARRIER-MISMATCH). -/
theorem noBarMismatch (hF : BarFacts L X T) (hb : L.block = 192) : ¬ BarMismatch L X := by
  refine noBarMismatch_of_schedule
    (fun g => barSched (decide (g % L.block < 128)) (T (g / L.block)))
    (fun g k pc id cnt mode hg he => hF.sched hg he) ?_
  rintro g h ⟨⟨hg, hh, hc⟩, hw⟩
  have h1 : g % L.block < 192 := by rw [hb]; exact Nat.mod_lt _ (by decide)
  have h2 : h % L.block < 192 := by rw [hb]; exact Nat.mod_lt _ (by decide)
  have h3 : decide (g % L.block < 128) = decide (h % L.block < 128) := by
    rw [decide_eq_decide]
    omega
  rw [h3, hc]

end BarFacts

end PTX.Kernels.FlashKdaFwd.Protocol

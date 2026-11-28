-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # Lanes of a warp at one barrier ordinal agree on the barrier

From the named-barrier rows (`bar_use`) and the ordinal inputs (`BarInputs`): two lanes of one
warp at their `k`-th barrier event name one barrier with one thread count (`bar_same`), and no
barrier event is a `bar.arrive` (`bar_sync`); only the startup's `bar.sync 0` names barrier 0,
without a count (`bar0_count`, the field `count` of `Bar0Rows`); a barrier's events all pass its
count (`bar_cnt`).

* A barrier event is of one of three classes (`bar_cls`): the startup's `bar.sync 0` (pc 97),
  warpgroup 0's (`Wg0Use`, warps 0–3), or `everyone_sync` (barrier 12, all 384 threads, recorded
  without a count: `BarRow.recCnt`) of a role of warps 4–11.
* The startup's barrier is its thread's first (`BarInputs.first`) and every other barrier event
  has one before it (`BarInputs.later`), so a startup barrier and another one are at different
  ordinals; warpgroup 0's lanes of one warp at one ordinal are at one pc (`BarInputs.wg0`); a warp
  is of warpgroup 0 or of warps 4–11, never both.

**Inputs** (`BarInputs`, trace counts of each lane's own barrier events): `first`, `later` (lane
A, from the startup's view: the `bar.sync 0` at 97 is the thread's first barrier event, and every
role starts after it); `wg0` (lane W1: warpgroup 0's control flow is warp-uniform, so the lanes of
a warp reach their `k`-th barrier at one site). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The barrier ordinal inputs** (owners per field). -/
structure BarInputs (L : Launch) (X : Execution) : Prop where
  /-- (lane A) The startup's barrier event is its thread's first. -/
  first : ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → StartupAt e.pc →
    Execution.isBar e = true → ((X.tr g).take k).countP Execution.isBar = 0
  /-- (lane A) Every other barrier event follows a barrier event of its thread. -/
  later : ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → 103 ≤ e.pc →
    Execution.isBar e = true → 0 < ((X.tr g).take k).countP Execution.isBar
  /-- (lane W1) Lanes of one warp of warpgroup 0 at one barrier ordinal are at one pc. -/
  wg0 : ∀ {g h i j : Nat} {e e' : Event}, SameWarp L g h → X.get (g, i) = some e →
    X.get (h, j) = some e' → Wg0At L g e.pc → Wg0At L h e'.pc → Execution.isBar e = true →
    Execution.isBar e' = true →
    ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar →
    e.pc = e'.pc

/-- The three classes of a barrier event. -/
def BarCls (L : Launch) (g : Nat) (e : Event) : Prop :=
  (StartupAt e.pc ∧ BarRow.Cta e) ∨ (Wg0At L g e.pc ∧ BarRow.Wg0Use L g e) ∨
    (4 ≤ warp L g ∧ 103 ≤ e.pc ∧ e.kind = .bar 12 none .sync)

/-- **A barrier event is of one of three classes.** -/
theorem bar_cls {g : Nat} {e : Event} (hu : BarUse L g e) : BarCls L g e := by
  rcases hu with ⟨hw, -, h⟩ | ⟨hw, h⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ |
    ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩ | ⟨⟨hw, -⟩, ⟨hpc, h⟩⟩
  · exact .inl ⟨hw, h⟩
  · exact .inr (.inl ⟨hw, h⟩)
  all_goals exact .inr (.inr ⟨by omega, by omega, h⟩)

/-- Lanes of one warp have one warp index. -/
theorem warp_eq (hp : Pre P L m) {g h : Nat} (hw : SameWarp L g h) : warp L g = warp L h := by
  obtain ⟨-, hs⟩ := hw
  simp only [warp, tidOf_x_eq hp, ← hp.block]
  exact hs

/-- **No barrier event is a `bar.arrive`.** -/
theorem bar_sync (hR : BarRows P L X) {g k id pc : Nat} {cnt : Option Nat} {md : BarMode}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩) : md = .sync := by
  rcases bar_cls (bar_use hR hg he rfl) with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, -, h⟩
  all_goals simp only [BarRow.Cta, BarRow.Sync, Kind.bar.injEq] at h
  all_goals exact h.2.2

/-- **Barrier 0 is passed without a thread count** (`Bar0Rows.count`, from the rows): only the
startup's `bar.sync 0` names barrier 0. -/
theorem bar0_count (hR : BarRows P L X) {e : EvId} {pc : Nat} {cnt : Option Nat}
    (ha : X.IsBarArrival e 0 cnt pc) (hg : e.1 < L.threads) : cnt = none := by
  obtain ⟨md, he⟩ := ha
  rcases bar_cls (bar_use hR hg he rfl) with ⟨-, h⟩ | ⟨-, h | h | ⟨-, h⟩⟩ | ⟨-, -, h⟩
  · simp only [BarRow.Cta, Kind.bar.injEq] at h
    exact h.2.1
  · obtain ⟨-, h⟩ := h
    simp only [BarRow.Sync, Kind.bar.injEq] at h
    omega
  · obtain ⟨-, h⟩ := h
    simp only [BarRow.Sync, Kind.bar.injEq] at h
    omega
  all_goals simp only [Kind.bar.injEq] at h
  all_goals omega

/-- The thread count of barrier `id`: none for barrier 0, 128 for `wg0_sync` (9), 64 for the
warp-pair barriers (10, 11), none for `everyone_sync` (12: all 384 threads, `BarRow.recCnt`). -/
def barCnt : Nat → Option Nat
  | 0 => none
  | 9 => some 128
  | 10 | 11 => some 64
  | _ => none

/-- **A barrier event's count is its barrier's** (`barCnt`). -/
theorem bar_cnt (hR : BarRows P L X) {g k id pc : Nat} {cnt : Option Nat} {md : BarMode}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .bar id cnt md⟩) : cnt = barCnt id := by
  rcases bar_cls (bar_use hR hg he rfl) with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩⟩ |
    ⟨-, -, h⟩
  all_goals simp only [BarRow.Cta, BarRow.Sync, Kind.bar.injEq] at h
  all_goals obtain ⟨rfl, rfl, -⟩ := h
  all_goals try rfl
  rcases Nat.mod_two_eq_zero_or_one (warp L g) with h2 | h2 <;> rw [h2] <;> rfl

/-- **Lanes of one warp at one barrier ordinal agree on the barrier and the count.** -/
theorem bar_same (hp : Pre P L m) (hR : BarRows P L X) (hO : BarInputs L X) {g h i j : Nat}
    {e e' : Event} (hw : SameWarp L g h) (hi : X.get (g, i) = some e)
    (hj : X.get (h, j) = some e') (hb : Execution.isBar e = true)
    (hb' : Execution.isBar e' = true)
    (hk : ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar) :
    e.kind = e'.kind := by
  obtain ⟨⟨hg, hh, -⟩, -⟩ := id hw
  have hwe := warp_eq hp hw
  rcases bar_cls (bar_use hR hg hi hb) with ⟨hs, hc⟩ | ⟨hs, hc⟩ | ⟨hs, hpc, hc⟩ <;>
    rcases bar_cls (bar_use hR hh hj hb') with ⟨hs', hc'⟩ | ⟨hs', hc'⟩ | ⟨hs', hpc', hc'⟩
  · exact hc.trans hc'.symm
  · have := hO.first hg hi hs hb
    have := hO.later hh hj hs'.2.1 hb'
    omega
  · have := hO.first hg hi hs hb
    have := hO.later hh hj hpc' hb'
    omega
  · have := hO.later hg hi hs.2.1 hb
    have := hO.first hh hj hs' hb'
    omega
  · have hpc := hO.wg0 hw hi hj hs hs' hb hb' hk
    simp only [BarRow.Wg0Use, BarRow.Everyone, BarRow.Sync, BarRow.wg0NineSites,
      List.mem_cons, List.not_mem_nil, or_false] at hc hc'
    rw [← hwe] at hc'
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hc' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
      first | omega | rw [h2, h2']
  · have := hs.1; omega
  · have := hO.later hg hi hpc hb
    have := hO.first hh hj hs' hb'
    omega
  · have := hs'.1; omega
  · exact hc.trans hc'.symm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

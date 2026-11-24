-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCredit

@[expose] public section

/-! # The generations of the statistics barriers

Statistics barrier `statsId st k` of a CTA has two participant warps (`pair st k`): softmax warp
`k + 4 st`, which only arrives (`bar.arrive`), and correction warp `8 + k`, which only waits
(`bar.sync`), each counting 64 (`shape`, `sources`). So generation `G` of the barrier is the
softmax warp's arrival number `G` with the correction warp's `bar.sync` number `G` (`gen_key`,
from `NamedBar.Sources.arrival_key`).

The softmax never arrives twice in one generation: before its arrival number `G + 1` it polls its
stage's credit barrier for the `G + 2`-th time, which observes the credit arrival with `G` earlier
ones of every correction thread of its CTA (`StatsCredit`); that arrival of the partner warp's
lane 0 follows its `bar.sync` number `G`, which therefore passed (`partner`). Hence generation `G`
is done before the softmax arrives again (`done_of_arrive`, `NamedBar.arrive_done_of_partner`),
and no arrival on any barrier faults (`not_ctaBarFault`) once barrier 2's `bar.arrive`, each the
last event of its thread on barrier 2, is accounted for (`Bar2ArriveLast`, a fact of the Tensor
Memory protocol). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof CtaBarrier

noncomputable section

namespace Stats

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- The two warps of statistics barrier `statsId st k`. -/
def pair (st k : Nat) : Finset Nat := {k + 4 * st, 8 + k}

theorem pair_card {st k : Nat} (hst : st < 2) : (pair st k).card = 2 :=
  Finset.card_pair (by omega)

/-- **The group of a statistics barrier**: its two warps, each counting 64. -/
theorem shape (hpre : Pre P L mem0) {st k : Nat} (hst : st < 2) (hk : k < 4) :
    NamedBar.Shape L (some 64) (pair st k) (statsId st k) where
  pos := by rw [pair_card hst]; decide
  target := by
    rw [pair_card hst]
    exact NamedBar.target_some_mul (n := 2) (by decide) (by decide)
  bound := by
    intro w hw
    rw [hpre.block]
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hw
    omega
  id_lt := by unfold statsId; omega

/-- An event on a barrier other than 2 is on a statistics barrier, counting 64: a softmax
`bar.arrive` or a correction `bar.sync`. -/
theorem stats_of_bar (ht : StatsFacts L X) {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (hg : g < L.threads) (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) (hid : id ≠ 2) :
    cnt = some 64 ∧ ∃ st k, st < 2 ∧ k < 4 ∧ id = statsId st k ∧
      ((warpOf L g = k + 4 * st ∧ m = .arrive) ∨ (warpOf L g = 8 + k ∧ m = .sync)) := by
  rcases ht.bar_form hg he with ⟨h2, -⟩ | ⟨hc, hw⟩
  · exact absurd h2 hid
  refine ⟨hc, ?_⟩
  rcases hw with ⟨hw8, rfl, rfl⟩ | ⟨h8, h12, hid', rfl⟩
  · exact ⟨warpOf L g / 4, warpOf L g % 4, by omega, by omega, by unfold statsId; omega,
      .inl ⟨by omega, rfl⟩⟩
  · rcases hid' with rfl | rfl
    · exact ⟨0, warpOf L g - 8, by omega, by omega, by unfold statsId; omega,
        .inr ⟨by omega, rfl⟩⟩
    · exact ⟨1, warpOf L g - 8, by omega, by omega, by unfold statsId; omega,
        .inr ⟨by omega, rfl⟩⟩

theorem statsId_inj {st k st' k' : Nat} (hk : k < 4) (hk' : k' < 4)
    (h : statsId st k = statsId st' k') : st = st' ∧ k = k' := by
  unfold statsId at h
  omega

/-- **The sources of a statistics barrier**: only its two warps arrive there, counting 64. -/
theorem sources (ht : StatsFacts L X) {st k : Nat} (hk : k < 4) :
    NamedBar.Sources L X (some 64) (pair st k) (statsId st k) := by
  intro e pc cnt ⟨m, he⟩ hg
  obtain ⟨hc, st', k', -, hk', hid, hw⟩ :=
    stats_of_bar ht (i := e.2) hg he (by unfold statsId; omega)
  obtain ⟨rfl, rfl⟩ := statsId_inj hk hk' hid
  refine ⟨?_, hc⟩
  simp only [pair, Finset.mem_insert, Finset.mem_singleton]
  unfold warpOf at hw
  omega

/-- An entry of a list adds one to the count of the selected entries before the next index. -/
theorem countP_take_succ {α : Type} {p : α → Bool} {xs : List α} {i : Nat} {x : α}
    (hx : xs[i]? = some x) :
    (xs.take (i + 1)).countP p = (xs.take i).countP p + if p x then 1 else 0 := by
  rw [List.take_add_one, hx, Option.toList_some, List.countP_append, List.countP_singleton]

/-- A later event on barrier `id` has a larger ordinal. -/
theorem barOrd_lt {g i j pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) (hij : i < j) :
    barOrd X g i id + 1 ≤ barOrd X g j id := by
  have h1 := countP_take_succ (p := Execution.isBarId id) (show (X.tr g)[i]? = _ from he)
  have h2 := (List.take_sublist_take_left (l := X.tr g) (by omega : i + 1 ≤ j)).countP_le
    (p := Execution.isBarId id)
  simp only [Execution.isBarId, beq_self_eq_true, ↓reduceIte] at h1
  unfold barOrd
  omega

/-- The event of a thread with `c` earlier events on barrier `id`, before an event with more. -/
theorem exists_bar {g x c id : Nat} (hc : c + 1 ≤ barOrd X g x id) :
    ∃ y pc cnt m, y < x ∧ X.get (g, y) = some ⟨pc, .bar id cnt m⟩ ∧ barOrd X g y id = c := by
  obtain ⟨y, ev, hy, hp, hcnt⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id) hc
  have hyx : y < x := by
    have := (List.getElem?_eq_some_iff.mp hy).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hyx.le] at hcnt
  have hget : X.get (g, y) = some ev := by
    change (X.tr g)[y]? = some ev
    rw [← hy, List.getElem?_take, ite_eq_left hyx]
  obtain ⟨pc, cnt, m, rfl⟩ := NamedBar.isBarId_form hp
  exact ⟨y, pc, cnt, m, hyx, hget, hcnt⟩

/-- **The credit partner of a softmax arrival**: when the softmax thread arrives again on its
statistics barrier, the partner warp's lane 0 has passed its `bar.sync` of the same ordinal. -/
theorem partner (hpre : Pre P L mem0) (ht : StatsFacts L X) (hU : StatsCredit L X)
    {g i j pc id : Nat} {cnt : Option Nat} {ev : Event} (hg : g < L.threads)
    (he : X.get (g, i) = some ⟨pc, .bar id cnt .arrive⟩) (hid : id ≠ 2) (hij : i < j)
    (hj : X.get (g, j) = some ev) (hjb : Execution.isBarId id ev = true) :
    ∃ f pcf, f.1 / L.block = g / L.block ∧ X.IsBarrier f id (some 64) pcf ∧
      f.2 + 1 < (X.tr f.1).length ∧ barOrd X f.1 f.2 id = barOrd X g i id := by
  obtain ⟨-, st, k, hst, hk, rfl, hw⟩ := stats_of_bar ht hg he hid
  have hwg : warpOf L g = k + 4 * st := by
    rcases hw with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · cases h
  obtain ⟨pcj, cntj, mj, rfl⟩ := NamedBar.isBarId_form hjb
  have hlt := barOrd_lt he hij
  have hcr := ht.soft_credit hg (by omega) hj (by unfold statsId; omega)
  have hsw : warpOf L g / 4 = st := by omega
  rw [hsw] at hcr
  obtain ⟨p, pcp, par, acq, sc, -, hpoll, hq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := statsBar L (ctaOf L g) st) (h := g) (f := j)
      (c := barOrd X g i (statsId st k) + 1) (by omega)
  obtain ⟨hcorr, hw'⟩ := corrLead_in hpre (cta_lt hg) hk
  obtain ⟨x, hx, rs, ⟨tx, cntx, pcx, hxget⟩, -⟩ :=
    hU (ctaOf L g) st hst g p pcp par acq sc _ ⟨hg, rfl, by omega, hsw⟩ hpoll hq _ hcorr
  have hcc := ht.corr_credit hcorr.1 (by omega) (by omega) hst hxget (by rw [hcorr.2.1])
  rw [hw', hx, show 8 + k - 5 + 4 * st = statsId st k by unfold statsId; omega] at hcc
  obtain ⟨y, pcy, cnty, my, hyx, hyget, hyo⟩ :=
    exists_bar (X := X) (g := corrLead L (ctaOf L g) k) (x := x) (id := statsId st k)
      (c := barOrd X g i (statsId st k))
      (by omega)
  obtain ⟨hcy, st', k', hst', hk', hid', hw''⟩ :=
    stats_of_bar ht hcorr.1 hyget (by unfold statsId; omega)
  have hmy : my = .sync := by
    rcases hw'' with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  subst hmy hcy
  refine ⟨(corrLead L (ctaOf L g) k, y), pcy, hcorr.2.1, hyget, ?_, hyo⟩
  have := len_of_get hxget
  simp only at this ⊢
  omega

/-- **The generation of a softmax arrival is done before the softmax arrives again.** -/
theorem done_of_arrive (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ht : StatsFacts L X) (hU : StatsCredit L X) {e : EvId} {key pc j : Nat}
    {cnt : Option Nat} {ev : Event} (hk : CtaBarArrivalK L X e key)
    (he : X.get e = some ⟨pc, .bar (key % 16) cnt .arrive⟩) (hij : e.2 < j)
    (hj : X.get (e.1, j) = some ev) (hjb : Execution.isBarId (key % 16) ev = true)
    (h2 : key % 16 ≠ 2) : CtaBarDone L X (e.1 / L.block) key := by
  have hg := event_thread_lt hX he
  obtain ⟨-, st, k, hst, hk4, hid, -⟩ := stats_of_bar ht hg he h2
  obtain ⟨f, pcf, hcta, hf, hpass, hord⟩ := partner hpre ht hU hg he h2 hij hj hjb
  rw [hid] at he hf hord
  exact (sources ht hk4).arrive_done_of_partner hX (shape hpre hst hk4) hk he hcta hf hpass hord

/-- **Barrier 2's premise (the last arrival)**: each `bar.arrive` on barrier 2 is the last event
of its thread on barrier 2 (barrier 2 belongs to the Tensor Memory allocation protocol). -/
def Bar2ArriveLast (X : Execution) : Prop :=
  ∀ g i j pc cnt ev, X.get (g, i) = some ⟨pc, .bar 2 cnt .arrive⟩ → i < j →
    X.get (g, j) = some ev → Execution.isBarId 2 ev = false

/-- **No CTA barrier arrival faults.** -/
theorem not_ctaBarFault (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X)
    (ht : StatsFacts L X) (hU : StatsCredit L X) (h2 : Bar2ArriveLast X) :
    ¬ CtaBarFault L X := by
  refine NamedBar.no_duplicate_arrival hX ?_ ?_
  · intro e f id cnt cnt' pc pc' m m' _ he hf
    have hge := event_thread_lt hX he
    have hgf := event_thread_lt hX hf
    rcases ht.bar_form hge he with ⟨rfl, rfl⟩ | ⟨rfl, hw⟩ <;>
      rcases ht.bar_form hgf hf with ⟨hid, rfl⟩ | ⟨rfl, hw'⟩
    · rfl
    · rcases hw' with ⟨-, h, -⟩ | ⟨h8, -, h | h, -⟩ <;> omega
    · rcases hw with ⟨-, h, -⟩ | ⟨h8, -, h | h, -⟩ <;> omega
    · rfl
  · intro e key pc cnt j ev hk he hij hj hjb
    by_cases hid : key % 16 = 2
    · rw [hid] at he hjb
      rw [h2 e.1 e.2 j pc cnt ev he hij hj] at hjb
      cases hjb
    · exact done_of_arrive hpre hX ht hU hk he hij hj hjb hid

end Stats

end
end PTX.Kernels.FlashAttn4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAllocHandshake
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsGen
public import Lemmas.Protocol.NamedBarReleased
public import Lemmas.Protocol.StagingHandoff
public import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # What reaches the exit of an exited CTA

The kernel has no exit cluster barrier. A CTA `c` that exited (`CtaExited`) has the exit of
lane 0 of its MMA warp (`lane0`), and the chain of the deallocation handshake orders the threads of
both CTAs of the pair before it, in `hb` (`ReachesExit`):

* **The handshake** (`hs_baseCausality`): lane 0 of `c`'s warp 12 exits after a successful acquire
  poll of `c`'s handshake barrier (`ExitFacts.mma_exit`, `hs_wait`), which observes the release
  arrival of every lane of the other CTA's warp 12 (`TmemAlloc.observes`, `ExitFacts.hs_arrive`).
* **The MMA warps** (`mma_reach`): lane 0 of warp 12 of either CTA of the pair passed its second
  `bar.sync 2` (generation 1) and then arrived on the other CTA's handshake barrier: for `c`
  itself before its exit, for the other CTA because `c`'s poll observed the arrival.
* **Barrier 2** (`reach_bar2`): generation 1 of barrier 2 of that CTA is then released, so every
  thread of warps 0–12 of the CTA made its second barrier-2 event (it is live there, or it exited
  after it, `ExitFacts.bar2_exit`; `NamedBar.Sources.arrival_of_released`); what it did before
  that event happens before what lane 0 of warp 12 does after its `bar.sync`
  (`NamedBar.Sources.arrive_sync_baseCausality`), so before the handshake arrival.

Barrier 2's group is warps 0–12 counting 416 (`bar2_shape`, `bar2_sources`: `StatsFacts.bar_form`
and `ExitFacts.bar2_warp`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier TmemAlloc

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Barrier 2 -/

/-- Barrier 2's warps: the softmax, correction and MMA warps. -/
def bar2Warps : Finset Nat := Finset.range 13

/-- **Barrier 2's group**: warps 0–12, counting 416. -/
theorem bar2_shape (hpre : Pre P L mem0) : NamedBar.Shape L (some 416) bar2Warps 2 where
  pos := by decide
  target := by
    simp only [bar2Warps, Finset.card_range]
    exact NamedBar.target_some_mul (n := 13) (by decide) (by decide)
  bound := by
    intro w hw
    rw [hpre.block]
    simp only [bar2Warps, Finset.mem_range] at hw
    omega
  id_lt := by decide

/-- **Barrier 2's sources**: only warps 0–12 arrive there, counting 416. -/
theorem bar2_sources (hs : StatsFacts L X) (hx : ExitFacts P L X) :
    NamedBar.Sources L X (some 416) bar2Warps 2 := by
  intro e pc cnt ⟨m, he⟩ hg
  have hw := hx.bar2_warp (i := e.2) hg he
  refine ⟨?_, ?_⟩
  · simp only [bar2Warps, Finset.mem_range]
    exact hw
  · rcases hs.bar_form (i := e.2) hg he with ⟨-, h⟩ | ⟨-, ⟨-, h, -⟩ | ⟨h8, -, h | h, -⟩⟩
    · exact h
    all_goals omega

/-! ### Lane 0 of the MMA warp -/

theorem lane0_lt (hpre : Pre P L mem0) {c : Nat} (hc : c < L.grid) : lane0 L c < L.threads := by
  unfold lane0 Launch.threads
  rw [hpre.block] at *
  nlinarith

theorem cta_lane0 (hpre : Pre P L mem0) (c : Nat) : ctaOf L (lane0 L c) = c := by
  unfold lane0 ctaOf
  rw [hpre.block]
  omega

theorem warp_lane0 (hpre : Pre P L mem0) (c : Nat) : warpOf L (lane0 L c) = 12 := by
  unfold lane0 warpOf
  rw [hpre.block]
  omega

theorem pairCta_lt (hpre : Pre P L mem0) {c : Nat} (hc : c < L.grid) : pairCta c < L.grid := by
  unfold pairCta
  rw [hpre.grid] at *
  omega

/-- A CTA of the pair of a launched CTA is launched. -/
theorem pair_lt (hpre : Pre P L mem0) {c c' : Nat} (hc : c' < L.grid) (h : c / 2 = c' / 2) :
    c < L.grid := by
  rw [hpre.grid] at *
  omega

/-- Two threads of one pair are of one cluster. -/
theorem sameCluster_pair (hpre : Pre P L mem0) {g h : Nat} (hg : g < L.threads)
    (hh : h < L.threads) (hc : ctaOf L g / 2 = ctaOf L h / 2) : SameCluster L g h := by
  refine ⟨hg, hh, ?_⟩
  simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]
  exact hc

/-- The last event of a thread of an exited CTA is its exit. -/
theorem exit_of_exited {c g : Nat} (hx : CtaExited L X c) (hg : g < L.threads)
    (hc : ctaOf L g = c) : ∃ k pc, X.get (g, k) = some ⟨pc, .exit⟩ := by
  obtain ⟨pc, hl⟩ := hx g hg hc
  rw [List.getLast?_eq_getElem?] at hl
  exact ⟨_, pc, hl⟩

/-- A thread instruction recorded in an mbarrier history is an event of the execution. -/
theorem get_of_record {L : Launch} {K : Kernel} {A : List Assumption}
    (hX : Consistent L K A mem0 X) {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m)
    {e : EvId} (hid : r.id = .thread e) : ∃ ev, X.get e = some ev ∧ ∀ pc, ev ≠ ⟨pc, .exit⟩ := by
  have ha := ((hX.tma.2.2.1 m).2.1 r hr).1
  rw [hid] at ha
  exact objectAction_thread ha

/-! ### The handshake -/

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- **The handshake orders the other CTA's warp 12 before an exit**: once lane 0 of CTA `c`'s
warp 12 exits, lane `l` of the other CTA's warp 12 made its arrival on `c`'s handshake barrier,
and the arrival happens before that exit. -/
theorem hs_baseCausality (htm : TmemFacts L X) (hx : ExitFacts P L X) {c : Nat} (hi : HsInit L X c)
    {k0 pc0 : Nat} (hk0 : X.get (lane0 L c, k0) = some ⟨pc0, .exit⟩) {l : Nat} (hl : l < 32) :
    ∃ a pca tx cnt, X.get (lane0 L (pairCta c) + l, a) =
        some ⟨pca, .arrive (hsLoc L c) tx cnt true .cluster⟩ ∧
      baseCausality L X (lane0 L (pairCta c) + l, a) (lane0 L c, k0) := by
  have h0 := Frame.lt_of_get hX hk0
  obtain ⟨-, w, -, hwk, -, pcw, acq, sc, hw⟩ := hx.mma_exit h0 (warp_lane0 hpre c) hk0
  rw [cta_lane0 hpre c] at hw
  obtain ⟨rfl, rfl⟩ := hx.hs_wait h0 hw
  have hub := observes hpre hX htm hi hw hl
  set h := lane0 L (pairCta c) + l
  set a := arriveIdx X h (hsLoc L c)
  obtain ⟨i, -, r, -, -, hri, hrid, -⟩ := hub
  obtain ⟨ev, hev, -⟩ := get_of_record hX (List.mem_of_getElem? hri) hrid
  obtain ⟨pca, tx, cnt, rel, sca, rfl⟩ := get_arriveIdx hev
  obtain ⟨rfl, rfl, -⟩ := hx.hs_arrive (Frame.lt_of_get hX hev) hev
  refine ⟨a, pca, tx, cnt, hev, ?_⟩
  have hlen : k0 < (X.tr (lane0 L c)).length := len_of_get hk0
  exact Staging.baseCausality_of_handoff (x := (h, a)) (w := (lane0 L c, w)) (m := hsLoc L c)
    ⟨tx, cnt, pca, hev⟩ ⟨⟨pcw, 0, hw⟩, observes hpre hX htm hi hw hl⟩
    ⟨sameCluster_pair hpre (Frame.lt_of_get hX hev) h0 (by
      rw [cta_lane0 hpre c]
      unfold h ctaOf lane0 pairCta at *
      rw [hpre.block] at *
      omega),
     sameCluster_pair hpre h0 (Frame.lt_of_get hX hev) (by
      rw [cta_lane0 hpre c]
      unfold h ctaOf lane0 pairCta at *
      rw [hpre.block] at *
      omega)⟩
    ⟨rfl, le_rfl⟩ ⟨rfl, hwk, hlen⟩

/-- **A lane of warp 12 of either CTA of an exited CTA's pair** made its handshake arrival,
which reaches an exit of the CTA: before its own exit, or observed by the poll of lane 0 of the
other CTA's warp 12 before that lane's exit. -/
theorem lane_reach (htm : TmemFacts L X) (hx : ExitFacts P L X) (hi : ∀ c, HsInit L X c) {c h : Nat}
    (hex : CtaExited L X c) (hc : c < L.grid) (hh : h < L.threads) (hw : warpOf L h = 12)
    (hcc : ctaOf L h / 2 = c / 2) :
    ∃ a pca tx cnt, X.get (h, a) =
        some ⟨pca, .arrive (hsLoc L (pairCta (ctaOf L h))) tx cnt true .cluster⟩ ∧
      ReachesExit L X c (h, a) := by
  by_cases hce : ctaOf L h = c
  · obtain ⟨k, pck, hk⟩ := exit_of_exited hex hh hce
    obtain ⟨a, w, haw, hwk, ⟨pca, tx, cnt, rel, sc, ha⟩, -⟩ := hx.mma_exit hh hw hk
    obtain ⟨rfl, rfl, -⟩ := hx.hs_arrive hh ha
    exact ⟨a, pca, tx, cnt, ha, ReachesExit.of_po (finish := (h, k)) ⟨hh, hce, pck, hk⟩
      (po_of_source_not_access rfl (by simp only; omega) (len_of_get hk) (by rw [ha]; rfl))⟩
  · have hh0 := lane0_lt hpre hc
    obtain ⟨k0, pc0, hk0⟩ := exit_of_exited hex hh0 (cta_lane0 hpre c)
    obtain ⟨hgl, hl⟩ := lane_of_warp hpre hw
    obtain ⟨a, pca, tx, cnt, ha, hab⟩ := hs_baseCausality hpre hX htm hx (hi c) hk0 hl
    have hpc : ctaOf L h = pairCta c := by
      unfold pairCta
      omega
    have hpg : lane0 L (pairCta c) + h % 32 = h := by
      rw [← hpc]
      exact hgl.symm
    rw [hpg] at ha hab
    have hp2 : pairCta (ctaOf L h) = c := by rw [hpc, pairCta_pairCta]
    exact ⟨a, pca, tx, cnt, by rw [hp2]; exact ha,
      ⟨(lane0 L c, k0), ⟨hh0, cta_lane0 hpre c, pc0, hk0⟩, hab⟩⟩

/-- **Lane 0 of warp 12 of either CTA of an exited CTA's pair** passed its second `bar.sync 2`
and then made an arrival that reaches an exit of the CTA. -/
theorem mma_reach (htm : TmemFacts L X) (hx : ExitFacts P L X) (hi : ∀ c, HsInit L X c) {c c' : Nat}
    (hex : CtaExited L X c) (hc : c < L.grid) (hcc : c' / 2 = c / 2) :
    ∃ j pcj cntj a, X.IsBarrier (lane0 L c', j) 2 cntj pcj ∧ barOrd X (lane0 L c') j 2 = 1 ∧
      j < a ∧ a < (X.tr (lane0 L c')).length ∧ ReachesExit L X c (lane0 L c', a) := by
  have hh := lane0_lt hpre (pair_lt hpre hc hcc)
  obtain ⟨a, pca, tx, cnt, ha, hr⟩ := lane_reach hpre hX htm hx hi hex hc hh
    (warp_lane0 hpre c') (by rw [cta_lane0 hpre c']; exact hcc)
  obtain ⟨-, -, j, hja, pcj, cntj, hj, hord⟩ := hx.hs_arrive hh ha
  exact ⟨j, pcj, cntj, a, hj, hord, hja, len_of_get ha, hr⟩

/-- A thread of warps 0–12 that reached generation 1 of barrier 2 has its second event on
barrier 2: generation 1 is released, so the thread arrived there or exited after doing so. -/
theorem bar2_second (hs : StatsFacts L X) (hx : ExitFacts P L X) {h j pcj : Nat} {cntj : Option Nat}
    (hj : X.IsBarrier (h, j) 2 cntj pcj) (hord : barOrd X h j 2 = 1)
    (hpassed : j + 1 < (X.tr h).length) {g : Nat} (hg : g < L.threads) (hcg : ctaOf L g = ctaOf L h)
    (hw : warpOf L g < 13) :
    ∃ i pc cnt m, X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩ ∧ barOrd X g i 2 = 1 := by
  have hS := bar2_sources hs hx
  have hG := bar2_shape hpre
  have hd := hS.sync_released hX hG hj hpassed
  change CtaBarrier.Released L.block (X.barriers (h / L.block)) 2 (barOrd X h j 2) at hd
  rw [hord] at hd
  rcases hS.arrival_of_released hX hG hd hg hcg
      (by simp only [bar2Warps, Finset.mem_range]; exact hw) with
    ⟨i, pc, cnt, m, he, hi⟩ | ⟨k, pc, hk⟩
  · exact ⟨i, pc, cnt, m, he, hi⟩
  · obtain ⟨y, pcy, cnty, my, -, hy, hyo⟩ :=
      Stats.exists_bar (c := 1) (hx.bar2_exit hg hw hk)
    exact ⟨y, pcy, cnty, my, hy, hyo⟩

/-- **What a thread of the pair does before its second barrier-2 event reaches an exit of an
exited CTA.** -/
theorem reach_bar2 (htm : TmemFacts L X) (hs : StatsFacts L X) (hx : ExitFacts P L X)
    (hi : ∀ c, HsInit L X c) {c : Nat} (hex : CtaExited L X c) (hc : c < L.grid) {g f : Nat}
    (hg : g < L.threads) (hcg : ctaOf L g / 2 = c / 2) (hw : warpOf L g < 13)
    (hord : barOrd X g (f + 1) 2 ≤ 1) : ReachesExit L X c (g, f) := by
  obtain ⟨j, pcj, cntj, a, hj, hjo, hja, hal, hr⟩ := mma_reach hpre hX htm hx hi hex hc hcg
  have hcta : ctaOf L g = ctaOf L (lane0 L (ctaOf L g)) := (cta_lane0 hpre _).symm
  obtain ⟨i, pc, cnt, m, he, hio⟩ :=
    bar2_second hpre hX hs hx hj hjo (by omega) hg hcta hw
  have hfi : f < i := by
    by_contra hn
    have := Stats.barOrd_lt he (j := f + 1) (by omega)
    omega
  have hhb : baseCausality L X (g, f) (lane0 L (ctaOf L g), a) :=
    (bar2_sources hs hx).arrive_sync_baseCausality hX (bar2_shape hpre)
      ⟨hg, lane0_lt hpre (cta_lt hg), hcta⟩ he hj (by omega)
      (by change barOrd X g i 2 = barOrd X _ j 2; rw [hio, hjo]) hfi hja hal
  exact hr.of_baseCausality hhb

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Lifetime

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPoll
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftP2
public import Lemmas.Order.WarpBarOrdinal
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # The softmax part of `Cross.PollRest`

Two lanes `g`, `h` of a softmax warp poll one site, `g` in an earlier round than `h`. Every
tile of the softmax has one warp barrier, after its polls (`Counts.warpBar`, `Counts.rounds`):
with `W` the warp barriers before `g`'s poll, `h` has made more than `W` before its poll, so its
`W`-th warp barrier is before its poll. That barrier's partner of `g` (full masks) is `g`'s
`W`-th warp barrier (`WarpBar.ordinal_eq`), after `g`'s poll. That barrier of `g` is a witness
of the return of `h`'s, which precedes `h`'s poll in the execution-dependency order
(`WarpBar.depStep`, `WarpBar.resumes`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- A softmax thread's warp barriers name every lane. -/
theorem soft_warpBar_member {g j m inst : Nat} (hg : g < L.threads) (hw : warpOf L g < 8)
    (he : X.WarpBar (g, j) m inst) (lane : Nat) (hl : lane < 32) : electMember m lane := by
  rw [P2Facts_soft_warpBar hpre hX ht hg hw he]
  exact electMember_full hl

/-- The warp barriers before a softmax poll grow with its round at the site. -/
theorem soft_poll_wb {g h k k' pc p p' : Nat} {m m' : Loc} {ok ok' acq acq' : Bool}
    {sc sc' : MbarScope} (hw : warpOf L g < 8) (hs : SameWarp L g h)
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hr : pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k')) :
    warpBars X g k < warpBars X h k' := by
  have hww : warpOf L g = warpOf L h := hs.2
  have hw' : warpOf L h < 8 := by omega
  have hT := soft_trips_pos hpre
  obtain ⟨d, -, hc, hi, hpc, hsd⟩ := soft_wait hpre hX ht hw he
  obtain ⟨d', -, hc', hi', hpc', hsd'⟩ := soft_wait hpre hX ht hw' he'
  have hpoll' : d'.site.isPoll = true := by
    rcases hsd' with ⟨w, h1, -⟩ | ⟨lp, h1, -⟩ <;> rw [h1] <;> rfl
  have hsite : d.site = d'.site := Softmax.pc_poll _ _ hpoll' (hpc.trans hpc'.symm)
  have r1 := hc.rounds d'.site hpoll'
  have r2 := hc'.rounds d'.site hpoll'
  rw [← hsite, hpc] at r1
  rw [hpc'] at r2
  unfold pollRound at hr
  rw [r1, r2] at hr
  unfold warpBars
  rw [hc.warpBar, hc'.warpBar]
  have ht01 := hi.tile0
  have ht02 := hi'.tile0
  have htr1 := hi.trip
  have htr2 := hi'.trip
  have htl1 := hi.tail
  obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
  obtain ⟨site', ii', tt', ww', mm', ll'⟩ := d'
  simp only at hsite hr ht01 ht02 htr1 htr2 htl1 hsd hsd'
  subst hsite
  rcases hsd with ⟨w, rfl, -⟩ | ⟨lp, rfl, -⟩
  · rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
    · simp [Softmax.roundOf, Softmax.Site.inItem] at hr
      simp [Softmax.wbPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterWB]
      exact Nat.mul_lt_mul_of_pos_left hr (by omega)
    · simp [Softmax.roundOf, Softmax.Site.inItem, Softmax.Site.tile0] at hr
      simp [Softmax.wbPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterWB]
      exact Nat.mul_lt_mul_of_pos_left hr (by omega)
    · have a1 := htr1 rfl
      have a2 := htr2 rfl
      simp [Softmax.roundOf, Softmax.Site.inTrip] at hr
      simp [Softmax.wbPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip,
        Softmax.Site.afterWB]
      rcases Nat.lt_or_ge ii ii' with hl | hl
      · have : Softmax.trips L * ii + Softmax.trips L ≤ Softmax.trips L * ii' := by
          have := Nat.mul_le_mul_left (Softmax.trips L) (Nat.succ_le_of_lt hl)
          rw [Nat.mul_succ] at this
          exact this
        omega
      · rcases Nat.lt_or_ge ii' ii with hl' | hl'
        · have : (Softmax.trips L - 1) * ii' + (Softmax.trips L - 1) ≤
              (Softmax.trips L - 1) * ii := by
            have := Nat.mul_le_mul_left (Softmax.trips L - 1) (Nat.succ_le_of_lt hl')
            rw [Nat.mul_succ] at this
            exact this
          omega
        · have : ii = ii' := by omega
          subst this
          omega
    · simp [Softmax.roundOf, Softmax.tailPos] at hr
  · cases lp
    · simp [Softmax.roundOf, Softmax.Site.inItem] at hr
      simp [Softmax.wbPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterWB]
      exact Nat.mul_lt_mul_of_pos_left hr (by omega)
    · have a1 := htr1 rfl
      have a2 := htr2 rfl
      simp [Softmax.roundOf, Softmax.Site.inTrip, Softmax.Site.afterS1] at hr
      simp [Softmax.wbPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip,
        Softmax.Site.afterWB]
      rcases Nat.lt_or_ge ii ii' with hl | hl
      · have : Softmax.trips L * ii + Softmax.trips L ≤ Softmax.trips L * ii' := by
          have := Nat.mul_le_mul_left (Softmax.trips L) (Nat.succ_le_of_lt hl)
          rw [Nat.mul_succ] at this
          exact this
        omega
      · rcases Nat.lt_or_ge ii' ii with hl' | hl'
        · have : (Softmax.trips L - 1) * ii' + (Softmax.trips L - 1) ≤
              (Softmax.trips L - 1) * ii := by
            have := Nat.mul_le_mul_left (Softmax.trips L - 1) (Nat.succ_le_of_lt hl')
            rw [Nat.mul_succ] at this
            exact this
          omega
        · have : ii = ii' := by omega
          subst this
          omega

/-- **The softmax part of `Cross.PollRest`**: two distinct lanes of a softmax warp polling at
one position in different rounds are ordered through the tile's warp barrier. -/
theorem Cross.PollRest_soft {g h k k' pc p p' : Nat} {m m' : Loc} {ok ok' acq acq' : Bool}
    {sc sc' : MbarScope} (hg : g < L.threads) (hh : h < L.threads) (hw : warpOf L g < 8)
    (hs : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hr : pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k')) :
    ∃ a, k < a ∧ DepBefore L kernel X (g, a) (h, k') := by
  have hww : warpOf L g = warpOf L h := hs.2
  have hw' : warpOf L h < 8 := by omega
  have hwb := soft_poll_wb hpre hX ht hw hs he he' hr
  -- `h`'s warp barrier of ordinal `W` before its poll
  obtain ⟨x, hxk, ev, hev, hq, hcnt⟩ := exists_nth Execution.isWarpBar (X.tr h)
    (n := warpBars X g k) (k := k') hwb
  obtain ⟨pcx, mx, ix, rfl⟩ : ∃ pc m inst, ev = ⟨pc, .warpBar m inst⟩ := by
    obtain ⟨pc0, kind⟩ := ev
    cases kind <;> simp_all [Execution.isWarpBar]
  have hxb : X.WarpBar (h, x) mx ix := ⟨pcx, hev⟩
  have hsh : SameWarp L h g := sameWarp_symm hs
  have hlg : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hlh : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨y, hp⟩ := WarpBar.partner hX hsh hxb
    (soft_warpBar_member hpre hX ht hh hw' hxb _ hlg)
  have hord := WarpBar.ordinal_eq hX hsh
    (fun j m inst hj => soft_warpBar_member hpre hX ht hh hw' hj _ hlg)
    (fun j m inst hj => soft_warpBar_member hpre hX ht hg hw hj _ hlh) hp
  -- `g`'s partner barrier is after its poll
  obtain ⟨my, iy, hxb2, hyb⟩ := hp
  have hord' : warpBars X g y = warpBars X g k := by
    rw [← hord]; exact hcnt
  have hky : k < y := by
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · have h1 := WarpBar.warpBars_succ hyb
      have h2 := PTX.Flow.countP_take_mono Execution.isWarpBar (X.tr g) (show y + 1 ≤ k by omega)
      simp only [warpBars] at h1 h2 hord'
      omega
    · subst heq
      obtain ⟨pcy, hy⟩ := hyb
      rw [he] at hy
      cases hy
  have hk' : k' < (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1
  exact ⟨y, hky, .tail (.single (.inl (WarpBar.depStep hX hs ⟨my, iy, hyb, hxb2⟩)))
    (.inl (WarpBar.resumes hxb2 hxk hk'))⟩

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftBarAgree

@[expose] public section

/-! # The softmax parts of `Cross.TcAgree`, `Cross.TcExitAgree` and `Cross.TcExitAbove`

A softmax thread makes fourteen warp-collective `tcgen05` events per tile (`Counts.tcColl`):
the loads `ld lp c` and their waits `ldW lp c` (offsets `2 c`, `2 c + 1`), the stores
`pst lp c` (offsets `8 + c` for `c < 3`, `12` for `c = 3`) and the waits `pwait lp 0`, `pwait lp 1`
(offsets `11`, `13`). Its `N`-th one is at offset `N % 14` of tile `N / 14 % n` of its item
(`n` the trips), a loop tile exactly when that tile is not `0`: its position and static operands
(`softTcAt`) depend only on the warp. At its exit it has made `14 n T` of them, `T` its cluster's
items, more than the ordinal of any of them. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The site at offset `off` of a tile. -/
def tcSite (lp : Bool) (off : Nat) : Softmax.Site :=
  if off < 8 then
    (if off % 2 = 0 then .ld lp ⟨off / 2 % 4, Nat.mod_lt _ (by decide)⟩
      else .ldW lp ⟨off / 2 % 4, Nat.mod_lt _ (by decide)⟩)
  else if off = 11 then .pwait lp 0
  else if off = 13 then .pwait lp 1
  else if off = 12 then .pst lp 3
  else .pst lp ⟨(off - 8) % 4, Nat.mod_lt _ (by decide)⟩

/-- The static operands at offset `off` of a tile. -/
def tcKindAt (L : Launch) (g off : Nat) : TcKind :=
  if off < 8 then
    (if off % 2 = 0 then .ld (Softmax.tmem L g (32 * (off / 2))) [] .s32x32b else .waitLd)
  else if off = 11 ∨ off = 13 then .waitSt
  else if off = 12 then .st (Softmax.tmem L g 112) [] .s32x32b
  else .st (Softmax.tmem L g (64 + 16 * (off - 8))) [] .s32x32b

/-- The offset of a site in its tile. -/
def tcOff : Softmax.Site → Nat
  | .ld _ c => 2 * c.val
  | .ldW _ c => 2 * c.val + 1
  | .pst _ c => if c.val < 3 then 8 + c.val else 12
  | .pwait _ h => if h.val = 0 then 11 else 13
  | _ => 0

/-- The position and static operands of a softmax thread's `N`-th warp-collective `tcgen05`
event. -/
def softTcAt (L : Launch) (g N : Nat) : Nat × TcKind :=
  ((tcSite (decide (N / 14 % Softmax.trips L ≠ 0)) (N % 14)).pc, tcKindAt L g (N % 14))

theorem softTcAt_warp {g h : Nat} (hs : SameWarp L g h) (N : Nat) :
    softTcAt L g N = softTcAt L h N := by
  obtain ⟨⟨-, -, hc⟩, hw⟩ := hs
  have hk : Softmax.kOf L g = Softmax.kOf L h := by
    simp only [Softmax.kOf, warpOf]; rw [hw]
  have hst : Softmax.stOf L g = Softmax.stOf L h := by
    simp only [Softmax.stOf, warpOf]; rw [hw]
  simp only [softTcAt, tcKindAt, Softmax.tmem, hk, hst]

/-- The ordinal of a warp-collective `tcgen05` event decomposes into item, tile and offset. -/
theorem tc_decomp {n i T off : Nat} (hT : T < n) (ho : off < 14) :
    (14 * n * i + (14 * T + off)) % 14 = off ∧
      (14 * n * i + (14 * T + off)) / 14 % n = T := by
  have e : 14 * n * i + (14 * T + off) = 14 * (n * i + T) + off := by ring
  rw [e]
  refine ⟨by omega, ?_⟩
  rw [show (14 * (n * i + T) + off) / 14 = n * i + T by omega, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hT]

/-- The tile structure of a `tcgen05` site: its count, its tile and its offset. -/
theorem soft_tc_site {L : Launch} {g : Nat} {d : Softmax.D} (hT : 1 ≤ Softmax.trips L)
    (hi : Softmax.Inv L g d)
    (hs : (∃ lp c, d.site = .ld lp c) ∨ (∃ lp c, d.site = .ldW lp c) ∨
      (∃ lp c, d.site = .pst lp c) ∨ ∃ lp h, d.site = .pwait lp h) :
    Softmax.tcPos d = 14 * Softmax.tileNo d + tcOff d.site ∧ tcOff d.site < 14 ∧
      Softmax.tileNo d < Softmax.trips L ∧
      tcSite (decide (Softmax.tileNo d ≠ 0)) (tcOff d.site) = d.site := by
  have ht0 := hi.tile0
  have htr := hi.trip
  obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
  simp only at ht0 htr hs ⊢
  rcases hs with ⟨lp, c, rfl⟩ | ⟨lp, c, rfl⟩ | ⟨lp, c, rfl⟩ | ⟨lp, c, rfl⟩
  · cases lp <;> rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
    all_goals simp [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
      Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip, tcOff, tcSite] at ht0 htr ⊢
    all_goals omega
  · cases lp <;> rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
    all_goals simp [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
      Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip, tcOff, tcSite] at ht0 htr ⊢
    all_goals omega
  · cases lp <;> rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
    all_goals simp [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
      Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip, tcOff, tcSite] at ht0 htr ⊢
    all_goals omega
  · cases lp <;> rcases Softmax.fin2_cases c with rfl | rfl
    all_goals simp [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
      Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip, tcOff, tcSite] at ht0 htr ⊢
    all_goals omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A softmax thread's `N`-th warp-collective `tcgen05` event is at `softTcAt L g N`**, and
`N` is below `14 n T`. -/
theorem soft_tc_at {g k pc : Nat} {kd : TcKind} (hw : warpOf L g < 8)
    (he : X.get (g, k) = some ⟨pc, .tc kd⟩) :
    (pc, tcStatic kd) = softTcAt L g (((X.tr g).take k).countP isTcColl) ∧
      ((X.tr g).take k).countP isTcColl < 14 * Softmax.trips L * Softmax.items L g := by
  obtain ⟨d, t, ins, o, -, hcn, hi, -, -, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hpc : d.site.pc = pc := (fires_pc hf).symm
  rw [hcn.tcColl]
  have hT := soft_trips_pos hpre
  have hs : (∃ lp c, d.site = .ld lp c) ∨ (∃ lp c, d.site = .ldW lp c) ∨
      (∃ lp c, d.site = .pst lp c) ∨ ∃ lp h, d.site = .pwait lp h := by
    unfold Softmax.Ev at hev
    cases hsd : d.site <;> simp only [hsd, reduceCtorEq, exists_false] at hev
    all_goals first
      | exact .inl ⟨_, _, rfl⟩
      | exact .inr (.inl ⟨_, _, rfl⟩)
      | exact .inr (.inr (.inl ⟨_, _, rfl⟩))
      | exact .inr (.inr (.inr ⟨_, _, rfl⟩))
  obtain ⟨h1, h2, h3, h4⟩ := soft_tc_site hT hi hs
  have hit := hi.item (by rcases hs with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
    rw [h] <;> rfl)
  rw [h1]
  obtain ⟨hm, hdv⟩ := tc_decomp (i := d.i) h3 h2
  refine ⟨?_, ?_⟩
  · unfold softTcAt
    rw [hm, hdv, h4, hpc]
    congr 1
    unfold Softmax.Ev at hev
    rcases hs with ⟨lp, c, hsd⟩ | ⟨lp, c, hsd⟩ | ⟨lp, c, hsd⟩ | ⟨lp, c, hsd⟩ <;>
      simp only [hsd] at hev ⊢
    · obtain ⟨vals, hk⟩ := hev
      injection hk with hk
      subst hk
      rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl <;> simp [tcOff, tcKindAt, tcStatic]
    · injection hev with hk
      subst hk
      rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl <;> simp [tcOff, tcKindAt, tcStatic]
    · obtain ⟨vals, hk⟩ := hev
      injection hk with hk
      subst hk
      rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl <;> simp [tcOff, tcKindAt, tcStatic]
    · injection hev with hk
      subst hk
      rcases Softmax.fin2_cases c with rfl | rfl <;> simp [tcOff, tcKindAt, tcStatic]
  · have : 14 * Softmax.trips L * (d.i + 1) ≤ 14 * Softmax.trips L * Softmax.items L g :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add] at this
    omega

/-- **The softmax part of `Cross.TcAgree`.** -/
theorem Cross.TcAgree_soft {g h k k' pc pc' n : Nat} {kd kd' : TcKind} (hw : warpOf L g < 8)
    (hs : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .tc kd⟩)
    (he' : X.get (h, k') = some ⟨pc', .tc kd'⟩) (hn : X.TcK (g, k) n) (hn' : X.TcK (h, k') n) :
    pc = pc' ∧ tcStatic kd = tcStatic kd' := by
  have hw' : warpOf L h < 8 := by
    have : warpOf L g = warpOf L h := hs.2
    omega
  have a := (soft_tc_at hpre hX ht hw he).1
  have b := (soft_tc_at hpre hX ht hw' he').1
  rw [hn.2, softTcAt_warp hs] at a
  rw [hn'.2] at b
  rw [← b] at a
  injection a with a1 a2
  exact ⟨a1, a2⟩

/-- At its exit a softmax thread has made `14 n T` warp-collective `tcgen05` events. -/
theorem soft_tc_exit {g k pc : Nat} (hw : warpOf L g < 8) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ((X.tr g).take k).countP isTcColl = 14 * Softmax.trips L * Softmax.items L g := by
  obtain ⟨d, -, hc, hi, hs⟩ := soft_exit_state hpre hX ht hw he
  rw [hc.tcColl]
  have hti := (hi.tail (.inr (.inr hs))).1
  obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
  simp only at hs hti ⊢
  subst hs hti
  simp [Softmax.tcPos, Softmax.ldPos, Softmax.wlPos, Softmax.stPos, Softmax.waitPos,
    Softmax.Site.tile0, Softmax.Site.inTrip]

/-- **The softmax part of `Cross.TcExitAgree`.** -/
theorem Cross.TcExitAgree_soft {g h k k' pc pc' : Nat} (hw : warpOf L g < 8)
    (hs : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (he' : X.get (h, k') = some ⟨pc', .exit⟩) :
    ((X.tr g).take k).countP isTcColl = ((X.tr h).take k').countP isTcColl := by
  have hw' : warpOf L h < 8 := by
    have : warpOf L g = warpOf L h := hs.2
    omega
  rw [soft_tc_exit hpre hX ht hw he, soft_tc_exit hpre hX ht hw' he']
  obtain ⟨⟨-, -, hc⟩, -⟩ := hs
  have hi : Softmax.items L g = Softmax.items L h := by
    simp only [Softmax.items, Work.T, Work.cid, clusterOf, ctaOf]
    rw [hc]
  rw [hi]

/-- **The softmax part of `Cross.TcExitAbove`.** -/
theorem Cross.TcExitAbove_soft {g h k k' pc n : Nat} (hw : warpOf L g < 8)
    (hs : SameWarp L g h) (he' : X.get (h, k') = some ⟨pc, .exit⟩) (hn : X.TcK (g, k) n) :
    n < ((X.tr h).take k').countP isTcColl := by
  have hw' : warpOf L h < 8 := by
    have : warpOf L g = warpOf L h := hs.2
    omega
  obtain ⟨⟨⟨epc, ek⟩, hx, hcl⟩, hn⟩ := hn
  obtain ⟨tk, rfl⟩ : ∃ tk, ek = .tc tk := by cases ek <;> simp_all [isTcColl]
  have := (soft_tc_at hpre hX ht hw hx).2
  rw [soft_tc_exit hpre hX ht hw' he', ← hn]
  obtain ⟨⟨-, -, hc⟩, -⟩ := hs
  have hi : Softmax.items L g = Softmax.items L h := by
    simp only [Softmax.items, Work.T, Work.cid, clusterOf, ctaOf]
    rw [hc]
  rw [← hi]
  exact this

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof

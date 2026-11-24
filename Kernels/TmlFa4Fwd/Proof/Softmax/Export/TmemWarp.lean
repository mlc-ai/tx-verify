-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem
public import Lemmas.Order.WarpBarOrdinal
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.SmWarp.WbCount
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAccSite
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' warp barriers, on their traces

A lane's warp barriers have the full mask (`soft_wb_mask`). A P store to the columns `112 …` of tile
`u` follows `u` warp barriers (`soft_st_wb`), and the lane's arrival on the second P barrier in tile
`u` follows `u + 1` (`soft_p2_wb`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem tab_parr2 : [false, true].all (fun lz => allRd.all fun r =>
    decide ((ptsOf lz (.arrive 96)).countP (before (.parr2 r)) =
      (ptsOf lz (.acquire 80)).countP (before (.parr2 r)))) = true := by
  decide +kernel

/-- **The counts at a second P arrival.** -/
theorem parr2_counts {d : D} {c : Cnt → Nat} {rb rp : Nat} (hQ : RefQ p L g d c rb rp) {r : Rd}
    (hs : d.site = .parr2 r) : c (.arrive 96) = c (.acquire 80) := by
  obtain ⟨hB, hP, -⟩ := tab_at (lz L g)
  simp only [tabOk, Bool.and_eq_true, decide_eq_true_eq] at hB hP
  obtain ⟨⟨b1, b2⟩, -⟩ := hB
  obtain ⟨⟨p1, p2⟩, -⟩ := hP
  have e1 := hQ.cnt (.acquire 80) rfl
  have e2 := hQ.cnt (.arrive 96) rfl
  unfold passed at e1 e2
  rw [b1, p1, hs] at e1
  rw [b2, p2, hs] at e2
  have h := List.all_eq_true.mp tab_parr2 (lz L g) (by cases lz L g <;> simp)
  have h2 := of_decide_eq_true (List.all_eq_true.mp h r (by cases r <;> simp [allRd]))
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L g < 8)
include hp hX hFw hw

/-- **A softmax lane's warp barriers name every lane.** -/
theorem soft_wb_mask {k mask inst : Nat} (hb : X.WarpBar (g, k) mask inst) :
    mask = 4294967295 := by
  obtain ⟨pc, he⟩ := hb
  rcases SmWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hin, hev⟩ | ⟨d, n, -, -, -, -, hev⟩
  · exfalso
    have hx : exit L g s = none := hin.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · exact (soft_wb_site hev.1 rfl).2

/-- **A P store to the columns `112 …`** of tile `u` follows `u` warp barriers. -/
theorem soft_st_wb {k a : Nat} {vals : List Value} {sh : TcShape} (hl : X.TSt (g, k) a vals sh)
    (hcol : 128 * (Prologue.warpIndex L g / 4) + 112 ≤ a % 65536) :
    warpBars X g k + 1 = Tm.sPolls L X g (Prologue.warpIndex L g / 4) k := by
  obtain ⟨-, -, q, hc, -, h2, -⟩ := soft_st hp hX hFw hw hl
  obtain ⟨pc, he⟩ := hl
  obtain ⟨d, n, cc, rb, rp, hσ, h0, hQ, hLk, hev⟩ :=
    role_state hp hX hFw hw he (.inr (.inl ⟨_, _, _, rfl⟩))
  obtain ⟨r, q', hs⟩ := soft_st_site hev
  obtain ⟨c1, -⟩ := (site_counts hQ).2 r q' hs
  obtain ⟨t1, t2, -⟩ := tm_counts hw hσ
  have hwb := wb_before hp hX hFw he hσ
  rw [hLk _ rfl, hLk _ rfl] at c1
  have hq3 : ¬ q.val < 3 := by omega
  rw [ite_eq_right hq3] at h2
  have hq' : ¬ q'.val < 3 := by
    intro h
    rw [ite_eq_left h] at c1
    omega
  rw [ite_eq_right hq'] at c1
  change d.site = _ at hs
  rw [hs] at hwb
  simp only [midWb, show q'.val = 3 by have := q'.isLt; omega, ↓reduceIte] at hwb
  omega

/-- **An arrival on the second P barrier** follows as many warp barriers as S-full polls. -/
theorem soft_p2_wb {k pc tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc,
      .arrive (Tm.p2Full L (g / L.block) (Prologue.warpIndex L g / 4)) tx cnt rel sc⟩) :
    warpBars X g k = Tm.sPolls L X g (Prologue.warpIndex L g / 4) k := by
  obtain ⟨d, n, c, rb, rp, hσ, h0, hQ, hLk, hev⟩ :=
    role_state hp hX hFw hw he (.inr (.inr ⟨_, _, _, _, _, rfl⟩))
  have hs : ∃ r, d.site = .parr2 r := by
    rcases soft_mbar hev (l := Tm.p2Full L (g / L.block) (Prologue.warpIndex L g / 4)) rfl with
      ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
    swap
    · cases hk
    rw [bl_eq hw] at hl
    simp only [Tm.p2Full, Tm.bar, Loc.mk.injEq] at hl
    have ho : arrOff d.scheduler.site = 112 := by omega
    change arrOff d.site = 112 at ho
    obtain ⟨st, v, kk, acc⟩ := d
    cases st <;> simp [arrOff] at ho
    exact ⟨_, rfl⟩
  obtain ⟨r, hs⟩ := hs
  obtain ⟨t1, t2, -⟩ := tm_counts hw hσ
  have hwb := wb_before hp hX hFw he hσ
  change d.site = _ at hs
  rw [hs] at hwb
  have h := parr2_counts hQ hs
  rw [hLk _ rfl, hLk _ rfl] at h
  rw [t1]
  simp only [midWb] at hwb
  omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

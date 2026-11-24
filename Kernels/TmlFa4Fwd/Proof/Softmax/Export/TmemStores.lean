-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemWarp
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.SmWarp.WbCount
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemAccSite
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The P stores before a P-full arrival and before a warp barrier

A softmax lane makes four P stores per tile. Three of them, of the columns below `112`, come before
its P-full arrival (`soft_store_low`), and the fourth before its warp barrier (`soft_store_high`).
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The P stores and S-full polls before a P-full arrival and a warp barrier. -/
theorem tab_stores : [false, true].all (fun lz => allRd.all fun r =>
    decide ((ptsOf lz .tcst).countP (before (.parr r)) + 1 =
      4 * (ptsOf lz (.acquire 80)).countP (before (.parr r))) &&
    decide ((ptsOf lz .tcst).countP (before (.pws r)) =
      4 * (ptsOf lz (.acquire 80)).countP (before (.pws r))) &&
    decide ((ptsOf lz (.arrive 96)).countP (before (.pws r)) =
      (ptsOf lz (.acquire 80)).countP (before (.pws r)))) = true := by
  decide +kernel

theorem store_counts {d : D} {c : Cnt → Nat} {rb rp : Nat} (hQ : RefQ p L g d c rb rp) {r : Rd} :
    (d.site = .parr r → c .tcst + 1 = 4 * c (.acquire 80)) ∧
      (d.site = .pws r → c .tcst = 4 * c (.acquire 80) ∧ c (.arrive 96) = c (.acquire 80)) := by
  obtain ⟨hB, hP, -⟩ := tab_at (lz L g)
  simp only [tabOk, Bool.and_eq_true, decide_eq_true_eq] at hB hP
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  obtain ⟨⟨p1, p2⟩, p3⟩ := hP
  have e1 := hQ.cnt (.acquire 80) rfl
  have e2 := hQ.cnt (.arrive 96) rfl
  have e3 := hQ.cnt .tcst rfl
  unfold passed at e1 e2 e3
  rw [b1, p1] at e1
  rw [b2, p2] at e2
  rw [b3, p3] at e3
  have h := List.all_eq_true.mp tab_stores (lz L g) (by cases lz L g <;> simp)
  have h2 := List.all_eq_true.mp h r (by cases r <;> simp [allRd])
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨⟨h1, h3⟩, h4⟩ := h2
  constructor
  · intro hs
    rw [hs] at e1 e3
    omega
  · intro hs
    rw [hs] at e1 e2 e3
    omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L g < 8)
include hp hX hFw hw

/-- The P store of an ordinal. -/
theorem store_nth {k n : Nat} {q : Fin 4} (hn : 4 * n + q.val + 1 ≤ Tm.stN X g k) :
    ∃ k' a vals, k' < k ∧ X.TSt (g, k') a vals .s32x32b ∧ vals.length = 16 ∧
      a % 65536 = 128 * (Prologue.warpIndex L g / 4) + 64 + 16 * q.val ∧
      Tm.sPolls L X g (Prologue.warpIndex L g / 4) k' = n + 1 := by
  obtain ⟨j, ev, hj, hget, hq, hcnt⟩ := exists_nthEv (X := X) (g := g) (k := k) (p := Tm.isTcSt)
    (n := 4 * n + q.val) hn
  obtain ⟨pc, kd⟩ := ev
  obtain ⟨a, vals, sh, rfl⟩ : ∃ a vals sh, kd = .tc (.st a vals sh) := by
    unfold Tm.isTcSt at hq
    split at hq
    · rename_i h; exact ⟨_, _, _, h⟩
    · cases hq
  have hst : X.TSt (g, j) a vals sh := ⟨pc, hget⟩
  obtain ⟨rfl, hlen, q', hcol, h1, -, h3⟩ := soft_st hp hX hFw hw hst
  have hN : Tm.stN X g j = 4 * n + q.val := hcnt
  have hq4 := q.isLt
  have hq4' := q'.isLt
  obtain rfl : q' = q := Fin.ext (by omega)
  exact ⟨j, a, vals, hj, hst, hlen, hcol, by omega⟩

/-- **The P stores below column `112` before a P-full arrival.** -/
theorem soft_store_low {k pc tx cnt : Nat} {rel : Bool} {sc : MbarScope} (q : Fin 4)
    (hq : q.val < 3) (he : X.get (g, k) = some ⟨pc,
      .arrive (Tm.pFull L (g / L.block) (Prologue.warpIndex L g / 4)) tx cnt rel sc⟩) :
    ∃ k' a vals, k' < k ∧ X.TSt (g, k') a vals .s32x32b ∧ vals.length = 16 ∧
      a % 65536 = 128 * (Prologue.warpIndex L g / 4) + 64 + 16 * q.val ∧
      Tm.sPolls L X g (Prologue.warpIndex L g / 4) k' =
        Tm.pArr L X g (Prologue.warpIndex L g / 4) k + 1 := by
  have hpa := soft_p hp hX hFw hw he
  obtain ⟨d, n, c, rb, rp, hσ, h0, hQ, hLk, hev⟩ :=
    role_state hp hX hFw hw he (.inr (.inr ⟨_, _, _, _, _, rfl⟩))
  have hs : ∃ r, d.site = .parr r := by
    rcases soft_mbar hev (l := Tm.pFull L (g / L.block) (Prologue.warpIndex L g / 4)) rfl with
      ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
    swap
    · cases hk
    rw [bl_eq hw] at hl
    simp only [Tm.pFull, Tm.bar, Loc.mk.injEq] at hl
    have ho : arrOff d.scheduler.site = 96 := by omega
    change arrOff d.site = 96 at ho
    obtain ⟨st, v, kk, acc⟩ := d
    cases st <;> simp [arrOff] at ho
    exact ⟨_, rfl⟩
  obtain ⟨r, hs⟩ := hs
  obtain ⟨t1, -, t3⟩ := tm_counts hw hσ
  have h := (store_counts hQ (r := r)).1 hs
  rw [hLk _ rfl, hLk _ rfl] at h
  exact store_nth hp hX hFw hw (by omega)

/-- **The P store from column `112` before a warp barrier.** -/
theorem soft_store_high {k mask inst : Nat} (hb : X.WarpBar (g, k) mask inst) :
    ∃ k' a vals, k' < k ∧ X.TSt (g, k') a vals .s32x32b ∧ vals.length = 16 ∧
      a % 65536 = 128 * (Prologue.warpIndex L g / 4) + 112 ∧
      Tm.sPolls L X g (Prologue.warpIndex L g / 4) k' = warpBars X g k + 1 := by
  obtain ⟨pc, he⟩ := hb
  rcases SmWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hin, hev⟩ | ⟨d, n, hσ, h0, hR, -, hev⟩
  · exfalso
    have hx : exit L g s = none := hin.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, -⟩ := hR.2 h0
    replace hQ : RefQ p L g d c rb rp := hQ
    obtain ⟨⟨r, hs⟩, -⟩ := soft_wb_site hev.1 rfl
    obtain ⟨-, -, t3⟩ := tm_counts hw hσ
    have hwb := wb_before hp hX hFw he hσ
    change d.site = _ at hs
    rw [hs] at hwb
    simp only [midWb] at hwb
    obtain ⟨h1, h2⟩ := (store_counts hQ (r := r)).2 hs
    rw [hLk _ rfl, hLk _ rfl] at h1 h2
    obtain ⟨k', a, vals, r1, r2, r3, r4, r5⟩ := store_nth hp hX hFw hw (k := k)
      (n := warpBars X g k) (q := 3) (by change 4 * warpBars X g k + 3 + 1 ≤ _; omega)
    exact ⟨k', a, vals, r1, r2, r3, by simpa using r4, r5⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Bar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefArith

@[expose] public section

/-! # Warpgroup 0's barrier ordinals: every step

A site that is not a barrier site fires no barrier event (`evK_noBar`); a barrier site fires one
event on barrier 9, 10, 11 or 12 (`evK_bar`, `barW_cases`), so the ledger's barrier count grows by
one exactly at the barrier sites (`bump_noBar`, `bump_bar`). The successor's ordinal is the state's
plus one at a barrier site (`succ_barOrd`, by the sites; at the block's end `arrS_barOrd`, from the
block's words), so the barrier facts are kept (`bar_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The warp pair's barrier is barrier 10 or 11. -/
theorem barW_cases (w : BitVec 64) : (barW w).toNat = 10 ∨ (barW w).toNat = 11 := by
  have h : andi w 1 = andi (BitVec.ofNat 64 (w.toNat % 2)) 1 := by
    apply BitVec.eq_of_toNat_eq
    simp [andi, r32, truncBits, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h2 | h2 <;>
    simp only [barW, h, h2] <;> decide

/-- The block number of the first block. -/
theorem i32_one_toNat : (i32 1).toNat = 1 := by decide

/-- **A site other than the barrier sites fires no barrier event.** -/
theorem evK_noBar {d : D} {e : Event} (hs : d.site.isBar = false) (hu : ∀ f, e.kind ≠ .ub f)
    (hev : EvK P L g w d e) : Execution.isBar e = false := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, k⟩ := e
  simp only at hu
  cases s <;> simp only [Site.isBar, Bool.true_eq_false] at hs <;>
    simp only [EvK, GWrAt, RdAt, WrAt, GenWrAt, NcEv, TcLdEv, TcStEv, ArrEv, PollEv] at hev <;>
    (try casesm* _ ∨ _, _ ∧ _, Exists _) <;> subst_vars <;> simp_all [Execution.isBar]

/-- A step on a non-barrier event keeps the barrier counts. -/
theorem bump_noBar {n : Cnt → Nat} {e : Event} (hb : Execution.isBar e = false) (id : Nat) :
    Code.bump cls n e (.bar id) = n (.bar id) := by
  obtain ⟨pc, k⟩ := e
  simp only [Code.bump, cls]
  cases k with
  | wait m q ok a sc => cases ok <;> simp_all [kindOf]
  | tc k => cases k <;> simp_all [kindOf]
  | _ => simp_all [kindOf, Execution.isBar]

/-- A step on a barrier event of id `i` counts one on `i`. -/
theorem bump_barId {n : Cnt → Nat} {e : Event} (hpc : inRole e = true) {i : Nat}
    {c : Option Nat} {md : BarMode} (hk : e.kind = .bar i c md) (id : Nat) :
    Code.bump cls n e (.bar id) = n (.bar id) + if id = i then 1 else 0 := by
  simp [Code.bump, cls, kindOf, hk, hpc, eq_comm]

/-- **The barrier facts after a barrier event** of a barrier site. -/
theorem bump_bar {d : D} {n : Cnt → Nat} {e : Event} (hpc : inRole e = true)
    (hu : ∀ f, e.kind ≠ .ub f) (hev : EvK P L g w d e) (hb : Execution.isBar e = true)
    (hz : ∀ id, id ≠ 9 → id ≠ 10 → id ≠ 11 → id ≠ 12 → n (.bar id) = 0) :
    (∀ id, id ≠ 9 → id ≠ 10 → id ≠ 11 → id ≠ 12 → Code.bump cls n e (.bar id) = 0) ∧
      barTot (Code.bump cls n e) = barTot n + 1 := by
  have hW := barW_cases w
  rcases evK_bar hu hev hb with ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨-, hk⟩ <;>
    refine ⟨fun id h9 h10 h11 h12 => ?_, ?_⟩ <;>
    simp only [barTot, bump_barId hpc hk] <;> (try rw [hz id h9 h10 h11 h12]) <;>
    split_ifs <;> omega

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The successor's ordinal** is the state's, plus one after a barrier site (every site but the
block's end). -/
theorem succ_barOrd {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
    (hs : d.site ≠ .arrS) (hn : succ P L g w d e = some (some d')) :
    barOrd d' = barOrd d + if d.site.isBar then 1 else 0 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  revert hs
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  case arrS => exact fun h => absurd rfl h
  all_goals
    intro _
    simp only [succ, dataRd, tcLoad, ncWord, poll, elemNext, afterSmr, afterSink, hb,
      Bool.false_eq_true, ↓reduceIte, afterA, finish, afterOst, nextChunk, afterObar, afterEld,
      loopEntry, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
      List.getD_cons_succ, Fin.zero_eta, Fin.mk_one] at hn
    repeat' split at hn
    all_goals (simp only [Option.some.injEq, reduceCtorEq] at hn) <;> subst hn <;>
      simp_all [barOrd, Site.reg, Site.bidx, Site.isBar, rounds, i32_one_toNat]

/-- **The ordinal at the block's end**: block `r`'s three barriers are passed, so the next
block's barrier 9 or the epilogue's first is the `3 (r + 1)`-th. -/
theorem arrS_barOrd {d d' : D} {n : Cnt → Nat} {e : Event} (hs : d.site = .arrS)
    (hJ : RefCore L g d n) (hn : succ P L g w d e = some (some d')) :
    barOrd d' = barOrd d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hs
  subst hs
  simp only [RefCore, Site.reg, Site.idx, Control.D.words, RefAt] at hJ
  obtain ⟨r, hl, -⟩ := hJ
  obtain ⟨-, hR, hrR, hbi, hcnt, -⟩ := hl
  dsimp only at hR hrR hbi hcnt
  subst hbi hcnt
  obtain ⟨he, hc, hn1⟩ := cnt_next hrR hR
  have hr1 : (W (r + 1)).toNat = r + 1 := toNat_W (by omega)
  simp only [succ] at hn
  by_cases hlast : r + 1 = rounds l0 l1
  · simp only [advance, he, decide_eq_true hlast, ↓reduceIte, hc, hn1] at hn
    simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hn
    obtain rfl := some_some_eq hn
    simp only [barOrd, Site.reg, Site.bidx, hr1, ← hlast]
    omega
  · simp only [advance, he, hlast, decide_false, Bool.false_eq_true, ↓reduceIte, hc, hn1, ne_eq,
      not_false_eq_true, decide_true, bi_next (by omega : r < 2 ^ 26)] at hn
    obtain rfl := some_some_eq hn
    have hr2 : (W (r + 1 + 1)).toNat = r + 1 + 1 := toNat_W (by omega)
    simp only [barOrd, Site.reg, Site.bidx, hr1, hr2]
    omega

set_option linter.unusedTactic false in
/-- **Every step keeps the barrier facts.** -/
theorem bar_step {d d' : D} {n : Cnt → Nat} {e : Event}
    (hb : scmp .ge .s (r2W L g) (pw P.b) = false) (hpc : inRole e = true)
    (hu : ∀ f, e.kind ≠ .ub f) (hJ : RefCore L g d n) (hB : BarOk d n) (hev : EvK P L g w d e)
    (hn : succ P L g w d e = some (some d')) : BarOk d' (Code.bump cls n e) := by
  obtain ⟨hz, ht⟩ := hB
  have ho : barOrd d' = barOrd d + if d.site.isBar then 1 else 0 := by
    by_cases hs : d.site = .arrS
    · rw [arrS_barOrd hs hJ hn, show d.site.isBar = false by rw [hs]; rfl]
      rfl
    · exact succ_barOrd hb hs hn
  cases hsb : d.site.isBar
  · have hnb := evK_noBar hsb hu hev
    simp only [hsb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at ho
    refine ⟨fun id h9 h10 h11 h12 => ?_, ?_⟩
    · rw [bump_noBar hnb]
      exact hz id h9 h10 h11 h12
    · simp only [barTot, bump_noBar hnb]
      rw [ho, ← ht]
      rfl
  · have hbe : Execution.isBar e = true := by
      cases hx : Execution.isBar e
      · obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
        obtain ⟨pc, k⟩ := e
        simp only at hsb hx hu
        cases s <;> simp only [Site.isBar, Bool.false_eq_true] at hsb <;>
          simp only [EvK] at hev <;> (try casesm* _ ∨ _, _ ∧ _, Exists _) <;> subst_vars <;>
          simp_all [Execution.isBar]
      · rfl
    obtain ⟨h1, h2⟩ := bump_bar hpc hu hev hbe hz
    simp only [hsb, ↓reduceIte] at ho
    exact ⟨h1, by rw [h2, ho, ht]⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

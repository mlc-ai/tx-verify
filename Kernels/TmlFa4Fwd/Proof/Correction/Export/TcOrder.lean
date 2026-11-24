-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcPlace
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Place
public import Kernels.TmlFa4Fwd.Proof.Correction.Order
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The order of a correction lane's `tcgen05` events

A lane past a `tcgen05` event's place has made more of them (`corr_tc_lt`), and is at a later time
(`corr_val_lt_tc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before allSites mem_allSites nexts Reg
  ordK val valT tw pend finPts rvPts finc brv bnb vv)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h j k : Nat} {e : Event}

def corrTcChk (s : Correction.Site) : Bool :=
  decide (tw s = 0) || ((val s).isSome && s.hasUk && !s.noTile && decide (s.pc < 9089) &&
    decide (CorrWarp.epi s = .ready 0))

theorem corr_tcChk_all : allSites.all corrTcChk = true := by decide +kernel

/-- The times before a `tcgen05` site, the sites at one position, the pending events inside a
stage and after it. -/
def corrPairChk (s s' : Correction.Site) : Bool :=
  (match val s, val s' with
    | some a, some b => Correction.pairOk s s' a b
    | _, _ => true) &&
  (!decide (s.pc = s'.pc) || s.noTile || decide (s = s') ||
    (decide (pend s = pend s' + 1) && decide (finc s = finc s') && match val s, val s' with
      | some a, some b => decide (4096 * a.1 + a.2 < 4096 * b.1 + b.2)
      | _, _ => false) ||
    (decide (pend s' = pend s + 1) && decide (finc s = finc s')))

theorem corr_pairChk_all : allSites.all (fun s => tcSites.all (corrPairChk s)) = true := by
  decide +kernel

private def pendChk (s s' : Correction.Site) : Bool :=
  decide (pend s = 0) || decide (pend s' = 0) || !decide (s.pc < s'.pc) ||
    (decide (brv s = brv s') && decide (pend s' < pend s)) || decide (brv s < brv s')

private theorem pend_chk : allSites.all (fun s => allSites.all (pendChk s)) = true := by
  decide +kernel

/-- The ballots of two lanes of a tile, by the places. -/
private theorem rv_le {R : Nat} {s s' : Correction.Site} {r r' : Nat} (hr : Reg R s r)
    (hr' : Reg R s' r') (hn : s.noTile = false) (hn' : s'.noTile = false)
    (hK : ordK s r < ordK s' r') : passed rvPts s r ≤ passed rvPts s' r' := by
  have := Correction.passed_lt hr hr' hn hn' hK rvPts
  omega

private theorem pend_rg : allSites.all (fun s => (decide (pend s = 0) || (decide (8006 ≤ s.pc) &&
    decide (s.pc ≤ 8446) && decide (finc s = 0) && decide (pend s ≤ 25))) &&
    (decide (tw s = 0) || decide (0 < pend s) || (decide (8447 ≤ s.pc) &&
      decide (0 < finPts.countP (· = s.pc))))) = true := by decide +kernel

private theorem rnd_tab : rvPts.countP Correction.inRound = 2 ∧
    finPts.countP Correction.inRound = 0 ∧
    (ptsOf (.nb 0)).countP Correction.inRound = 1 := by decide

/-- A correction state with its place and its relation to the trace. -/
structure CorrTcAt (p : Params) (L : Launch) (X : Execution) (g k R : Nat) (d : Correction.D)
    (n : Cls → Nat) (r : Nat) : Prop where
  cnt : ∀ c, c ≠ .st → n (.corr c) = passed (ptsOf c) d.site r
  fits : CorrWarp.CFits p L g d (n .shfl) (n .vote)
  reg : Reg R d.site r
  tile : d.site.noTile = false
  tc : TcC X g k d.site n

/-- The rescale ballots before a state are the places'. -/
theorem CorrTcAt.ballots {R : Nat} {d : Correction.D} {n : Cls → Nat} {r : Nat}
    (hA : CorrTcAt p L X g k R d n r) : ((X.tr g).take k).countP isRb = passed rvPts d.site r := by
  have h := hA.tc.ballots
  rw [hA.cnt (.nb 0) (by simp)] at h
  obtain ⟨t1, -, t3⟩ := rnd_tab
  simp only [passed, t1, t3] at h ⊢
  simp only [brv, bnb] at h
  push_cast at h
  omega

theorem CorrTcAt.tcCount {R : Nat} {d : Correction.D} {n : Cls → Nat} {r : Nat}
    (hA : CorrTcAt p L X g k R d n r) : ((X.tr g).take k).countP isTcColl + pend d.site =
      25 * ((X.tr g).take k).countP isRv + finPts.countP (before d.site) := by
  have h := hA.tc.tc
  simp only [finc] at h
  omega

private theorem pend_at (s : Correction.Site) :
    (pend s = 0 ∨ (8006 ≤ s.pc ∧ s.pc ≤ 8446) ∧ finPts.countP (before s) = 0 ∧ pend s ≤ 25) ∧
      (0 < tw s → 0 < pend s ∨ (8447 ≤ s.pc ∧ 0 < finPts.countP (· = s.pc))) := by
  have h := List.all_eq_true.mp pend_rg s (mem_allSites s)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.imp_right fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨⟨a, b⟩, by simpa [finc] using c, d⟩, fun h => ?_⟩
  rcases h2 with (h2 | h2) | h2
  · omega
  · exact .inl h2
  · exact .inr h2

/-- **A lane past a `tcgen05` event's place has made more of them.** -/
theorem corr_tc_lt {R : Nat} {d d' : Correction.D} {n n' : Cls → Nat} {r r' : Nat}
    (hA : CorrTcAt p L X g j R d n r) (hA' : CorrTcAt p L X h k R d' n' r')
    (hag : ∀ i, i < ((X.tr g).take j).countP isRb → i < ((X.tr h).take k).countP isRb →
      ordEv X isRb isRv g i = ordEv X isRb isRv h i)
    (htw : 0 < tw d.site) (hK : ordK d.site r < ordK d'.site r') :
    ((X.tr g).take j).countP isTcColl < ((X.tr h).take k).countP isTcColl := by
  have hle := rv_le hA.reg hA'.reg hA.tile hA'.tile hK
  rw [← hA.ballots, ← hA'.ballots] at hle
  have hV := countP_le_of_ordinal (p := isRb) (q := isRv) isRb_of_isRv hle
    (fun i hi => hag i hi (by omega))
  have t := hA.tcCount
  have t' := hA'.tcCount
  obtain ⟨a1, a2⟩ := pend_at d.site
  obtain ⟨b1, -⟩ := pend_at d'.site
  -- the final stage's events
  have hfin : finPts.countP (before d.site) + finPts.countP (· = d.site.pc) ≤
      finPts.countP (before d'.site) := by
    have := Correction.passed_lt hA.reg hA'.reg hA.tile hA'.tile hK finPts
    simpa [passed, rnd_tab.2.1] using this
  rcases a2 htw with hp | ⟨hpc, hp⟩
  · -- inside a rescale stage
    rcases b1 with b1 | ⟨hin', hf', hp25⟩
    · omega
    by_cases hp0 : pend d'.site = 0
    · omega
    obtain ⟨hin, hf, -⟩ := a1.resolve_left (by omega)
    -- both are inside rescale stages
    rcases Nat.lt_or_ge (((X.tr g).take j).countP isRb) (((X.tr h).take k).countP isRb) with hlt |
        hge
    · -- a later stage, whose ballot is nonzero
      obtain ⟨h1, h2⟩ := hA'.tc.taken (by omega)
      have hV' : ((X.tr g).take j).countP isRv + 1 ≤ ((X.tr h).take k).countP isRv := by
        rw [countP_ordinal (p := isRb) (q := isRv) isRb_of_isRv,
          countP_ordinal (p := isRb) (q := isRv) isRb_of_isRv]
        obtain ⟨z, hz⟩ : ∃ z, ((X.tr h).take k).countP isRb = z + 1 :=
          Nat.exists_eq_succ_of_ne_zero (by omega)
        rw [hz] at h2 ⊢
        simp only [Nat.add_sub_cancel] at h2
        rw [List.range_succ, List.countP_append, List.countP_singleton, h2]
        simp only [ite_true, Nat.add_le_add_iff_right]
        obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le (show ((X.tr g).take j).countP isRb ≤ z by omega)
        rw [hw, List.range_add, List.countP_append]
        refine Nat.le_add_right_of_le (le_of_eq (List.countP_congr fun i hi => ?_))
        have := List.mem_range.mp hi
        rw [hag i this (by omega)]
      omega
    · -- one stage
      have hpp : passed rvPts d.site r = passed rvPts d'.site r' := by
        rw [← hA.ballots, ← hA'.ballots]; omega
      have hchk := List.all_eq_true.mp (List.all_eq_true.mp pend_chk d.site (mem_allSites _))
        d'.site (mem_allSites _)
      simp only [pendChk, brv, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq, decide_eq_false_iff_not, Nat.cast_inj, Nat.cast_lt] at hchk
      simp only [passed, rnd_tab.1] at hpp
      have hb1 : rvPts.countP (before d.site) ≤ 2 := by
        have := List.countP_le_length (l := rvPts) (p := before d.site); simpa [rvPts] using this
      have hb2 : 1 ≤ rvPts.countP (before d.site) ∧ 1 ≤ rvPts.countP (before d'.site) ∧
          rvPts.countP (before d'.site) ≤ 2 := by
        have hb : allSites.all (fun s => decide (pend s = 0) ||
            (decide (1 ≤ rvPts.countP (before s)) && decide (rvPts.countP (before s) ≤ 2))) =
              true := by decide +kernel
        have q1 := List.all_eq_true.mp hb d.site (mem_allSites _)
        have q2 := List.all_eq_true.mp hb d'.site (mem_allSites _)
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at q1 q2
        have q1' := q1.resolve_left (by omega)
        have q2' := q2.resolve_left (by omega)
        exact ⟨q1'.1, q2'.1, q2'.2⟩
      have hrr : r = r' := by omega
      subst hrr
      have hpc : d.site.pc < d'.site.pc := by unfold ordK at hK; omega
      rcases hchk with (((c | c) | c) | c) | c
      · omega
      · omega
      · exact absurd hpc c
      · omega
      · omega
  · -- in the final stage
    have hp0 : pend d.site = 0 := by
      rcases a1 with a1 | ⟨⟨-, h2⟩, -⟩
      · exact a1
      · omega
    have hp0' : pend d'.site = 0 := by
      rcases b1 with b1 | ⟨⟨h1, h2⟩, hf', -⟩
      · exact b1
      · omega
    omega

/-- A time before a `tcgen05` site's place, for a site of the rounds or the final stage. -/
theorem corr_val_lt_tc {R : Nat} {s s' : Correction.Site} {r r' : Nat} {a b : Nat × Nat}
    (ha : val s = some a) (hb : val s' = some b) (hs' : 0 < tw s') (h : Reg R s r)
    (h' : Reg R s' r') (hK : ordK s r < ordK s' r') (p : Params) : valT p r a < valT p r' b := by
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp corr_pairChk_all s (mem_allSites s)) s'
    (List.mem_filter.mpr ⟨mem_allSites s', by simpa using hs'⟩)
  simp only [corrPairChk, ha, hb, Bool.and_eq_true] at h2
  obtain ⟨h2, -⟩ := h2
  exact Correction.val_lt_of (Correction.pairOk_iff.mp h2).1 (Correction.pairOk_iff.mp h2).2 h h' hK
      p

end
end PTX.Kernels.TmlFa4Fwd.Proof

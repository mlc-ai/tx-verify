-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataStat
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataWrote
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataRecip
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataTrip0
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataTrip1
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataVote0
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCountsDataVote1

@[expose] public section

/-! # `Counts`: the steps of the data of the final part

From the steps leading into each conjunct's sites (`pre_*`): a new event is the last of the
prefix, an old one keeps its index and its counts (`step_finLd`, `step_finOk`, `step_finSt`,
`step_finA`, `step_wrote`, `step_fenced`, `step_rsLd`, `step_rsSt`, `step_rsWrote`,
`step_rsVote`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The steps -/

variable {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}

theorem step_finLd (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hc : Counts L g d es) :
    ∀ st j, finChunk d' st j → ∃ r < (es ++ [e]).length, ∃ pc,
      (es ++ [e])[r]? =
        some ⟨pc, .tc (.ld (tmem L g (256 + 128 * st.val + 16 * j.val)) d'.o .s32x32b)⟩ ∧
      arrivals (leadLoc L g (144 + 8 * st.val)) ((es ++ [e]).take r) =
        trips L * d'.i + trips L := by
  intro st j hf
  obtain ⟨hp | ⟨hold, ho⟩, hi⟩ := pre_finChunk hn hf
  · obtain ⟨hs, a, hk⟩ := hp
    obtain ⟨hpc, hk'⟩ := hev
    rw [hs] at hk'
    obtain ⟨vals, hv⟩ := hk'
    rw [hk] at hv
    injection hv with hv1
    injection hv1 with ha hvals
    refine ⟨es.length, by simp, e.pc, ?_, ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk, ha]
    · rw [snoc_take le_rfl, List.take_length, hc.free st.val st.isLt, hi]
      obtain ⟨site, i, t, aw, aa, o⟩ := d
      simp only at hs
      subst hs
      fin_cases st <;> simp [freePos]
  · obtain ⟨r, hr, pc, hget, hcnt⟩ := hc.finLd st j hold
    refine ⟨r, by simp; omega, pc, by rw [snoc_get hr, hget, ho], ?_⟩
    rw [snoc_take hr.le, hcnt, hi]

theorem step_finOk (hn : next L g d e = some (some d')) (hc : Counts L g d es) :
    ∀ st j h el, d'.site = .fst st j h el → finOk d'.o (fcPair d') = true := by
  intro st j h el hs
  obtain ⟨hp, ho, haw⟩ := pre_fst hn hs
  have hfc : fcPair d' = fcPair d := by simp only [fcPair, haw]
  rw [ho, hfc]
  rcases hp with ⟨-, hok⟩ | ⟨h', el', hs'⟩
  · exact hok
  · exact hc.finOk st j h' el' hs'

theorem step_finSt (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hc : Counts L g d es) :
    ∀ st, finStat d' st → ∃ r < (es ++ [e]).length, ∃ pc ac bs,
      (es ++ [e])[r]? = some ⟨pc, .rd ac bs⟩ ∧
      ac.loc = ownLoc L g (332 + 512 * st.val + 4 * rowOf L g) ∧ rebuild 3 bs = .ok d'.aw ∧
      barEvents (kOf L g + 3 + 4 * st.val) 64 .sync ((es ++ [e]).take r) =
        (trips L + 1) * d'.i + trips L + 1 := by
  intro st hf
  obtain ⟨hp | ⟨hold, haw⟩, hi⟩ := pre_finStat hn hf
  · obtain ⟨hs, ac, bs, hk, hv⟩ := hp
    obtain ⟨hpc, hk'⟩ := hev
    rw [hs] at hk'
    obtain ⟨ac', bs', hk2, hloc⟩ := hk'
    rw [hk] at hk2
    injection hk2 with h1 h2
    subst h1 h2
    refine ⟨es.length, by simp, e.pc, ac, bs, ?_, hloc, hv, ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk]
    · rw [snoc_take le_rfl, List.take_length, hc.sync st.val st.isLt, hi]
      obtain ⟨site, i, t, aw, aa, o⟩ := d
      simp only at hs
      subst hs
      fin_cases st <;> simp [syncPos] <;> ring
  · obtain ⟨r, hr, pc, ac, bs, hget, hloc, hv, hcnt⟩ := hc.finSt st hold
    exact ⟨r, by simp; omega, pc, ac, bs, by rw [snoc_get hr, hget], hloc, by rw [haw]; exact hv,
      by rw [snoc_take hr.le, hcnt, hi]⟩

theorem step_finA (hn : next L g d e = some (some d')) (hc : Counts L g d es) :
    ∀ st, finRecip d' st → ∃ r, recipE d'.aw = .ok r ∧ d'.a = rd32 r := by
  intro st hf
  obtain ⟨⟨-, x, hx, ha⟩ | ⟨hold, ha⟩, haw⟩ := pre_finRecip hn hf
  · exact ⟨x, by rw [haw]; exact hx, ha⟩
  · obtain ⟨x, hx, ha'⟩ := hc.finA st hold
    exact ⟨x, by rw [haw]; exact hx, by rw [ha]; exact ha'⟩

theorem step_wrote (hw : WrAt L g d e) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hc : Counts L g d es) :
    ∀ st j h el, wDone d' st j h el → ∃ r < (es ++ [e]).length, ∃ pc ac bs,
      (es ++ [e])[r]? = some ⟨pc, .wr ac bs⟩ ∧ ac.loc = fstLoc L g st j h el ∧ ac.size = 4 ∧
      arrivals (ownLoc L g (256 + 8 * st.val)) ((es ++ [e]).take r) = d'.i := by
  intro st j h el hd
  obtain ⟨hs | hold, hi⟩ := pre_wDone hn hd
  · obtain ⟨hpc, hk⟩ := hev
    rw [hs] at hk
    obtain ⟨ac, bs, hk⟩ := hk
    obtain ⟨hloc, hsz⟩ := hw st j h el hs ac bs hk
    refine ⟨es.length, by simp, e.pc, ac, bs, ?_, hloc, hsz, ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk]
    · rw [snoc_take le_rfl, List.take_length, hc.staged st.val st.isLt, hi]
      obtain ⟨site, i, t, aw, aa, o⟩ := d
      simp only at hs
      subst hs
      fin_cases st <;> simp [stagedPos]
  · obtain ⟨r, hr, pc, ac, bs, hget, hloc, hsz, hcnt⟩ := hc.wrote st j h el hold
    exact ⟨r, by simp; omega, pc, ac, bs, by rw [snoc_get hr, hget], hloc, hsz,
      by rw [snoc_take hr.le, hcnt, hi]⟩

theorem step_fenced (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hc : Counts L g d es) : ∀ st : Fin 2,
    (d'.site = .oFree st true → ∃ pc, (es ++ [e])[(es ++ [e]).length - 1]? =
      some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩) ∧
    (d'.site = .staged st → ∃ pc pc' rel sc,
      (es ++ [e])[(es ++ [e]).length - 2]? =
        some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      (es ++ [e])[(es ++ [e]).length - 1]? =
        some ⟨pc', .arrive (leadLoc L g (144 + 8 * st.val)) 0 1 rel sc⟩) := by
  intro st
  obtain ⟨h1, h2⟩ := pre_fenced hn st
  obtain ⟨hpc, hk⟩ := hev
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have hd := h1 hs
    rw [hd] at hk
    refine ⟨e.pc, ?_⟩
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [snoc_last]
    obtain ⟨epc, ek⟩ := e
    simp only at hk ⊢
    rw [hk]
  · have hd := h2 hs
    rw [hd] at hk
    obtain ⟨rel, sc, hk⟩ := hk
    obtain ⟨pc, hf⟩ := (hc.fenced st).1 hd
    have hl : 1 ≤ es.length := by
      by_contra h0
      simp only [not_le, Nat.lt_one_iff, List.length_eq_zero_iff] at h0
      subst h0
      simp at hf
    refine ⟨pc, e.pc, rel, sc, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      rw [show es.length + 1 - 2 = es.length - 1 by omega, snoc_get (by omega), hf]
    · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk]

theorem pre_rsChunk (hn : next L g d e = some (some d')) {st : Fin 2} {j : Fin 8}
    (h : rsChunk d' st j) :
    ((d.site = .rld st j ∧ ∃ a, e.kind = .tc (.ld a d'.o .s32x32b)) ∨
      (rsChunk d st j ∧ d'.o = d.o)) ∧
      d'.i = d.i ∧ d'.t = d.t := by
  rcases (show st = 0 ∨ st = 1 by omega) with hst | hst
  · exact pre_rsChunk0 hn hst h
  · exact pre_rsChunk1 hn hst h

theorem pre_rsSite (hn : next L g d e = some (some d')) {st : Fin 2} (h : rsSite d' st) :
    ((d.site = .ldA st ∧ ∃ ac bs, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok d'.aw) ∨
      (rsSite d st ∧ d'.aw = d.aw)) ∧ d'.i = d.i ∧ d'.t = d.t := by
  rcases (show st = 0 ∨ st = 1 by omega) with hst | hst
  · exact pre_rsSite0 hn hst h
  · exact pre_rsSite1 hn hst h

theorem step_rsLd (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hc : Counts L g d es) :
    ∀ st j, rsChunk d' st j → ∃ r < (es ++ [e]).length, ∃ pc,
      (es ++ [e])[r]? =
        some ⟨pc, .tc (.ld (tmem L g (256 + 128 * st.val + 16 * j.val)) d'.o .s32x32b)⟩ ∧
      arrivals (leadLoc L g (144 + 8 * st.val)) ((es ++ [e]).take r) =
        trips L * d'.i + (1 + d'.t) := by
  intro st j hf
  obtain ⟨hp | ⟨hold, ho⟩, hi, htt⟩ := pre_rsChunk hn hf
  · obtain ⟨hs, a, hk⟩ := hp
    obtain ⟨hpc, hk'⟩ := hev
    rw [hs] at hk'
    obtain ⟨vals, hv⟩ := hk'
    rw [hk] at hv
    injection hv with hv1
    injection hv1 with ha hvals
    refine ⟨es.length, by simp, e.pc, ?_, ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk, ha]
    · rw [snoc_take le_rfl, List.take_length, hc.free st.val st.isLt, hi, htt]
      obtain ⟨site, i, t, aw, aa, o⟩ := d
      simp only at hs
      subst hs
      fin_cases st <;> simp [freePos]
  · obtain ⟨r, hr, pc, hget, hcnt⟩ := hc.rsLd st j hold
    refine ⟨r, by simp; omega, pc, by rw [snoc_get hr, hget, ho], ?_⟩
    rw [snoc_take hr.le, hcnt, hi, htt]

theorem step_rsSt (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hc : Counts L g d es) :
    ∀ st, rsSite d' st → ∃ r < (es ++ [e]).length, ∃ pc ac bs,
      (es ++ [e])[r]? = some ⟨pc, .rd ac bs⟩ ∧
      ac.loc = ownLoc L g (332 + 512 * st.val + 4 * rowOf L g) ∧ rebuild 3 bs = .ok d'.aw ∧
      barEvents (kOf L g + 3 + 4 * st.val) 64 .sync ((es ++ [e]).take r) =
        (trips L + 1) * d'.i + (2 + d'.t) := by
  intro st hf
  obtain ⟨hp | ⟨hold, haw⟩, hi, htt⟩ := pre_rsSite hn hf
  · obtain ⟨hs, ac, bs, hk, hv⟩ := hp
    obtain ⟨hpc, hk'⟩ := hev
    rw [hs] at hk'
    obtain ⟨ac', bs', hk2, hloc⟩ := hk'
    rw [hk] at hk2
    injection hk2 with h1 h2
    subst h1 h2
    refine ⟨es.length, by simp, e.pc, ac, bs, ?_, hloc, hv, ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk]
    · rw [snoc_take le_rfl, List.take_length, hc.sync st.val st.isLt, hi, htt]
      obtain ⟨site, i, t, aw, aa, o⟩ := d
      simp only at hs
      subst hs
      fin_cases st <;> simp [syncPos]
  · obtain ⟨r, hr, pc, ac, bs, hget, hloc, hv, hcnt⟩ := hc.rsSt st hold
    exact ⟨r, by simp; omega, pc, ac, bs, by rw [snoc_get hr, hget], hloc, by rw [haw]; exact hv,
      by rw [snoc_take hr.le, hcnt, hi, htt]⟩

theorem pre_rsStored (hn : next L g d e = some (some d')) {st : Fin 2} {j : Fin 8}
    (h : rsStored d' st j) : (d.site = .rst st j ∨ rsStored d st j) ∧ d'.i = d.i ∧ d'.t = d.t := by
  rcases (show st = 0 ∨ st = 1 by omega) with hst | hst
  · exact pre_rsStored0 hn hst h
  · exact pre_rsStored1 hn hst h

theorem pre_rsAfterVote (hn : next L g d e = some (some d')) {st : Fin 2}
    (h : rsAfterVote d' st) :
    ((d.site = .vote st ∧ ∃ m a b, e.kind = .vote m a b ∧
        ((d'.site = .rld st 0 ∧ b ≠ 0) ∨ (d'.site = .oFree st false ∧ b = 0))) ∨
      (rsAfterVote d st ∧ (d'.site = .oFree st false → d.site = .rwait st))) ∧
      d'.i = d.i ∧ d'.t = d.t ∧ d'.aw = d.aw ∧ d'.a = d.a := by
  rcases (show st = 0 ∨ st = 1 by omega) with hst | hst
  · exact pre_rsAfterVote0 hn hst h
  · exact pre_rsAfterVote1 hn hst h

theorem RsStoredIn.snoc {st : Fin 2} {j : Fin 8} {q : Nat} (h : RsStoredIn L g es st j q) :
    RsStoredIn L g (es ++ [e]) st j q := by
  obtain ⟨r, hr, pc, vals, hget, hcnt⟩ := h
  exact ⟨r, by simp; omega, pc, vals, by rw [snoc_get hr, hget], by rw [snoc_take hr.le, hcnt]⟩

theorem step_rsWrote (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hc : Counts L g d es) :
    ∀ st j, rsStored d' st j → RsStoredIn L g (es ++ [e]) st j (trips L * d'.i + (1 + d'.t)) := by
  intro st j hd
  obtain ⟨hs | hold, hi, htt⟩ := pre_rsStored hn hd
  · obtain ⟨hpc, hk⟩ := hev
    rw [hs] at hk
    obtain ⟨vals, hk⟩ := hk
    refine ⟨es.length, by simp, e.pc, vals, ?_, ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk ⊢
      rw [hk]
    · rw [snoc_take le_rfl, List.take_length, hc.free st.val st.isLt, hi, htt]
      obtain ⟨site, i, t, aw, aa, o⟩ := d
      simp only at hs
      subst hs
      fin_cases st <;> simp [freePos]
  · rw [hi, htt]
    exact (hc.rsWrote st j hold).snoc

theorem step_rsVote (hi : Inv L g d) (hev : Ev L g d e) (hv : VoteAt d e)
    (hn : next L g d e = some (some d')) (hc : Counts L g d es) :
    ∀ st, rsAfterVote d' st → (∃ b, ltOneE d'.aw = .ok b) ∧ ∃ v < (es ++ [e]).length, ∃ m a b,
      (es ++ [e])[v]? = some ⟨(Site.vote st).pc, .vote m a b⟩ ∧ a = ltOne d'.aw ∧
      arrivals (leadLoc L g (144 + 8 * st.val)) ((es ++ [e]).take v) =
        trips L * d'.i + (1 + d'.t) ∧
      (d'.site = .oFree st false → b ≠ 0 →
        ∀ j, RsStoredIn L g (es ++ [e]) st j (trips L * d'.i + (1 + d'.t))) := by
  intro st hf
  obtain ⟨hp | ⟨hold, hfree⟩, hii, htt, haw, ha⟩ := pre_rsAfterVote hn hf
  · obtain ⟨hs, m, a, b, hk, hb⟩ := hp
    obtain ⟨hpc, -⟩ := hev
    rw [hii, htt, haw]
    refine ⟨hi.alpha (by rw [hs]; rfl), es.length, by simp, m, a, b, ?_, hv st hs m a b hk, ?_,
      ?_⟩
    · rw [snoc_last]
      obtain ⟨epc, ek⟩ := e
      simp only at hk hpc ⊢
      rw [hk, hpc, hs]
    · rw [snoc_take le_rfl, List.take_length, hc.free st.val st.isLt]
      obtain ⟨site, i, t, aw, aa, o⟩ := d
      simp only at hs
      subst hs
      fin_cases st <;> simp [freePos]
    · intro hs' hb0
      rcases hb with ⟨hr, -⟩ | ⟨-, hb⟩
      · rw [hr] at hs'; cases hs'
      · exact absurd hb hb0
  · obtain ⟨hal, v, hv', m, a, b, hget, hpa, hcnt, himp⟩ := hc.rsVote st hold
    rw [hii, htt, haw]
    refine ⟨hal, v, by simp; omega, m, a, b, by rw [snoc_get hv', hget], hpa,
      by rw [snoc_take hv'.le, hcnt], fun hs hb j => ?_⟩
    have hrw := hfree hs
    exact (hc.rsWrote st j (by unfold rsStored; rw [hrw])).snoc

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction

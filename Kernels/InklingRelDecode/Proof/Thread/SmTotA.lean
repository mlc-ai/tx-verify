-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmMax

@[expose] public section

/-! # The scores and the mask on any S words (pcs 1431-1755)

The pieces of `SmScF` (the 32 packed fused multiply-adds) and `SmScM`, `SmScN` (the 32 groups of
the mask) for any S words the load returned: the pair registers hold the outcomes of `SmTot`
(`D.scP`, `mwT`) in the states `D.scoredT m` and `D.maskedT L g d m`. An `fma` that faults kills
the thread (`SegD`); the unpacks, selections and packs of the mask do not fault, because the
outcome of an `fma.rn.f32x2` is a pair of two four-byte words (`fma2E_pair4`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### One instruction that rewrites a live register -/

/-- **One instruction that writes `d` with the outcome `E`**, between facts by the table `v` and
facts by a table `v'` that gives `d` the outcome's value and agrees with `v` elsewhere. -/
theorem SegD.oneT {K : Kernel} {A : List Assumption} {pc d : Nat} {op : Op}
    {liveS liveT : List Nat} {v v' : Nat → Value} {E : Exec Value}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom liveS v) →
      execLocalA A L g t op = E.map fun x => PTX.next (setReg t d x))
    (hd : ∀ x, E = .ok x → d ∈ liveT → v' d = x)
    (hcov : ∀ r ∈ liveT, r = d ∨ (r ≠ d ∧ r ∈ liveS ∧ v' r = v r)) :
    SegD K A L g 1 pc (factsFrom liveS v) (pc + 1) (factsFrom liveT v') (E.toBool = true) := by
  intro t ht
  have he := hex t ht
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · rcases hE : E with e | x
    · rw [hE] at hok; cases hok
    rw [hE] at he
    refine ⟨_, run_local hc hl ht he, by simp [PTX.next, setReg, ht.1], ht.2.1, ht.2.2.1,
      ht.2.2.2.1, holds_of_pointwise fun r hr => ?_⟩
    rcases hcov r hr with rfl | ⟨hne, hrS, hv⟩
    · simp [PTX.next, setReg, hd x hE hr]
    · simp only [PTX.next, setReg, Function.update_of_ne hne, hv]
      exact holds_mem ht.2.2.2.2 (mem_factsFrom hrS)
  · rcases hE : E with e | x
    · rw [hE] at he
      exact dead_of_error (hc.symm ▸ by rw [ht.1]) hl ht.2.2.2.1 he
    · rw [hE] at hno; exact absurd rfl hno

/-! ### The scored states -/

theorem joinValue_slices {v : Value} (h : v.bytes = 8) :
    joinValue (slW v 0).1 (slW v 1).1 = v := by
  simp [slW, joinValue, h]

theorem scSvT_zero (d : D) : scSvT d 0 = d.sv := by
  funext k
  simp [scSvT]

theorem D.scoredT_zero (d : D) : d.scoredT 0 = d := by
  simp [D.scoredT, scSvT_zero]

theorem scoredT_pair_done (d : D) {m q : Nat} (hq : q < m) (hq' : q < 32) :
    valueOf L g (d.scoredT m) (2447 + q) = d.scP q := by
  rw [valueOf_svp _ hq']
  simp only [D.scoredT, scSvT, show 2 * q / 2 = q by omega, show (2 * q + 1) / 2 = q by omega,
    hq, ↓reduceIte]
  have e0 : slW (d.scP q) (2 * q) = slW (d.scP q) 0 := by simp [slW]
  have e1 : slW (d.scP q) (2 * q + 1) = slW (d.scP q) 1 := by simp [slW]
  rw [e0, e1]
  exact joinValue_slices (scP_bytes d q)

theorem scoredT_pair_todo (d : D) {m q : Nat} (hq : m ≤ q) (hq' : q < 32) :
    valueOf L g (d.scoredT m) (2447 + q) = d.sP q := by
  rw [valueOf_svp _ hq']
  simp only [D.scoredT, scSvT, show ¬ (2 * q / 2 < m) by omega,
    show ¬ ((2 * q + 1) / 2 < m) by omega, ↓reduceIte]
  rfl

theorem valueOf_scoredT_step (d : D) {m : Nat} (hm : m < 32) {r : Nat}
    (hr : ¬ (876 ≤ r ∧ r < 876 + 64)) (hne : r ≠ 2447 + m) :
    valueOf L g (d.scoredT (m + 1)) r = valueOf L g (d.scoredT m) r := by
  by_cases h : 2447 ≤ r ∧ r < 2447 + 32
  · obtain ⟨q, rfl⟩ : ∃ q, r = 2447 + q := ⟨r - 2447, by omega⟩
    rw [valueOf_svp _ (by omega), valueOf_svp _ (by omega)]
    have h2 : ∀ k, k / 2 = q → scSvT d (m + 1) k = scSvT d m k := by
      intro k hk
      simp only [scSvT]
      have : ¬ (k / 2 = m) := by omega
      by_cases h3 : k / 2 < m
      · simp [h3, show k / 2 < m + 1 by omega]
      · simp [h3, show ¬ (k / 2 < m + 1) by omega]
    simp only [D.scoredT]
    rw [h2 (2 * q) (by omega), h2 (2 * q + 1) (by omega)]
  · exact valueOf_frameSv (L := L) (g := g) (d := d.scoredT m) (d' := d.scoredT (m + 1)) rfl rfl
      rfl rfl rfl rfl rfl hr h

theorem wpair_bP (d : D) {m : Nat} (hm : m ≤ 31) : wpair d (31 - m) = d.bP m := by
  unfold wpair D.bP
  rw [show 31 - (31 - m) = m by omega]

/-- **One packed fused multiply-add on any S words** (pc `1431 + m`): the pair `m` becomes the
outcome `D.scP`, or the thread is dead where it faults. -/
theorem seg_fma1T (d : D) {m : Nat} (hm : m < 32) :
    SegD kernel asms L g 1 (1431 + m)
      (factsFrom (Flow.live (1431 + m)) (valueEx (valueOf L g (d.scoredT m)) (wex d 32)))
      (1431 + m + 1)
      (factsFrom (Flow.live (1431 + m + 1)) (valueEx (valueOf L g (d.scoredT (m + 1)))
        (wex d 32))) ((d.scE m).toBool = true) := by
  obtain ⟨la, lb, lc⟩ := live_f1 m hm
  have hA : valueEx (valueOf L g (d.scoredT m)) (wex d 32) (2306 - m) = d.bP m := by
    rw [show 2306 - m = 2275 + (31 - m) by omega, valueEx_wex_in _ d (by omega),
      wpair_bP d (by omega)]
  have hB : valueEx (valueOf L g (d.scoredT m)) (wex d 32) 1960 = invP d.e := by
    rw [valueEx_wex_off _ d 32 (by omega)]
    rw [show invP d.e = valueOf L g d 1960 from (valueOf_p1961 (L := L) (g := g) d).symm]
    exact valueOf_frameSv (L := L) (g := g) (d := d) (d' := d.scoredT m) rfl rfl rfl rfl rfl rfl
      rfl (by omega) (by omega)
  have hC : valueEx (valueOf L g (d.scoredT m)) (wex d 32) (2447 + m) = d.sP m := by
    rw [valueEx_wex_off _ d 32 (by omega), scoredT_pair_todo d (le_refl m) hm]
  refine SegD.oneT (d := 2447 + m) (fma2At_spec (fma_code m hm)) rfl (fun t h => ?_) ?_ ?_
  · have hpc : t.pc = 1431 + m := h.1
    have hE : Assumptions.emuSites.contains t.pc = false := by rw [hpc]; exact emu_fma m hm
    have ra := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g (d.scoredT m))
      (wex d 32)) la)
    have rb := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g (d.scoredT m))
      (wex d 32)) lb)
    have rc := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g (d.scoredT m))
      (wex d 32)) lc)
    rw [hA] at ra
    rw [hB] at rb
    rw [hC] at rc
    exact exec_fma2E (A := asms) (L := L) (g := g) (d := 2447 + m)
      (idealAtSc (L := L) (g := g) (by decide) hE)
      (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega)) ra rb rc
  · intro x hx _
    rw [valueEx_wex_off _ d 32 (by omega), scoredT_pair_done d (m := m + 1) (q := m) (by omega)
      hm, D.scP, show d.scE m = .ok x from hx]
    rfl
  · intro r hr
    have hr877 := live_f3 m hm r hr
    by_cases h0 : r = 2447 + m
    · exact .inl h0
    · refine .inr ⟨h0, (subX_sound (live_f2 m hm) r hr |>.resolve_left (by simpa using h0)).2,
        ?_⟩
      by_cases h1 : 2275 ≤ r ∧ r < 2275 + 32
      · obtain ⟨j, rfl⟩ : ∃ j, r = 2275 + j := ⟨r - 2275, by omega⟩
        rw [valueEx_wex_in _ d (by omega), valueEx_wex_in _ d (by omega)]
      · rw [valueEx_wex_off _ d 32 h1, valueEx_wex_off _ d 32 h1]
        exact valueOf_scoredT_step d hm hr877 h0

/-- **The first `m` fused multiply-adds on any S words.** -/
theorem seg_fmasT (d : D) : ∀ m, m ≤ 32 →
    SegD kernel asms L g m 1431
      (factsFrom (Flow.live 1431) (valueEx (valueOf L g d) (wex d 32))) (1431 + m)
      (factsFrom (Flow.live (1431 + m)) (valueEx (valueOf L g (d.scoredT m)) (wex d 32)))
      (∀ j < m, (d.scE j).toBool = true) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [D.scoredT_zero]
    exact (SegD.of_seg (Seg.refl _ _)).iff ⟨fun _ j hj => absurd hj (by omega),
      fun _ => trivial⟩
  | succ m ih =>
    intro hm
    refine ((ih (by omega)).comp (seg_fma1T d (m := m) (by omega))).iff ⟨fun h j hj => ?_,
      fun h => ⟨fun j hj => h j (by omega), h m (by omega)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h.1 j hj
    · exact h.2

/-- **The scores on any S words** (pcs 1303 to 1462): the bias widening and the 32 packed fused
multiply-adds; the thread is dead where an `fma` faults. -/
theorem seg_scoresT (d : D) (hb : ∀ k < 64, BfOk (d.wd k)) :
    SegD kernel asms L g 160 1303 (factsAt L g 1303 d) 1463 (factsAt L g 1463 (d.scoredT 32))
      (∀ j < 32, (d.scE j).toBool = true) := by
  have h := SegD.seg_comp (seg_widen32 (L := L) (g := g) d hb)
    (seg_fmasT (L := L) (g := g) d 32 (le_refl 32))
  refine SegD.of_len (h.weaken_end fun R hR => holds_overlay hR fun r hr => ?_) rfl
  rw [valueEx_wex_off _ d 32 (live_wex_dead r (by simpa using hr))]

/-! ### One group of the mask on any words -/

/-- **One group of the mask on two four-byte words**: as `seg_maskG`, for the halves `vx`, `vy`
of a pair register whatever they are. -/
theorem seg_maskGV {pc a b c e src pl ph : Nat} {d0 d1 : D} {vx vy : Value} {cl ch : Bool}
    (hu : unpackAt pc a b src = true) (h1 : selpAt (pc + 1) c b ph = true)
    (h2 : selpAt (pc + 2) e a pl = true) (h3 : packAt (pc + 3) src e c 64 = true)
    (hno : ∀ k < 4, Assumptions.emuSites.contains (pc + k) = false)
    (hvx : vx.bytes = 4) (hvy : vy.bytes = 4)
    (hsrc : valueZ L g d0 src = .pair vx vy)
    (hpl : valueZ L g d0 pl = .pred cl) (hph : valueZ L g d0 ph = .pred ch)
    (lsrc : src ∈ Flow.live pc) (lpl : pl ∈ Flow.live (pc + 2)) (lph : ph ∈ Flow.live (pc + 1))
    (lb : b ∈ Flow.live (pc + 1)) (la : a ∈ Flow.live (pc + 2))
    (lc : c ∈ Flow.live (pc + 3)) (le : e ∈ Flow.live (pc + 3))
    (cu : subX (Flow.live (pc + 1)) (Flow.live pc) [a, b] = true)
    (c1 : subX (Flow.live (pc + 1 + 1)) (Flow.live (pc + 1)) [c] = true)
    (c2 : subX (Flow.live (pc + 1 + 1 + 1)) (Flow.live (pc + 1 + 1)) [e] = true)
    (c3 : subX (Flow.live (pc + 1 + 1 + 1 + 1)) (Flow.live (pc + 1 + 1 + 1)) [src] = true)
    (dend : disj (Flow.live (pc + 1 + 1 + 1 + 1)) [a, b, c, e] = true)
    (hnd : [a, b, c, e, src].Nodup) (hp1 : pl ∉ [a, b, c, e, src])
    (hp2 : ph ∉ [a, b, c, e, src])
    (hv : valueZ L g d1 src = joinValue (selV cl vx) (selV ch vy))
    (hfr : ∀ r ∈ Flow.live (pc + 1 + 1 + 1 + 1), r ≠ src → valueZ L g d1 r = valueZ L g d0 r) :
    Seg kernel asms L g 4 pc (factsZ L g pc d0) (pc + 4) (factsZ L g (pc + 4) d1) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hp1 hp2
  obtain ⟨⟨nab, nac, nae, nas⟩, ⟨nbc, nbe, nbs⟩, ⟨nce, ncs⟩, nes, -⟩ := hnd
  obtain ⟨pla, plb, plc, ple, pls⟩ := hp1
  obtain ⟨pha, phb, phc, phe, phs⟩ := hp2
  have hnb : ∀ k, k < 4 → Assumption.SegFreePc asms (pc + k) := fun k hk => segFree (hno k hk)
  have s1 : Seg kernel asms L g 1 pc (factsFrom (Flow.live pc) (valueEx (valueZ L g d0) []))
      (pc + 1) (factsFrom (Flow.live (pc + 1)) (valueEx (valueZ L g d0) [(b, vy), (a, vx)])) := by
    refine Seg.set2 (K := kernel) (unpackAt_spec hu) rfl nab (fun t h => ?_) (subX_cov2 cu)
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact hnb 0 (by omega)
    have hr := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d0) []) lsrc)
    have hr' : t.regs src = some (.pair vx vy) := by
      rw [← hsrc]; exact hr
    exact exec_unpack hS hr' hvx hvy
  have s2 : Seg kernel asms L g 1 (pc + 1)
      (factsFrom (Flow.live (pc + 1)) (valueEx (valueZ L g d0) [(b, vy), (a, vx)]))
      (pc + 1 + 1) (factsFrom (Flow.live (pc + 1 + 1)) (valueEx (valueZ L g d0)
        ([(c, selV ch vy)] ++ [(b, vy), (a, vx)]))) := by
    refine Seg.set1 (K := kernel) (selpAt_spec h1) rfl (fun t h => ?_) (subX_sound c1)
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact hnb 1 (by omega)
    have hrp := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d0)
      [(b, vy), (a, vx)]) lph)
    have hrb := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d0)
      [(b, vy), (a, vx)]) lb)
    rw [valueEx_cons_ne _ _ phb, valueEx_cons_ne _ _ pha, valueEx_nil, hph] at hrp
    rw [valueEx_cons_self] at hrb
    rw [exec_selpI hS hrp hrb hvy]
    rfl
  have s3 : Seg kernel asms L g 1 (pc + 1 + 1)
      (factsFrom (Flow.live (pc + 1 + 1)) (valueEx (valueZ L g d0)
        ([(c, selV ch vy)] ++ [(b, vy), (a, vx)])))
      (pc + 1 + 1 + 1) (factsFrom (Flow.live (pc + 1 + 1 + 1)) (valueEx (valueZ L g d0)
        ([(e, selV cl vx)] ++ ([(c, selV ch vy)] ++ [(b, vy), (a, vx)])))) := by
    refine Seg.set1 (K := kernel) (selpAt_spec h2) rfl (fun t h => ?_) (subX_sound c2)
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact hnb 2 (by omega)
    have hrp := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d0)
      ([(c, selV ch vy)] ++ [(b, vy), (a, vx)])) lpl)
    have hra := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d0)
      ([(c, selV ch vy)] ++ [(b, vy), (a, vx)])) la)
    rw [List.singleton_append, valueEx_cons_ne _ _ plc, valueEx_cons_ne _ _ plb,
      valueEx_cons_ne _ _ pla, valueEx_nil, hpl] at hrp
    rw [List.singleton_append, valueEx_cons_ne _ _ nac, valueEx_cons_ne _ _ nab,
      valueEx_cons_self] at hra
    rw [exec_selpI hS hrp hra hvx]
    rfl
  have s4 : Seg kernel asms L g 1 (pc + 1 + 1 + 1)
      (factsFrom (Flow.live (pc + 1 + 1 + 1)) (valueEx (valueZ L g d0)
        ([(e, selV cl vx)] ++ ([(c, selV ch vy)] ++ [(b, vy), (a, vx)]))))
      (pc + 1 + 1 + 1 + 1) (factsFrom (Flow.live (pc + 1 + 1 + 1 + 1)) (valueEx (valueZ L g d0)
        ([(src, joinValue (selV cl vx) (selV ch vy))] ++
          ([(e, selV cl vx)] ++ ([(c, selV ch vy)] ++ [(b, vy), (a, vx)]))))) := by
    have hc : kernel.code[pc + 1 + 1 + 1]? = some ⟨none, .move
        ⟨.pack, .int .b 64, [some src], [.reg e, .reg c]⟩⟩ := packAt_spec h3
    refine Seg.set1 (K := kernel) hc rfl (fun t h => ?_) (subX_sound c3)
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact hnb 3 (by omega)
    have hA := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d0)
      ([(e, selV cl vx)] ++ ([(c, selV ch vy)] ++ [(b, vy), (a, vx)]))) le)
    have hB := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d0)
      ([(e, selV cl vx)] ++ ([(c, selV ch vy)] ++ [(b, vy), (a, vx)]))) lc)
    rw [List.singleton_append, valueEx_cons_self] at hA
    rw [List.singleton_append, valueEx_cons_ne _ _ nce, List.singleton_append,
      valueEx_cons_self] at hB
    exact exec_pack hS (Or.inr rfl) hA hB (selV_bytes hvx) (selV_bytes hvy)
  have s := ((s1.comp s2).comp s3).comp s4
  refine Seg.of_len (Seg.overlay_end s fun r hr => ?_) rfl
  by_cases hrs : r = src
  · subst hrs
    rw [hv]
    simp only [List.singleton_append, valueEx_cons_self]
  · have hn := disj_sound dend r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [List.singleton_append, valueEx_cons_ne _ _ hrs, valueEx_cons_ne _ _ hn.2.2.2,
      valueEx_cons_ne _ _ hn.2.2.1, valueEx_cons_ne _ _ hn.2.1, valueEx_cons_ne _ _ hn.1,
      valueEx_nil]
    exact hfr r hr hrs

/-! ### The masked states -/

theorem maskedT_zero (d : D) : D.maskedT L g d 0 = d.scoredT 32 := by
  have : mSvT L g d 0 = scSvT d 32 := by
    funext k
    simp [mSvT, msk]
  simp only [D.maskedT, D.scoredT, this]

theorem hW_pair {a b : Value} (k : Nat) :
    hW (.pair a b) k = if k % 2 = 0 then a else b := by
  simp [hW, splitValue]

theorem maskedT_src (d : D) {i : Nat} (hi : i < 32) :
    valueZ L g (D.maskedT L g d i) (2447 + po i) = d.scP (po i) := by
  have hq : po i < 32 := by unfold po; split_ifs <;> omega
  rw [valueZ_pair _ hq, valueOf_svp _ hq]
  simp only [D.maskedT, mSvT, show 2 * po i / 2 = po i by omega,
    show (2 * po i + 1) / 2 = po i by omega, msk_po, scSvT, show po i < 32 from hq, ↓reduceIte,
    Bool.false_eq_true]
  have e0 : slW (d.scP (po i)) (2 * po i) = slW (d.scP (po i)) 0 := by simp [slW]
  have e1 : slW (d.scP (po i)) (2 * po i + 1) = slW (d.scP (po i)) 1 := by simp [slW]
  rw [e0, e1]
  exact joinValue_slices (scP_bytes d _)

theorem maskedT_dst (d : D) {i : Nat} (hi : i < 32) :
    valueZ L g (D.maskedT L g d (i + 1)) (2447 + po i) =
      joinValue (mwT L g d (2 * po i)) (mwT L g d (2 * po i + 1)) := by
  have hq : po i < 32 := by unfold po; split_ifs <;> omega
  rw [valueZ_pair _ hq, valueOf_svp _ hq]
  simp only [D.maskedT, mSvT, show 2 * po i / 2 = po i by omega,
    show (2 * po i + 1) / 2 = po i by omega, msk_po_succ, ↓reduceIte]

theorem valueOf_maskedT_step (d : D) {i : Nat} (hi : i < 32) {r : Nat}
    (hr : ¬ (876 ≤ r ∧ r < 876 + 64)) (hne : r ≠ 2447 + po i) :
    valueOf L g (D.maskedT L g d (i + 1)) r = valueOf L g (D.maskedT L g d i) r := by
  by_cases h : 2447 ≤ r ∧ r < 2447 + 32
  · obtain ⟨q, rfl⟩ : ∃ q, r = 2447 + q := ⟨r - 2447, by omega⟩
    rw [valueOf_svp _ (by omega), valueOf_svp _ (by omega)]
    have h2 : ∀ k, k / 2 = q → mSvT L g d (i + 1) k = mSvT L g d i k := by
      intro k hk
      unfold mSvT
      rw [hk, msk_succ_ne (by omega)]
    simp only [D.maskedT]
    rw [h2 (2 * q) (by omega), h2 (2 * q + 1) (by omega)]
  · exact valueOf_frameSv (L := L) (g := g) (d := D.maskedT L g d i)
      (d' := D.maskedT L g d (i + 1)) rfl rfl rfl rfl rfl rfl rfl hr h

theorem maskedT_step (d : D) {i : Nat} (hi : i < 32) {r : Nat}
    (hr : ¬ (876 ≤ r ∧ r < 876 + 64)) (hne : r ≠ 2447 + po i) :
    valueZ L g (D.maskedT L g d (i + 1)) r = valueZ L g (D.maskedT L g d i) r := by
  unfold valueZ
  rw [show valuesZ L g (D.maskedT L g d (i + 1)) = valuesZ L g d from rfl,
    show valuesZ L g (D.maskedT L g d i) = valuesZ L g d from rfl,
    valueOf_maskedT_step d hi hr hne]

/-- The predicates of the group `i`, in any state. -/
theorem mask_predsG (d : D) {i : Nat} (hi : i < 32) :
    valueZ L g d (mpl i) = .pred (visK d.e (g % L.block) d.n (2 * po i)) ∧
    valueZ L g d (mph i) = .pred (visK d.e (g % L.block) d.n (2 * po i + 1)) := by
  by_cases h0 : i = 0
  · subst h0
    simp only [mpl, mph, po, ↓reduceIte, valueZ]
    refine ⟨?_, ?_⟩ <;> simp only [valuesZ, PTX.Flow.lookupLit, Option.getD_some]
  by_cases h1 : i = 1
  · subst h1
    simp only [mpl, mph, po, ↓reduceIte, valueZ]
    refine ⟨?_, ?_⟩ <;> simp only [valuesZ, PTX.Flow.lookupLit, Option.getD_some] <;> rfl
  have h2 : 2 ≤ i := by omega
  have a := valueZ_pred_lo d (L := L) (g := g) h2 hi
  have b := valueZ_pred_hi d (L := L) (g := g) h2 hi
  simp only [mpl, mph, po, h0, h1, ↓reduceIte]
  exact ⟨a, b⟩

/-- **One group of the mask on any S words, at every index.** -/
theorem seg_maskIT (d : D) {i : Nat} (hi : i < 32) :
    Seg kernel asms L g 4 (1628 + 4 * i) (factsZ L g (1628 + 4 * i) (D.maskedT L g d i))
      (1628 + 4 * i + 4) (factsZ L g (1628 + 4 * i + 4) (D.maskedT L g d (i + 1))) := by
  obtain ⟨hu, h1, h2, h3⟩ := mask_code i hi
  obtain ⟨lsrc, lpl, lph, lb, la, lc, le⟩ := mask_live1 i hi
  obtain ⟨cu, c1, c2, c3, dend⟩ := mask_live2 i hi
  obtain ⟨hnd, hp1, hp2⟩ := mask_dist i hi
  obtain ⟨hpl, hph⟩ := mask_predsG (L := L) (g := g) (D.maskedT L g d i) hi
  obtain ⟨a, b, hab, ha, hb⟩ := scP_pair d (po i)
  have hdst := maskedT_dst (L := L) (g := g) d hi
  have e0 : mwT L g d (2 * po i) = selV (visK d.e (g % L.block) d.n (2 * po i)) a := by
    simp only [mwT, show 2 * po i / 2 = po i by omega, hab, hW_pair]
    simp
  have e1 : mwT L g d (2 * po i + 1) =
      selV (visK d.e (g % L.block) d.n (2 * po i + 1)) b := by
    simp only [mwT, show (2 * po i + 1) / 2 = po i by omega, hab, hW_pair]
    simp
  rw [e0, e1] at hdst
  exact seg_maskGV (L := L) (g := g) (d0 := D.maskedT L g d i) (d1 := D.maskedT L g d (i + 1))
    hu h1 h2 h3 (mask_emu i hi) ha hb (by rw [maskedT_src d hi, hab]) hpl hph lsrc lpl lph lb la
    lc le cu c1 c2 c3 dend hnd hp1 hp2 hdst
    (fun r hr hne => maskedT_step d hi (mask_dead i hi r hr) hne)

/-- **The first `m` groups of the mask on any S words.** -/
theorem seg_masksT (d : D) : ∀ m, m ≤ 32 →
    Seg kernel asms L g (4 * m) 1628 (factsZ L g 1628 (D.maskedT L g d 0)) (1628 + 4 * m)
      (factsZ L g (1628 + 4 * m) (D.maskedT L g d m)) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih =>
    exact fun hm => Seg.of_len ((ih (by omega)).comp (seg_maskIT d (i := m) (by omega)))
      (by omega)

/-- **The visibility mask on any S words** (pcs 1628 to 1755). -/
theorem seg_mask32T (d : D) :
    Seg kernel asms L g 128 1628 (factsZ L g 1628 (d.scoredT 32)) 1756
      (factsZ L g 1756 (D.maskedT L g d 32)) := by
  have := seg_masksT (L := L) (g := g) d 32 (le_refl 32)
  rw [maskedT_zero] at this
  exact Seg.of_len this rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm

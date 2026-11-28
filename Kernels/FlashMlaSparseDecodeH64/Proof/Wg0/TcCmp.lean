-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TcOrd
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarPlace

@[expose] public section

/-! # Comparing warpgroup 0's collective counts by place

For `d` at a collective site and `s` at a place no earlier, both of one CTA (the same blocks):

* `vOrd_le_of`: `s` has made at least `d`'s votes;
* `tcOrd_le_of`: with `H` the arms of the blocks by the vote results `V` (`hH`) and both vote
  words `V`'s (`VtOk`), `s` has made more collectives than `d`, or as many when it is at `d`'s
  place, itself at a collective site.

The proof reads both states as a region, a block and an order (`form`), and the collective sites
by their order (`tc_sites`, `tc_of_ord`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {L : Launch} {g g' : Nat}

/-- The order of a state in its region. -/
abbrev oo (d : D) : Nat := d.site.ord + elOff d

/-- The base of the epilogue's counts. -/
abbrev eb (d : D) (H : Nat → Nat) : Nat := 3 * rounds d.l0 d.l1 + 16 * H (rounds d.l0 d.l1)

/-- **A state as a region, block and order.** -/
private theorem form {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) :
    (d.site.reg = .setup ∧ place d ≤ 5) ∨
    (∃ r, d.site.reg = .loop ∧ r < rounds d.l0 d.l1 ∧ d.bi.toNat = r + 1 ∧
      scmpi .eq .b d.bi 1 = decide (r = 0) ∧
      place d = wg0Blk0 + stride * r + oo d ∧ oo d ≤ 77 ∧ vOrd d = r +
        (if 38 < d.site.ord then 1 else 0) ∧
      ∀ w H, tcOrd w d H = 3 * r + 16 * H r + locL (oo d) (armV d)) ∨
    (d.site.reg = .epi ∧ d.site ≠ .ebar ∧ place d = wg0EpiBlk0 + stride * rounds d.l0 d.l1 + oo d ∧
      oo d ≤ 162 ∧ vOrd d = rounds d.l0 d.l1 ∧ ∀ w H, tcOrd w d H = eb d H + locE (oo d)) ∨
    (d.site.reg ≠ .setup ∧ vOrd d = rounds d.l0 d.l1 ∧ ∀ w H,
      (d.site = .ebar ∧ place d = endPlace ∧ tcOrd w d H = eb d H + 8) ∨
      (d.site = .dealloc ∧ place d = endPlace + 1 ∧
        tcOrd w d H = eb d H + 8 - (if scmpi .ne .b w 0 then 1 else 0)) ∨
      (d.site = .exit ∧ place d = endPlace + 2 ∧
        tcOrd w d H = eb d H + 8 + (if scmpi .ne .b w 0 then 0 else 1))) := by
  have he := elOff_le d
  have ho := ord_epi_le d.site
  by_cases hx : d.site = .ebar ∨ d.site = .dealloc ∨ d.site = .exit
  · refine .inr (.inr (.inr ⟨?_, ?_, fun w H => ?_⟩))
    · rcases hx with h | h | h <;> simp [h, Site.reg]
    · rcases hx with h | h | h <;> simp [vOrd, h, Site.reg]
    · rcases hx with h | h | h <;> simp [tcOrd, place, h]
  push Not at hx
  have hp := place_reg hx
  obtain ⟨h1, h2, h3⟩ := hx
  cases hk : d.site.reg with
  | setup => exact .inl ⟨rfl, by rw [hp, hk]; exact (setup_tab _ hk).1⟩
  | loop =>
    simp only [RefCore, hk, RefAt, Control.D.words] at hJ
    obtain ⟨r, hl, -⟩ := hJ
    obtain ⟨-, hR, hr, hbi, -⟩ := hl
    dsimp only at hR hr hbi
    have hb : d.bi.toNat = r + 1 := by rw [hbi]; exact toNat_W (by omega)
    refine .inr (.inl ⟨r, rfl, hr, hb, ?_, ?_, ?_, ?_, fun w H => ?_⟩)
    · rw [hbi, scmpi_eq_b_W (by omega) (by omega) (by omega)]; simp
    · rw [hp, hk, regPlace, hb]; simp only [oo, Nat.add_sub_cancel]; omega
    · have := ord_loop_le _ hk; simp only [oo]; omega
    · simp [vOrd, hk, hb]
    · clear hbi; unfold tcOrd; rw [hb]; split <;> simp_all [oo]
  | epi =>
    refine .inr (.inr (.inl ⟨rfl, h1, by rw [hp, hk, regPlace]; simp only [oo]; omega,
      by simp only [oo]; omega, by simp [vOrd, hk],
      fun w H => by unfold tcOrd; split <;> simp_all [oo, eb]⟩))
  | fin => rcases fin_tab _ hk with h | h <;> contradiction

/-- **The collective sites by their order**: the block's score loads and wait and its arm, the
epilogue's chunk loads and waits, the deallocation. -/
private theorem tc_sites {d : D} (h : d.site.isTc = true) :
    (d.site.reg = .loop ∧ elOff d = 0 ∧ (d.site.isArm = false ∧ 4 ≤ d.site.ord ∧ d.site.ord ≤ 6 ∨
      d.site.isArm = true ∧ 56 ≤ d.site.ord ∧ d.site.ord ≤ 71)) ∨
    (d.site.reg = .epi ∧ d.site ≠ .ebar ∧ elOff d = 0 ∧
      ∃ c < 4, d.site.ord = 7 + 38 * c ∨ d.site.ord = 8 + 38 * c) ∨ d.site = .dealloc := by
  obtain ⟨s, el⟩ := d
  cases s <;> simp only [Site.isTc, Bool.false_eq_true] at h <;>
    simp only [Site.reg, Site.ord, Site.isArm, elOff, chunkBase, reduceCtorEq, true_and,
      false_and, or_false, false_or, Bool.true_eq_false, ne_eq, not_false_eq_true]
  all_goals first
    | (rename_i k; have := k.isLt; omega)
    | (rename_i c; exact ⟨c.val, c.isLt, by omega⟩)
    | omega

set_option linter.unusedTactic false in
/-- **A site at a collective order is collective.** -/
private theorem tc_of_ord {d : D} :
    (d.site.reg = .loop → (4 ≤ oo d ∧ oo d ≤ 6 ∨ 56 ≤ oo d ∧ oo d ≤ 71) →
      d.site.isTc = true ∧ (56 ≤ oo d → d.site.isArm = true)) ∧
    (d.site.reg = .epi → d.site ≠ .ebar → (∃ c < 4, oo d = 7 + 38 * c ∨ oo d = 8 + 38 * c) →
      d.site.isTc = true) := by
  obtain ⟨s, el⟩ := d
  cases s <;> simp only [Site.reg, Site.ord, Site.isArm, Site.isTc, elOff, chunkBase, oo,
    reduceCtorEq, false_implies, and_true, true_and, implies_true, forall_const,
    w0Wv, w0Wq, w0ArrV, w0ArrS, w0ArrL, w0Wsv, ne_eq, not_true_eq_false, not_false_eq_true]
  all_goals first
    | (intro h; omega)
    | (rintro ⟨c', hc, h | h⟩ <;> omega)
    | (rename_i k; have := k.isLt; intro h; omega)

/-- **A collective state as a region, block and order.** -/
private theorem dform {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) (htc : d.site.isTc = true) :
    (∃ r, d.site.reg = .loop ∧ r < rounds d.l0 d.l1 ∧ d.bi.toNat = r + 1 ∧
      scmpi .eq .b d.bi 1 = decide (r = 0) ∧ place d = wg0Blk0 + stride * r + d.site.ord ∧
      vOrd d = r + (if 38 < d.site.ord then 1 else 0) ∧ oo d = d.site.ord ∧
      (∀ w H, tcOrd w d H = 3 * r + 16 * H r + locL d.site.ord (armV d)) ∧
      (d.site.isArm = false ∧ 4 ≤ d.site.ord ∧ d.site.ord ≤ 6 ∨
        d.site.isArm = true ∧ 56 ≤ d.site.ord ∧ d.site.ord ≤ 71)) ∨
    (place d = wg0EpiBlk0 + stride * rounds d.l0 d.l1 + d.site.ord ∧ vOrd d = rounds d.l0 d.l1 ∧
      (∀ w H, tcOrd w d H = eb d H + locE d.site.ord) ∧
      ∃ c < 4, d.site.ord = 7 + 38 * c ∨ d.site.ord = 8 + 38 * c) ∨
    (d.site = .dealloc ∧ place d = endPlace + 1 ∧ vOrd d = rounds d.l0 d.l1 ∧
      ∀ w H, tcOrd w d H = eb d H + 8 - (if scmpi .ne .b w 0 then 1 else 0)) := by
  rcases tc_sites htc with ⟨hk, he, hc⟩ | ⟨hk, hb, he, hc⟩ | hd
  · rcases form hJ with ⟨h, -⟩ | ⟨r, -, hr, hb, hq, hp, -, hv, ht⟩ | ⟨h, -⟩ | ⟨-, -, hE⟩
    · simp [hk] at h
    · simp only [oo, he, Nat.add_zero] at hp ht
      exact .inl ⟨r, hk, hr, hb, hq, hp, hv, by simp [oo, he], fun w H => by rw [ht], hc⟩
    · simp [hk] at h
    · rcases hE 0 (fun _ => 0) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.reg] at hk
  · rcases form hJ with ⟨h, -⟩ | ⟨r, h, -⟩ | ⟨-, -, hp, -, hv, ht⟩ | ⟨-, hv, hE⟩
    · simp [hk] at h
    · simp [hk] at h
    · simp only [oo, he, Nat.add_zero] at hp ht
      exact .inr (.inl ⟨hp, hv, fun w H => by rw [ht], hc⟩)
    · rcases hE 0 (fun _ => 0) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all [Site.reg]
  · rcases form hJ with ⟨h, -⟩ | ⟨r, h, -⟩ | ⟨h, -⟩ | ⟨-, hv, hE⟩
    all_goals try simp [hd, Site.reg] at h
    refine .inr (.inr ⟨hd, ?_, hv, fun w H => ?_⟩)
    · rcases hE 0 (fun _ => 0) with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ <;> simp_all
    · rcases hE w H with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ <;> simp_all

/-- A collective site is off the set-up. -/
theorem tc_reg {d : D} (h : d.site.isTc = true) : d.site.reg ≠ .setup := by
  rcases tc_sites h with ⟨hk, -⟩ | ⟨hk, -⟩ | hk <;> rw [hk] <;> simp [Site.reg]

/-- Off the set-up both lengths are loaded. -/
theorem lens_two {s : Site} (h : s.reg ≠ .setup) : 2 ≤ s.lens := by
  cases s <;> simp_all [Site.reg, Site.lens]

/-- **The collectives before a state read the arms only up to its votes.** -/
theorem tcOrd_congr {w : BitVec 64} {d : D} {H H' : Nat → Nat} (h : ∀ r ≤ vOrd d, H r = H' r) :
    tcOrd w d H = tcOrd w d H' := by
  have hR : d.site.reg ≠ .setup → d.site.reg ≠ .loop →
      H (rounds d.l0 d.l1) = H' (rounds d.l0 d.l1) := fun h1 h2 => by
    apply h; unfold vOrd; split <;> simp_all
  have hL : d.site.reg = .loop → H (d.bi.toNat - 1) = H' (d.bi.toNat - 1) := fun h1 => by
    apply h; simp only [vOrd, h1]; omega
  unfold tcOrd
  split
  all_goals first
    | (split
       · rfl
       · rename_i hk; rw [hL hk]
       · rename_i hk1 hk2; rw [hR (by simp_all) (by simp_all)])
    | (rename_i hs; rw [hR (by simp [hs, Site.reg]) (by simp [hs, Site.reg])])

section
variable {d s : D} {n n' : Cnt → Nat} (hJd : RefCore L g d n) (hJs : RefCore L g' s n')
  (hR : s.site.reg ≠ .setup → rounds s.l0 s.l1 = rounds d.l0 d.l1) (htc : d.site.isTc = true)
  (hle : place d ≤ place s)
include hJd hJs hR htc hle

/-- **A lane no earlier than a collective state has made at least its votes.** -/
theorem vOrd_le_of : vOrd d ≤ vOrd s := by
  have h26 := rounds_lt d.l0 d.l1
  have he := elOff_le s
  rcases form hJs with ⟨hs, hp'⟩ | ⟨r', hs, hr', -, -, hp', ho', hv', -⟩ |
      ⟨hs, -, hp', -, hv', -⟩ | ⟨hs, hv', hE⟩ <;>
    rcases dform hJd htc with ⟨r, -, hr, -, -, hp, hv, -, -, hc⟩ | ⟨hp, hv, -, c, hc, ho⟩ |
      ⟨-, hp, hv, -⟩ <;>
    simp only [wg0Blk0, wg0EpiBlk0, stride, loopBase, wg0Off, w0Epi, wg0Org, endPlace, endSlot,
      blockCap, oo] at *
  all_goals have hRR := hR
  all_goals simp only [hs, ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hRR
  all_goals (try split_ifs at hv hv')
  all_goals omega

set_option linter.unusedSimpArgs false in
/-- **A lane no earlier than a collective state has made more collectives**, or as many at the
state's place, itself at a collective site; `H` counts the arms by the vote results `V`. -/
theorem tcOrd_le_of {w : BitVec 64} {H : Nat → Nat} {V : Nat → Bool}
    (hH : ∀ r, H (r + 1) = H r + if r ≠ 0 ∧ V r = true then 1 else 0)
    (hVd : VtOk d V) (hVs : VtOk s V) (had : ArmOk d)
    (hD : s.site = .dealloc → scmpi .ne .b w 0 = false) :
    place d < place s ∧ tcOrd w d H + 1 ≤ tcOrd w s H ∨
      place s = place d ∧ s.site.isTc = true ∧ tcOrd w d H ≤ tcOrd w s H := by
  have hmono : ∀ a b, a ≤ b → H a ≤ H b := fun a b hab => by
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih => exact Nat.le_trans ih (by rw [Nat.succ_eq_add_one, hH]; omega)
  have h26 := rounds_lt d.l0 d.l1
  have he := elOff_le s
  have hT := tc_of_ord (d := s)
  have hRR := hR
  rcases form hJs with ⟨hs, hp'⟩ | ⟨r', hs, hr', hb', hq', hp', ho', -, ht'⟩ |
      ⟨hs, hb', hp', ho', -, ht'⟩ | ⟨hs, -, hE⟩ <;>
    simp only [hs, ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at hRR
  all_goals rcases dform hJd htc with ⟨r, hk, hr, hb, hq, hp, -, -, ht, hc⟩ |
    ⟨hp, -, ht, c, hc, ho⟩ | ⟨hd, hp, -, ht⟩
  all_goals simp only [wg0Blk0, wg0EpiBlk0, stride, loopBase, wg0Off, w0Epi, wg0Org, endPlace,
    endSlot, blockCap, oo, eb] at *
  all_goals try (exfalso; omega)
  -- the arm of `d`'s block runs when `d` is in it, and `d`'s block adds at most its arm
  all_goals try (
    have hA : d.site.isArm = true → armV d = true ∧ r ≠ 0 ∧ V r = true := fun h => by
      have hv := had h
      have hvt := hVd hk (by
        rcases hc with ⟨h', -⟩ | ⟨-, h', -⟩
        · simp_all
        · omega)
      simp only [hb, Nat.add_sub_cancel] at hvt
      simp only [armV, hq, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
        Bool.not_eq_false] at hv
      exact ⟨had h, hv.1, by rw [← hvt]; simpa using hv.2⟩
    have hstep :
        3 * r + 16 * H r + locL d.site.ord (armV d) + 1 ≤ 3 * (r + 1) + 16 * H (r + 1) := by
      have h1 := hH r
      rcases hc with ⟨h0, h4, h6⟩ | ⟨h0, h56, h71⟩
      · have := hmono r (r + 1) (by omega)
        cases armV d <;> simp only [locL, Bool.false_eq_true, ↓reduceIte] <;> omega
      · obtain ⟨h2, h3, h4⟩ := hA h0
        simp only [h2, locL, h3, h4, ne_eq, not_false_eq_true, and_self, ite_true] at h1 ⊢
        omega)
  · -- `s` in the loop
    by_cases hrr : r < r'
    · have := hmono (r + 1) r' (by omega)
      left; rw [ht, ht']; omega
    obtain rfl : r = r' := by omega
    have hvs : 38 < s.site.ord → s.vt = V r := fun h => by
      have := hVs hs h; rwa [hb', Nat.add_sub_cancel] at this
    rcases hc with ⟨h0, h4, h6⟩ | ⟨h0, h56, h71⟩
    · by_cases ho : d.site.ord < s.site.ord + elOff s
      · left; rw [ht, ht']
        refine ⟨by omega, ?_⟩
        cases armV d <;> cases armV s <;> simp only [locL, Bool.false_eq_true, ↓reduceIte] <;>
          omega
      · right; refine ⟨by omega, (hT.1 hs (by omega)).1, ?_⟩
        rw [ht, ht']
        cases armV d <;> cases armV s <;> simp only [locL, Bool.false_eq_true, ↓reduceIte] <;>
          omega
    · obtain ⟨h2, h3, h4⟩ := hA h0
      have h5 : armV s = true := by
        simp only [armV, hq', hvs (by omega), h3, h4, decide_false, Bool.not_true,
          Bool.or_false, Bool.not_false]
      by_cases ho : d.site.ord < s.site.ord + elOff s
      · left; rw [ht, ht', h2, h5]; simp only [locL, ↓reduceIte]; omega
      · right; refine ⟨by omega, (hT.1 hs (by omega)).1, ?_⟩
        rw [ht, ht', h2, h5]; simp only [locL, ↓reduceIte]; omega
  · -- `s` in the epilogue, `d` in the loop
    have := hmono (r + 1) (rounds s.l0 s.l1) (by omega)
    left; rw [ht, ht']; omega
  · -- both in the epilogue
    rw [hRR] at hp'
    by_cases hlt : d.site.ord < s.site.ord + elOff s
    · left; rw [ht, ht', hRR]; refine ⟨by omega, ?_⟩
      simp only [locE]; omega
    · right; refine ⟨by omega, hT.2 hs hb' ⟨c, hc, by omega⟩, ?_⟩
      rw [ht, ht', hRR]; simp only [locE]; omega
  all_goals rcases hE w H with ⟨hx, hpx, htx⟩ | ⟨hx, hpx, htx⟩ | ⟨hx, hpx, htx⟩
  all_goals simp only [endPlace, endSlot, loopBase, stride, blockCap, wg0Org, hRR] at hpx htx
  all_goals try simp only [hD hx, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at htx
  all_goals try (exfalso; omega)
  all_goals first
    | (have := hmono (r + 1) (rounds d.l0 d.l1) (by omega); left; rw [ht, htx]; omega)
    | (left; rw [ht, htx]; refine ⟨by omega, ?_⟩; simp only [locE]; omega)
    | (right; refine ⟨by omega, by rw [hx]; rfl, ?_⟩; rw [ht, htx]; omega)
    | (left; rw [ht, htx]; refine ⟨by omega, ?_⟩; split_ifs <;> omega)


end

/-- **A collective site is determined by its order**, up to the score loads' arm. -/
theorem tc_ord_inj {s s' : Site} (h : s.isTc = true) (h' : s'.isTc = true)
    (ho : s.ord = s'.ord) : s = s' ∨ ∃ a a' k, s = .sld a k ∧ s' = .sld a' k := by
  cases s <;> simp only [Site.isTc, Bool.false_eq_true] at h <;>
    cases s' <;> simp only [Site.isTc, Bool.false_eq_true] at h' <;>
    simp only [Site.ord, chunkBase] at ho
  all_goals first
    | omega
    | exact .inl rfl
    | exact .inr ⟨_, _, _, rfl, by congr 1; ext; omega⟩
    | exact .inl (by congr 1; ext; omega)

/-- **Two collective states of one CTA at one place are at one site**, up to the score loads'
arm (equal in a warp, `sld_succ`). -/
theorem tc_place_inj {d s : D} {n n' : Cnt → Nat} (hJd : RefCore L g d n)
    (hJs : RefCore L g' s n') (hR : rounds s.l0 s.l1 = rounds d.l0 d.l1)
    (htc : d.site.isTc = true) (hts : s.site.isTc = true) (hp : place d = place s) :
    d.site = s.site ∨ ∃ a a' k, d.site = .sld a k ∧ s.site = .sld a' k := by
  have h26 := rounds_lt d.l0 d.l1
  rcases dform hJd htc with ⟨r, -, hr, -, -, hp1, -, -, -, hc⟩ | ⟨hp1, -, -, c, hc, ho⟩ |
      ⟨hd, hp1, -, -⟩ <;>
    rcases dform hJs hts with ⟨r', -, hr', -, -, hp2, -, -, -, hc'⟩ | ⟨hp2, -, -, c', hc', ho'⟩ |
      ⟨hd', hp2, -, -⟩ <;>
    rw [hp1, hp2] at hp <;>
    simp only [wg0Blk0, wg0EpiBlk0, stride, loopBase, wg0Off, w0Epi, wg0Org, endPlace,
      endSlot, blockCap, hR] at *
  all_goals first
    | (exfalso; omega)
    | exact tc_ord_inj htc hts (by omega)
    | exact .inl (hd.trans hd'.symm)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

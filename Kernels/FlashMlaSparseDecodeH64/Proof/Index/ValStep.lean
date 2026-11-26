-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.ValInv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexAddr
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefNext

@[expose] public section

/-! # The pair words are kept by every step

`ixv_step`: from an index state with the loops' counters in block `i` (`Ctr`) and the pair words
of the block (`IxV`), a step of the machine on an event leads to a state with counters in some block
`i'` and the pair words of it, when the pair load's payload (if the state is a pair load) is the
word of its position (`ixLdWord`). -/

/-! # The pair words across the loops' transitions

`ixv_mainTop`, `ixv_mainEnd`, `ixv_xTop`, `ixv_xEnd`: the machine's loop transitions (`mainTop`,
`mainEnd`, `xTop`, `xEnd`) keep the invariant `IxV` of the next block (`Index/ValInv.lean`). A
block's end moves the next pair `n` (`f`) to the current one and the position word on by 64; the
head loads the next pair only below the loop's count, where the pair's words are those of the
block. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

theorem ixv_ofC_pf {c : IxCtl} {i : Nat} (h : MRow P L g c i) : IxV P L g (ofC (.pf, c)) i :=
  ⟨h, fun h => absurd h (by simp)⟩

theorem ixv_ofC_wA {c : IxCtl} {i : Nat} (h : MRow P L g c i) (hn : NRow P L g c i) :
    IxV P L g (ofC (.wA, c)) i := ⟨h, hn⟩

theorem ixv_ofC_xpf {c : IxCtl} {i : Nat} (h : ERow P L g c (i - nMain c.l0)) :
    IxV P L g (ofC (.xpf, c)) i := ⟨h, fun h => absurd h (by simp)⟩

theorem ixv_ofC_wB {c : IxCtl} {i : Nat} (h : ERow P L g c (i - nMain c.l0))
    (hf : FRow P L g c i) : IxV P L g (ofC (.wB, c)) i := ⟨h, hf⟩

/-- **The main loop's head** keeps the words of block `i`; its branch to `wA` is the loop's last
block. -/
theorem ixv_mainTop {c : IxCtl} {i : Nat} (hi : i < nMin c.l0 c.l1) (hc : c.cnt = W i)
    (hM : MRow P L g c i) : IxV P L g (ofC (mainTop c)) i := by
  have hm := (nMain_bnd c.l0).2.1
  have hmin : nMin c.l0 c.l1 ≤ nMain c.l0 := Nat.min_le_left _ _
  have hw : addi c.cnt 1 = W (i + 1) := by rw [hc]; exact addi1_W (by omega)
  unfold mainTop; dsimp only
  split
  · rename_i h
    have hge : scmp .ge .s (W (i + 1)) (ixNmin c.l0 c.l1) = decide (nMin c.l0 c.l1 ≤ i + 1) := by
      obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
      have := rounds_lt c.l0 c.l1
      rw [(nmin_pos (by simp only [nMin] at hi; omega)).2]
      exact scmp_ge_W (by omega) (by omega)
    rw [hw, hge] at h
    simp only [decide_eq_true_eq] at h
    exact ixv_ofC_wA hM (fun h' => absurd h' (by simp only; omega))
  · exact ixv_ofC_pf hM

/-- The main loop's back-edge test at the end of block `i`: another block follows. -/
theorem neg_test {c : IxCtl} {i : Nat} (h : MainW P L g c i) :
    scmpi .ne .b (addi c.neg 1) 0 = decide (i + 1 ≠ nMin c.l0 c.l1) := by
  obtain ⟨hi, hc, hn, hx, ha⟩ := h
  obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
  have hn1 : addi c.neg 1 = W ((2 ^ 32 - nMin c.l0 c.l1 + (i + 1)) % 2 ^ 32) := by
    rw [hn, addi_Wm (by omega) (by omega)]
    congr 1
    simp only [Int.toNat_one]
    omega
  rw [hn1, scmpi_ne_b_W (by omega) (by omega) (by omega)]
  simp only [Int.toNat_zero, decide_eq_decide]
  simp only [nMin] at hi ⊢
  omega

/-- The position word advances by 64 within the block bound. -/
theorem wpos_next {c : IxCtl} {i : Nat} (hi : i < nMin c.l0 c.l1)
    (hw : c.wpos = W (lane2 L g + 1 + 64 * i)) :
    addi c.wpos 64 = W (lane2 L g + 1 + 64 * (i + 1)) := by
  have hl : tidOf L g % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hm := (nMain_bnd c.l0).2.1
  have hmin : nMin c.l0 c.l1 ≤ nMain c.l0 := Nat.min_le_left _ _
  rw [hw, addi_int (by norm_num) (by norm_num) (by simp only [Int.reduceToNat, lane2]; omega)]
  simp only [Int.reduceToNat]
  congr 1

/-- **The end of main block `i`** keeps the words of block `i + 1`. -/
theorem ixv_mainEnd {c : IxCtl} {i : Nat} (h : MainW P L g c i) (hM : MRow P L g c i)
    (hN : NRow P L g c i) : IxV P L g (ofC (mainEnd c)) (i + 1) := by
  have ht := neg_test h
  obtain ⟨hi, hc, hn, hx, ha⟩ := h
  unfold mainEnd; dsimp only
  rw [ht]
  split
  · rename_i h'
    simp only [decide_eq_true_eq] at h'
    have hlt : i + 1 < nMin c.l0 c.l1 := by omega
    obtain ⟨hn0, hn1⟩ := hN hlt
    exact ixv_mainTop hlt hc ⟨hn0, hn1, wpos_next hi hM.2.2⟩
  · exact ixv_vac (vac_ixMainDone _)

/-- **The extra loop's head** keeps the words of block `i`; its branch to `wB` is the last block. -/
theorem ixv_xTop {c : IxCtl} {i : Nat} (hMR : nMain c.l0 < roundsOf c.l0 c.l1)
    (h2 : i < roundsOf c.l0 c.l1) (hxb : c.xb = W i)
    (hE : ERow P L g c (i - nMain c.l0)) : IxV P L g (ofC (xTop c)) i := by
  have hr2 := (nblk_pos (tot_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hMR))).2.1
  have hw : addi c.xb 1 = W (i + 1) := by rw [hxb]; exact addi1_W (by omega)
  unfold xTop; dsimp only
  split
  · rename_i h
    have hge : scmp .ge .s (W (i + 1)) (ixNblk c.l0 c.l1) =
        decide (roundsOf c.l0 c.l1 ≤ i + 1) := by
      rw [(nmin_pos (by omega)).1]
      exact scmp_ge_W (by omega) (by omega)
    rw [hw, hge] at h
    simp only [decide_eq_true_eq] at h
    exact ixv_ofC_wB hE (fun h' => absurd h' (by simp only; omega))
  · exact ixv_ofC_xpf hE

/-- The extra loop's back-edge test at the end of block `i`. -/
theorem xneg_test {c : IxCtl} {i : Nat} (h : XW L g c i) :
    scmpi .ne .b (addi c.xn 1) 0 = decide (i + 1 ≠ roundsOf c.l0 c.l1) := by
  obtain ⟨hMR, h1, h2, hxb, hxn, hxa⟩ := h
  have hr2 := (nblk_pos (tot_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hMR))).2.1
  have hn1 : addi c.xn 1 = W ((2 ^ 32 - roundsOf c.l0 c.l1 + (i + 1)) % 2 ^ 32) := by
    rw [hxn, addi_Wm (by omega) (by omega)]
    congr 1
    simp only [Int.toNat_one]
    omega
  rw [hn1, scmpi_ne_b_W (by omega) (by omega) (by omega)]
  simp only [Int.toNat_zero, decide_eq_decide]
  omega

/-- **The end of extra block `i`** keeps the words of block `i + 1`. -/
theorem ixv_xEnd {c : IxCtl} {i : Nat} (h : XW L g c i) (hF : FRow P L g c i) :
    IxV P L g (ofC (xEnd c)) (i + 1) := by
  have ht := xneg_test h
  obtain ⟨hMR, h1, h2, hxb, hxn, hxa⟩ := h
  unfold xEnd; dsimp only
  rw [ht]
  split
  · rename_i h'
    simp only [decide_eq_true_eq] at h'
    have hlt : i + 1 < roundsOf c.l0 c.l1 := by omega
    obtain ⟨hf0, hf1⟩ := hF hlt
    exact ixv_xTop hMR hlt hxb ⟨hf0, hf1⟩
  · exact ixv_vac (by simp [Vac])

/-- The lane's first position word. -/
theorem ixPos0_W {m : Mem0} (hp : Pre P L m) (g : Nat) : ixPos0 L g = W (lane2 L g + 1) := by
  have hl := Nat.mod_lt (tidOf L g) (show 0 < 32 by norm_num)
  rw [ixPos0, ixA_lane2 hp]
  have := addi1_W (a := tidOf L g % 32 * 2) (by omega)
  rw [this]
  simp only [lane2]
  congr 1
  omega

/-- **After the main cache's first pair**: the main loop's block `0` (or no block). -/
theorem ixv_afterPre {m : Mem0} (hp : Pre P L m) {c : IxCtl}
    (hm0 : c.m0 = ixWdM P L g (lane2 L g)) (hm1 : c.m1 = ixWdM P L g (lane2 L g + 1)) :
    IxV P L g (ofC (afterPre P L g c)) 0 := by
  unfold afterPre
  split
  · exact ixv_vac (vac_ixNoMain _)
  · rename_i h
    have hR : 0 < roundsOf c.l0 c.l1 := by
      cases ht : scmpi .lt .s (totL c.l0 c.l1) 64
      · exact (nblk_pos ht).1
      · exact absurd (nblk_zero ht).2.1 h
    have h1 : 1 ≤ nMin c.l0 c.l1 := by
      have := (nMain_bnd c.l0).1
      simp only [nMin]; omega
    unfold mainEntry
    refine ixv_mainTop (by simp only; omega) rfl ⟨?_, ?_, ?_⟩
    · simpa using hm0
    · simpa using hm1
    · simp only [Nat.mul_zero, Nat.add_zero]
      exact ixPos0_W hp g

/-- **After the extra cache's first pair**: the extra loop's block `M` (or the barrier). -/
theorem ixv_afterXpre {c : IxCtl} (h : Ctr P L g .xpre c i)
    (he0 : c.e0 = ixWdX P L g (lane2 L g)) (he1 : c.e1 = ixWdX P L g (lane2 L g + 1)) :
    IxV P L g (ofC (afterXpre L g c)) i := by
  obtain ⟨hMR, rfl, hx⟩ := h
  have hR : 0 < roundsOf c.l0 c.l1 := by omega
  obtain ⟨-, hr2, -⟩ := nblk_pos (tot_of_pos hR)
  obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
  have ht : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false := by
    rw [hx, (nmin_pos hR).1, scmp_ge_W (by omega) (by omega)]
    simp only [decide_eq_false_iff_not, not_le]
    exact hMR
  unfold afterXpre
  rw [ht]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine ixv_xTop hMR hMR hx ⟨?_, ?_⟩
  · simpa using he0
  · simpa using he1

/-- The main loop's block is named by its counter. -/
theorem mainW_inj {c : IxCtl} {i i' : Nat} (h : MainW P L g c i) (h' : MainW P L g c i') :
    i = i' := by
  obtain ⟨hi, hc, -⟩ := h
  obtain ⟨hi', hc', -⟩ := h'
  have hm := (nMain_bnd c.l0).2.1
  have h1 : i < nMain c.l0 := lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have h2 : i' < nMain c.l0 := lt_of_lt_of_le hi' (Nat.min_le_left _ _)
  have := congrArg BitVec.toNat (hc.symm.trans hc')
  simp only [toNat_W (show i + 1 < 2 ^ 64 by omega), toNat_W (show i' + 1 < 2 ^ 64 by omega)]
    at this
  omega

/-- The extra loop's block is named by its counter. -/
theorem xw_inj {c : IxCtl} {i i' : Nat} (h : XW L g c i) (h' : XW L g c i') : i = i' := by
  obtain ⟨-, -, hl, hb, -⟩ := h
  obtain ⟨-, -, hl', hb', -⟩ := h'
  have hr := rounds_lt c.l0 c.l1
  have := congrArg BitVec.toNat (hb.symm.trans hb')
  simp only [toNat_W (show i + 1 < 2 ^ 64 by omega), toNat_W (show i' + 1 < 2 ^ 64 by omega)]
    at this
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- A pair load's step: the event's bytes rebuild to the 32-bit word, the successor is `ldNext`. -/
theorem ncPair_some' {e : Event} {d d' : D} {n : BitVec 64 → BitVec 64 → D}
    (h : ncPair e d n = some (some d')) :
    ∃ y ac bs, e.kind = .nc ac bs ∧ rebuild 3 bs = .ok (.bits 32 y) ∧ d' = ldNext d y n := by
  unfold ncPair at h
  split at h
  · rename_i ac bs hk
    split at h
    · rename_i y hy
      exact ⟨y, ac, bs, hk, hy, (Option.some.inj (Option.some.inj h)).symm⟩
    · cases h
    · cases h
  · cases h

theorem poll_cases {e : Event} {d a : D} {s : IxSite} (h : poll e d s = some (some a)) :
    a = d ∨ a = { d with site := s } := by
  unfold poll at h
  split at h
  · rename_i ok
    simp only [Option.some.injEq] at h
    subst h
    split <;> simp_all
  · cases h

theorem lenNext_some {e : Event} {f : BitVec 64 → D} {a : D}
    (h : lenNext e f = some (some a)) : ∃ x, a = f x := by
  unfold lenNext at h
  split at h
  · exact ncNext_some h
  · cases h

/-- **The pair words are kept by every step** the machine follows. -/
theorem ixv_step {m : Mem0} (hp : Pre P L m) {d a : D} {f : Event} {i : Nat}
    (hel : d.el < d.site.elems) (hct : Ctr P L g d.site d.c i) (hV : IxV P L g d i)
    (hpay : ∀ ac bs, f.kind = .nc ac bs → isLd d.site = true →
      rebuild 3 bs = .ok (.bits 32 (ixLdWord P L g d i)))
    (hs : succ P L g d f = some (some a)) :
    ∃ i', Ctr P L g a.site a.c i' ∧ IxV P L g a i' := by
  obtain ⟨site, el, ac, c⟩ := d
  dsimp only at hel hct hV hpay
  cases site with
  | exit => simp [succ] at hs
  | lenA | lenB =>
    simp only [succ] at hs
    obtain ⟨x, rfl⟩ := lenNext_some hs
    first
      | exact ⟨0, ctr_afterA P _, ixv_vac (vac_ixAfterA P _)⟩
      | exact ⟨0, ctr_lens _, ixv_vac (vac_ixLens _)⟩
  | pre | pf | xpre | xpf =>
    simp only [succ] at hs
    obtain ⟨y, ac', bs, hk, hr, rfl⟩ := ncPair_some' hs
    have hy := hpay ac' bs hk rfl
    rw [hr] at hy
    obtain rfl : y = ixLdWord P L g ⟨_, el, ac, c⟩ i := by
      have := Except.ok.inj hy
      exact (Value.bits.inj this).2
    have hel2 : el < 2 := by simpa [IxSite.elems] using hel
    unfold ldNext
    dsimp only
    split
    · obtain rfl : el = 0 := by omega
      refine ⟨i, hct, ?_⟩
      first
        | exact fun _ => rfl
        | exact ⟨hV.1, fun _ => rfl⟩
    · obtain rfl : el = 1 := by omega
      first
        | exact ⟨0, ctr_afterPre hct, ixv_afterPre hp (hV rfl) rfl⟩
        | exact ⟨i, hct.1, hV.1, fun _ => ⟨hV.2 rfl, rfl⟩⟩
        | exact ⟨i, ctr_afterXpre hct, ixv_afterXpre hct (hV rfl) rfl⟩
  | wA | wB =>
    simp only [succ] at hs
    rcases poll_cases hs with rfl | rfl <;> exact ⟨i, hct, hV⟩
  | sA1 | sA2 | sB1 | sB2 =>
    simp only [succ] at hs
    obtain ⟨r, rfl⟩ := shflNext_some hs
    exact ⟨i, hct, hV⟩
  | bA | bB | bar =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact ⟨i, hct, hV⟩
  | stA | stB =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    unfold stNext
    dsimp only
    split
    · exact ⟨i, hct, hV⟩
    · first
        | rcases afterSt_cases (L := L) (g := g) .bA .arrA with h | h <;> rw [h] <;>
            exact ⟨i, hct, hV⟩
        | rcases afterSt_cases (L := L) (g := g) .bB .arrB with h | h <;> rw [h] <;>
            exact ⟨i, hct, hV⟩
  | arrA =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact ⟨i + 1, ctr_mainEnd hct, ixv_mainEnd hct hV.1 hV.2⟩
  | arrB =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact ⟨i + 1, ctr_xEnd hct, ixv_xEnd hct hV.2⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

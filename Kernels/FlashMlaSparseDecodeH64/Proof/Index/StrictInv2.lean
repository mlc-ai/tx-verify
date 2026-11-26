-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefArith
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictEntry

@[expose] public section

/-! # The index machine's invariant

`IxInv`: the invariant of a state of the index machine that the strict chain keeps (`succ_inv`):
the extra length word is nonzero only for a positive `extra_topk` (`ExtraOk`), the extra loop's
counter is the main cache's block count before the extra loop, the element is below the site's,
and the second element of an index pair's load has the first's 32-bit word. `IxWf`: the events'
well-formedness (the loaded words and the shuffled words are 32-bit; the second length's is
positive only for a positive `extra_topk`). -/

/-! # The extra loop's page size is nonzero

`extra_nz`: the extra loop is reached (`scmp .ge .s xb (ixNblk l0 l1) = false` with `xb` the
main cache's block count) only when the extra length word is nonzero, so `extra_topk` is
positive (`Pre.extraPos`) and the page size parameter loads as a nonzero word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

private theorem trunc_lt' (x : BitVec 64) : (truncBits 32 x).toNat < 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]; omega

/-- The padded main length, at least 64 and below `2 ^ 31`. -/
theorem ixMax_bnd (a : BitVec 64) : 64 ≤ (ixMax a).toNat ∧ (ixMax a).toNat < 2 ^ 31 := by
  simp only [ixMax, max32]
  split
  · rename_i h
    have h64 : r32 (i32 64) = W 64 := by decide
    rw [h64] at h
    have hx : (r32 (ixPad a)).toNat < 2 ^ 32 := trunc_lt' _
    simp only [PTX.compare, toSigned, toNat_W (show 64 < 2 ^ 64 by omega),
      decide_eq_true_eq] at h
    split_ifs at h <;> omega
  · decide

/-- A zero length word adds no block: the extra loop's test holds at the main cache's count. -/
theorem ge_of_len_zero {l0 l1 : BitVec 64} (h : r32 l1 = 0) :
    scmp .ge .s (ixNmain l0) (ixNblk l0 l1) = true := by
  obtain ⟨hm1, hm2⟩ := ixMax_bnd l0
  have hp : ixPad l1 = 0 := by
    have : ixPad l1 = andi (add32 (addi l1 63) (shru (shrs (addi l1 63) 31) 26)) (-64) := rfl
    have h63 : addi l1 63 = W 63 := by simp only [addi, h]; decide
    rw [this, h63]; decide
  have hMW : ixMax l0 = W (ixMax l0).toNat := eq_W _
  generalize (ixMax l0).toNat = M at hm1 hm2 hMW
  have ht : totL l0 l1 = W M := by
    rw [totL_eq]
    have : padL l1 = 0 := hp
    rw [this]
    show add32 0 (ixMax l0) = _
    rw [hMW]
    have h0 : (0 : BitVec 64) = W 0 := rfl
    rw [h0]
    w32_norm
  have hn : ixNblk l0 l1 = W (M / 64) := by
    show nblkL l0 l1 = _
    unfold nblkL
    rw [ht]
    w32_norm
  have hm : ixNmain l0 = W (M / 64) := by
    unfold ixNmain
    rw [hMW]
    w32_norm
  rw [hn, hm]
  have hq : M / 64 < 2 ^ 32 := by omega
  simp only [scmp, r32_W hq, PTX.compare, toSigned]
  simp

theorem r32_eq_zero_iff (x : BitVec 64) : r32 x = 0 ↔ x.toNat % 2 ^ 32 = 0 := by
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [r32, truncBits, BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [r32, truncBits, BitVec.toNat_ofNat]
    omega

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The extra length word of the control words**: nonzero only when `extra_topk` is positive. -/
def ExtraOk (P : Params) (c : IxCtl) : Prop :=
  c.l1.toNat % 2 ^ 32 ≠ 0 → 0 < P.extra_topk

theorem extraOk_ctl0 : ExtraOk P (ixCtl0 P) := by
  intro h
  by_contra h0
  have : P.extra_topk = 0 := by omega
  apply h
  simp [pw, this, leNat_eq]

/-- **The extra loop's page size is nonzero**: the loop is reached from the main cache's count
(`xb`) only when the extra length word is nonzero. -/
theorem extra_nz (hp : Pre P L m) {c : IxCtl} (hxb : c.xb = ixNmain c.l0) (hx : ExtraOk P c)
    (h : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false) :
    (pw P.extraPage).toNat % 2 ^ 32 ≠ 0 := by
  have h1 : c.l1.toNat % 2 ^ 32 ≠ 0 := fun h0 => by
    rw [hxb, ge_of_len_zero ((r32_eq_zero_iff _).mpr h0)] at h
    cases h
  obtain ⟨h2, -, -, h3⟩ := hp.extraPos (hx h1)
  exact pw_nz h2 (by have := hp.extraBlockStrideRange; omega)

/-- The words a transition keeps. -/
def Keep (c c' : IxCtl) : Prop := c'.l0 = c.l0 ∧ c'.l1 = c.l1 ∧ c'.xb = c.xb

theorem Keep.refl (c : IxCtl) : Keep c c := ⟨rfl, rfl, rfl⟩

theorem Keep.trans {a b c : IxCtl} (h : Keep a b) (h' : Keep b c) : Keep a c :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem keep_mainTop (c : IxCtl) : Keep c (mainTop c).2 := by
  unfold mainTop; dsimp only; split <;> exact Keep.refl _

theorem keep_mainDone (c : IxCtl) : Keep c (ixMainDone c).2 := by
  unfold ixMainDone; split <;> exact Keep.refl _

theorem keep_noMain (c : IxCtl) : Keep c (ixNoMain c).2 := by
  unfold ixNoMain; exact keep_mainDone _

theorem keep_afterPre (P : Params) (L : Launch) (g : Nat) (c : IxCtl) :
    Keep c (afterPre P L g c).2 := by
  unfold afterPre
  split
  · exact keep_noMain _
  · unfold mainEntry; exact keep_mainTop _

theorem keep_mainEnd (c : IxCtl) : Keep c (mainEnd c).2 := by
  unfold mainEnd
  dsimp only
  split
  · exact keep_mainTop _
  · exact keep_mainDone _

/-- After the lengths: the extra loop's counter is the main cache's block count. -/
theorem lens_xb (c : IxCtl) : (ixLens c).2.l0 = c.l0 ∧ (ixLens c).2.l1 = c.l1 ∧
    (ixLens c).2.xb = ixNmain c.l0 := by
  unfold ixLens
  dsimp only
  split
  · have := keep_noMain { c with xb := ixNmain c.l0, m0 := 0, m1 := 0 }
    exact ⟨this.1, this.2.1, this.2.2⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem l1_xTop (c : IxCtl) : (xTop c).2.l1 = c.l1 := by
  unfold xTop; dsimp only; split <;> rfl

theorem l1_afterXpre (L : Launch) (g : Nat) (c : IxCtl) : (afterXpre L g c).2.l1 = c.l1 := by
  unfold afterXpre
  split
  · rfl
  · rw [l1_xTop]

theorem l1_xEnd (c : IxCtl) : (xEnd c).2.l1 = c.l1 := by
  unfold xEnd; dsimp only
  split
  · rw [l1_xTop]
  · rfl

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0}

/-- The sites before the extra loop's entry: the extra loop's counter is the main cache's count. -/
def mainSite : IxSite → Bool
  | .pre | .pf | .wA | .sA1 | .sA2 | .stA | .bA | .arrA | .xpre => true
  | _ => false

/-- **The invariant of an index state.** -/
structure IxInv (P : Params) (d : D) : Prop where
  extra : ExtraOk P d.c
  xb : mainSite d.site = true → d.c.xb = ixNmain d.c.l0
  el : d.el < d.site.elems
  acc : isLd d.site = true → d.el = 1 → ∃ y0, d.ac = [.bits 32 y0]

/-- **The events' well-formedness**: a loaded word is a 32-bit word (the second length's is
positive only for a positive `extra_topk`), a shuffle receives one. -/
structure IxWf (P : Params) (e : Event) : Prop where
  nc : ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y)
  len : e.pc = 2365 → ∀ x bs y, e.kind = .nc x bs → rebuild 3 bs = .ok (.bits 32 y) →
    y.toNat % 2 ^ 32 ≠ 0 → 0 < P.extra_topk
  shfl : ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok → ∃ y, recv = .bits 32 y

/-- The state at a site's first element, from control words that satisfy the invariant. -/
theorem ixInv_ofC {s : IxSite} {c : IxCtl} (h1 : ExtraOk P c)
    (h2 : mainSite s = true → c.xb = ixNmain c.l0) : IxInv P (ofC (s, c)) :=
  ⟨h1, h2, IxSite.elems_pos s, fun _ h => absurd h Nat.zero_ne_one⟩

theorem ixInv_keep {d : D} {s : IxSite} {c : IxCtl} (h : IxInv P d)
    (hk : Keep d.c c) (hs : mainSite s = true → mainSite d.site = true) :
    IxInv P (ofC (s, c)) := by
  refine ixInv_ofC (fun h0 => h.extra ?_) fun hm => ?_
  · exact (by simpa [hk.2.1] using h0)
  · rw [hk.1, hk.2.2]; exact h.xb (hs hm)

theorem ixInv_lens {c : IxCtl} (h : ExtraOk P c) : IxInv P (ofC (ixLens c)) := by
  obtain ⟨h0, h1, h2⟩ := lens_xb c
  exact ixInv_ofC (fun h' => h (by rw [← h1]; exact h')) fun _ => by rw [h0, h2]

theorem ixInv_afterA {c : IxCtl} (h : ExtraOk P c) : IxInv P (ofC (ixAfterA P c)) := by
  unfold ixAfterA
  split
  · exact ixInv_lens h
  · exact ixInv_ofC h fun hm => by cases hm

/-- A step to another site of a one-element site: the element stays `0`. -/
theorem ixInv_site {d : D} {s : IxSite} (hi : IxInv P d) (h1 : d.site.elems = 1)
    (hs : mainSite s = true → mainSite d.site = true) : IxInv P { d with site := s } := by
  have h0 : d.el = 0 := by have := hi.el; omega
  have h3 : d.el < s.elems := by rw [h0]; exact IxSite.elems_pos s
  exact ⟨hi.extra, fun hm => hi.xb (hs hm), h3, fun _ h => absurd (h0.symm.trans h) Nat.zero_ne_one⟩

/-- A shuffle's step: the next site, the control words keep the counts (only a received word
changes). -/
theorem ixInv_shfl {d : D} {s : IxSite} {c' : IxCtl} (hi : IxInv P d) (h1 : d.site.elems = 1)
    (hk : Keep d.c c') (hs : mainSite s = true → mainSite d.site = true)
    (hl : isLd s = false) : IxInv P { d with site := s, c := c' } := by
  have h := ixInv_keep hi hk hs
  have h0 : d.el = 0 := by have := hi.el; omega
  refine ⟨h.extra, h.xb, by simp only; rw [h0]; exact IxSite.elems_pos s, fun hld _ => ?_⟩
  simp only at hld
  rw [hl] at hld
  cases hld

theorem main_afterXpre (L : Launch) (g : Nat) (c : IxCtl) :
    mainSite (afterXpre L g c).1 = false := by
  unfold afterXpre xTop
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem main_xEnd (c : IxCtl) : mainSite (xEnd c).1 = false := by
  unfold xEnd xTop
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem main_afterSt (L : Launch) (g : Nat) : mainSite (afterSt L g .bB .arrB) = false := by
  unfold afterSt; split <;> rfl

/-- A length load, for the loaded word `y`, continues to `f y`. -/
theorem lenNext_eq {e : Event} {f : BitVec 64 → D} {d' : D}
    (hw : ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y))
    (h : lenNext e f = some (some d')) :
    ∃ x bs y, e.kind = .nc x bs ∧ rebuild 3 bs = .ok (.bits 32 y) ∧ d' = f y := by
  unfold lenNext at h
  split at h
  · rename_i x bs hk
    obtain ⟨y, hy⟩ := hw x bs hk
    unfold Code.ncNext at h
    rw [hy] at h
    simp only [Option.some.injEq] at h
    exact ⟨x, bs, y, hk, hy, h.symm⟩
  · cases h

theorem ld_elems {s : IxSite} (h : isLd s = true) : s.elems = 2 := by
  cases s <;> simp_all [isLd, IxSite.elems]

theorem ixInv_ncPair {e : Event} {d : D} {n : BitVec 64 → BitVec 64 → D} {d' : D}
    (hi : IxInv P d) (hn : ∀ y0 y1, IxInv P (n y0 y1)) (hld : isLd d.site = true)
    (h : ncPair e d n = some (some d')) : IxInv P d' := by
  obtain ⟨y, rfl⟩ := ncPair_some h
  unfold ldNext
  have h2 := ld_elems hld
  have hel := hi.el
  split
  · rename_i hm
    have h0 : d.el = 0 := by omega
    exact ⟨hi.extra, hi.xb, by show d.el + 1 < d.site.elems; omega, fun _ _ => ⟨y, rfl⟩⟩
  · exact hn _ _

theorem ixInv_poll {e : Event} {d : D} {t : IxSite} {d'' : D} (hi : IxInv P d)
    (h1 : d.site.elems = 1) (hs : mainSite t = true → mainSite d.site = true)
    (h : poll e d t = some (some d'')) : IxInv P d'' := by
  unfold poll at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    split
    · exact ixInv_site hi h1 hs
    · exact hi
  · cases h

theorem ixInv_stNext {d n d' : D} (hi : IxInv P d) (hn : IxInv P n) (h2 : d.site.elems = 2)
    (hld : isLd d.site = false) (h : stNext d n = d') : IxInv P d' := by
  subst h
  unfold stNext
  split
  · rename_i hm
    refine ⟨hi.extra, hi.xb, by show d.el + 1 < d.site.elems; omega, fun h => ?_⟩
    simp [hld] at h
  · exact hn

/-- **The invariant is kept by every transition of the machine.** -/
theorem succ_inv {L : Launch} {g : Nat} {d d' : D} {e : Event} (hi : IxInv P d)
    (hw : IxWf P e) (hpc : e.pc = d.site.pc) (h : succ P L g d e = some (some d')) :
    IxInv P d' := by
  obtain ⟨site, el, ac, c⟩ := d
  have hi1 : ExtraOk P c := hi.extra
  cases site <;> simp only [succ] at h
  · -- lenA
    obtain ⟨x, bs, y, -, -, rfl⟩ := lenNext_eq hw.nc h
    exact ixInv_afterA fun h0 => hi1 h0
  · -- lenB
    obtain ⟨x, bs, y, hk, hy, rfl⟩ := lenNext_eq hw.nc h
    refine ixInv_lens fun h0 => ?_
    exact hw.len hpc x bs y hk hy h0
  · exact ixInv_ncPair hi (fun y0 y1 =>
      ixInv_keep hi (keep_afterPre P L g { c with m0 := y0, m1 := y1 }) fun _ => rfl) rfl h
  · exact ixInv_ncPair hi (fun y0 y1 => ixInv_keep (s := .wA) (c := { c with n0 := y0, n1 := y1 })
    hi ⟨rfl, rfl, rfl⟩ fun _ => rfl) rfl h
  · exact ixInv_poll hi rfl (fun _ => rfl) h
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact ixInv_shfl hi rfl ⟨rfl, rfl, rfl⟩ (fun _ => rfl) rfl
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact ixInv_shfl hi rfl ⟨rfl, rfl, rfl⟩ (fun _ => rfl) rfl
  · exact ixInv_stNext hi (ixInv_keep hi (Keep.refl c) fun _ => rfl) rfl rfl
      (Option.some.inj (Option.some.inj h))
  · obtain rfl := Option.some.inj (Option.some.inj h)
    exact ixInv_site hi rfl fun _ => rfl
  · obtain rfl := Option.some.inj (Option.some.inj h)
    exact ixInv_keep hi (keep_mainEnd c) fun _ => rfl
  · refine ixInv_ncPair hi (fun y0 y1 => ixInv_ofC
      (c := (afterXpre L g { c with e0 := y0, e1 := y1 }).2)
      (fun h0 => hi1 (by rw [l1_afterXpre] at h0; exact h0))
      fun hm => by rw [main_afterXpre] at hm; cases hm) rfl h
  · exact ixInv_ncPair hi (fun y0 y1 => ixInv_keep (s := .wB) (c := { c with f0 := y0, f1 := y1 })
    hi ⟨rfl, rfl, rfl⟩ fun hm => by cases hm) rfl h
  · exact ixInv_poll hi rfl (fun hm => by cases hm) h
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact ixInv_shfl hi rfl ⟨rfl, rfl, rfl⟩ (fun hm => by cases hm) rfl
  · obtain ⟨r, rfl⟩ := shflNext_some h
    exact ixInv_shfl hi rfl ⟨rfl, rfl, rfl⟩ (fun hm => by cases hm) rfl
  · exact ixInv_stNext hi (ixInv_keep hi (Keep.refl c) fun hm => by
      rw [main_afterSt] at hm; cases hm) rfl rfl (Option.some.inj (Option.some.inj h))
  · obtain rfl := Option.some.inj (Option.some.inj h)
    exact ixInv_site hi rfl fun hm => by cases hm
  · obtain rfl := Option.some.inj (Option.some.inj h)
    refine ixInv_ofC (fun h0 => hi1 (by rw [l1_xEnd] at h0; exact h0)) fun hm => ?_
    rw [main_xEnd] at hm; cases hm
  · obtain rfl := Option.some.inj (Option.some.inj h)
    exact ixInv_site hi rfl fun hm => by cases hm
  · cases h

/-- **The first state satisfies the invariant.** -/
theorem ixInv_first (P : Params) (L : Launch) (g : Nat) : IxInv P (ofC (ixFirst P L g)) := by
  unfold ixFirst
  dsimp only
  split
  · exact ixInv_ofC extraOk_ctl0 fun hm => by cases hm
  · split
    · exact ixInv_afterA extraOk_ctl0
    · exact ixInv_ofC extraOk_ctl0 fun hm => by cases hm

/-- **The extra loop's entry** (`qk_xentry`'s hypothesis): the page size is nonzero. -/
theorem ix_hz (hp : Pre P L m) {d : D} (hs : d.site = .xpre) (hi : IxInv P d) :
    scmp .ge .s d.c.xb (ixNblk d.c.l0 d.c.l1) = false → (pw P.extraPage).toNat % 2 ^ 32 ≠ 0 :=
  extra_nz hp (hi.xb (by rw [hs]; rfl)) hi.extra

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

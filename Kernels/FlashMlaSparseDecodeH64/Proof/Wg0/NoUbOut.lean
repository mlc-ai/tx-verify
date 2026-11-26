-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NoUbMem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Stage
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.GenericShared
import Lemmas.Flow.UbStop
import Lemmas.Flow.TmplOkMore

@[expose] public section

/-! # Warpgroup 0's states fire no undefined behaviour: the staging stores, the rescale stores,
the vote, the output

The staging stores go through generic pointers of the lane's CTA at aligned bytes; the rescale
arm's Tensor Memory stores need their 64 sources to hold 4-byte values; the vote needs its
predicate; the election, the deallocation and the output's TMA store have operands the set-up
fixes. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- **A weak generic store through a generic shared pointer at an aligned byte of a payload of the
element's width is no fault.** -/
theorem gen_wr_nonub {A : List Assumption} {t : TState} {a : MemAccess} {pc r x off n : Nat}
    {e : Event} {o : Option TState}
    (hk : a.kind = .store) (hsem : a.sem = .weak) (hsp : a.space = none)
    (hb : a.addr.base = .reg r 64) (ho : a.addr.off = (off : Int))
    (hchk : (a.nc || a.hints.globalOnly || a.vec == 8 || (a.vec == 4 && a.elem.width == 64)) =
      false)
    (hr : t.regs r = some (.ptr 64 true (.shared (g / L.block) (g / L.block))
      (BitVec.ofNat 64 x)))
    (hg : g < L.threads ∧ g / L.block < L.grid) (hx : x + off < 2 ^ 32)
    (hrule : a.rule = some .threadAccess) (hloc : a.locSpace? = none)
    (hw : a.elem.width / 8 ≠ 0) (hn : a.elem.width / 8 * a.vec = n)
    (hal : (x + off) % n = 0) (hsub : t.sub < a.srcs.length)
    (hall : ∀ o ∈ a.srcs, ∃ r, o = .reg r)
    (hpay : ∀ r, Opnd.reg r ∈ a.srcs → ∃ v, t.regs r = some v ∧ v.bytes = a.elem.width / 8)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e o) : ∀ f, e.kind ≠ .ub f := by
  intro f he
  have h := fires_ub hf he
  obtain ⟨rr, hr'⟩ := hall _ (List.getElem_mem hsub)
  have hs : a.srcs[t.sub]? = some (.reg rr) := by rw [List.getElem?_eq_getElem hsub, hr']
  obtain ⟨v, hv, hb'⟩ := hpay rr (hr' ▸ List.getElem_mem hsub)
  have hl : accessLoc L g t a = .ok ⟨.shared, g / L.block, x + off⟩ := by
    have h64 : x < 18446744073709551616 := by omega
    have hx' : (BitVec.ofNat 64 x).toNat = x := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
    simp only [accessLoc, hsp, hb, ho, readReg, hr, readSharedAddress, readValue, bind,
      Except.bind, pure, Except.pure, hx', or_true, ite_true, hg, and_self]
    have hlt : x < 2 ^ 32 := by omega
    have hI : (0 : Int) ≤ (x : Int) + (off : Int) ∧ (x : Int) + (off : Int) < 2 ^ 32 := by omega
    have hT : ((x : Int) + (off : Int)).toNat = x + off := by omega
    simp only [hlt, hI, hT, ↓reduceIte, and_self]
  have hal' : ¬ (a.elem.width / 8 = 0 ∨ (x + off) % (a.elem.width / 8 * a.vec) ≠ 0) := by
    subst hn
    intro hh
    rcases hh with hh | hh
    · exact hw hh
    · exact hh hal
  simp only [eventTmpl] at h
  unfold memTmpl at h
  rw [hrule, hloc] at h
  simp only [ite_true] at h
  unfold accessTmpl at h
  rw [hk, accessAcc_of_weak hsem] at h
  simp only [hchk, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, hl, elemAcc,
    hal', pure, Except.pure, hs, readValue, readReg, hv, storeValue_of_bytes hb'] at h
  cases h

/-- The staging pointer of chunk `k` is 16-byte aligned and leaves room for the chunk offsets. -/
theorem stW_bounds (hp : Pre P L m) (ht : tidOf L g < 128) {k : Nat} (hk : k < 8) :
    (∀ o, o % 16 = 0 → (stW L g k + o) % 16 = 0) ∧ ∀ o ≤ 40960, stW L g k + o < 2 ^ 32 := by
  have h := stW_eq (g := g) hp ht hk
  have hS := sharedBase_lt hp
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have hx : (k ^^^ tidOf L g % 8) < 8 := Nat.xor_lt_two_pow (n := 3) hk (Nat.mod_lt _ (by decide))
  rw [h]
  exact ⟨fun o ho => by omega, fun o ho => by omega⟩

theorem noUbAt_ost2 (hp : Pre P L m) (hg : g < L.threads ∧ g / L.block < L.grid) (d : D)
    (hs : ∃ c k, d.site = .ost2 c k) (ht : tidOf L g < 128) : W0NoUbPay P L g w d := by
  obtain ⟨c, k, hs⟩ := hs
  have hb := fun j : Nat => fun hj : j < 8 => stW_bounds (g := g) hp ht hj
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  fin_cases c <;> fin_cases k <;> w0_shapeS
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 0) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 0 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 0 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 1) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 1 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 1 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 2) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 2 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 2 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 3) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 3 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 3 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 4) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 4 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 4 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 5) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 5 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 5 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 6) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 6 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 6 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 7) (off := 0) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 7 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 7 (by decide) |>.1 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 0) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 0 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 0 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 1) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 1 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 1 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 2) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 2 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 2 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 3) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 3 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 3 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 4) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 4 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 4 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 5) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 5 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 5 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 6) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 6 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 6 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 7) (off := 8192) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 7 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 7 (by decide) |>.1 8192 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 0) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 0 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 0 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 1) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 1 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 1 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 2) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 2 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 2 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 3) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 3 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 3 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 4) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 4 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 4 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 5) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 5 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 5 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 6) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 6 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 6 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 7) (off := 32768) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 7 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 7 (by decide) |>.1 32768 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 0) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 0 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 0 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 1) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 1 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 1 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 2) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 2 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 2 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 3) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 3 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 3 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 4) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 4 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 4 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 5) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 5 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 5 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 6) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 6 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 6 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.mem _)) e o at hf
    intro hpay
    exact gen_wr_nonub (x := stW L g 7) (off := 40960) rfl rfl rfl rfl rfl rfl
      (regs_of_factsFrom hF (by decide +kernel)) hg ((hb 7 (by decide)).2 _ (by decide)) (by decide)
      (by decide) (by decide) (by decide) (hb 7 (by decide) |>.1 40960 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf

/-! ### The rescale arm's stores -/

/-- What a Tensor Memory store's payload needs: its sources hold 4-byte values. -/
def PayTc (t : TState) (ins : Instr) : Prop :=
  ∀ ta ss sh, ins.op = .tcSt ta ss sh → ∀ r, Opnd.reg r ∈ ss →
    ∃ v, t.regs r = some v ∧ v.bytes = 4

/-- The obligation of a Tensor Memory store site. -/
abbrev W0NoUbTc (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) : Prop :=
  ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
    (code P L g w).AtD d t → (code P L g w).inv d → kernel.code[(code P L g w).pc d]? = some ins →
    Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o →
    PayTc t ins → ∀ f, e.kind ≠ .ub f

theorem tcst_nonub {A : List Assumption} {t : TState} {ss : List Opnd} {ta a pc : Nat}
    {e : Event} {o : Option TState} (hb : L.block % 32 = 0)
    (hn : TcShape.s32x32b.countOk ss.length = true) (hr : t.regs ta = some (b32 a))
    (ha : a < 2 ^ 16) (hs : TcShape.s32x32b.splitOk a = true)
    (hall : ∀ o ∈ ss, ∃ r, o = .reg r)
    (hpay : ∀ r, Opnd.reg r ∈ ss → ∃ v, t.regs r = some v ∧ v.bytes = 4)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss .s32x32b)) e o) : ∀ f, e.kind ≠ .ub f := by
  intro f he
  obtain ⟨vals, hv, h4⟩ := mapM_regs_ok (L := L) (g := g) (t := t) (ss := ss) (fun p hp => by
    obtain ⟨r, hr'⟩ := hall _ (List.getElem_mem hp)
    obtain ⟨v, hv, hb'⟩ := hpay r (hr' ▸ List.getElem_mem hp)
    exact ⟨r, v, by rw [List.getElem?_eq_getElem hp, hr'], hv, hb'⟩)
  exact tcSt_ok (A := A) hb hn hr (by omega)
    (tcDataAddressOk_of_row_zero hs (Nat.div_eq_of_lt ha)) hv h4 f (fires_ub hf he)

theorem noUbAt_rst (hp : Pre P L m) (d : D) (hs : ∃ c, d.site = .rst c) : W0NoUbTc P L g w d := by
  obtain ⟨c, hs⟩ := hs
  have hb : L.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  fin_cases c <;> w0_shape
  · change Fires _ (eventTmpl _ L g t (.tcSt _ _ _)) e o at hf
    intro hpay
    exact tcst_nonub hb (by decide) (rg 1263) (by decide) (by decide) (by simp)
      (fun r hr => hpay _ _ _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.tcSt _ _ _)) e o at hf
    intro hpay
    exact tcst_nonub hb (by decide) (rg 1392) (by decide) (by decide) (by simp)
      (fun r hr => hpay _ _ _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.tcSt _ _ _)) e o at hf
    intro hpay
    exact tcst_nonub hb (by decide) (rg 1521) (by decide) (by decide) (by simp)
      (fun r hr => hpay _ _ _ rfl r hr) hf
  · change Fires _ (eventTmpl _ L g t (.tcSt _ _ _)) e o at hf
    intro hpay
    exact tcst_nonub hb (by decide) (rg 1650) (by decide) (by decide) (by simp)
      (fun r hr => hpay _ _ _ rfl r hr) hf

/-! ### The vote -/

/-- A full-mask `vote.any` of a predicate register is no fault. -/
theorem vote_any_ok {A : List Assumption} {t : TState} {dv a r : Nat} {neg : Bool}
    {ty : Option DType} {p : Bool} (hr : t.regs r = some (b32 4294967295))
    (hp : t.regs a = some (.pred p)) (hw : warpSize L g = 32) (f : Fault) :
    eventTmpl A L g t (.warp ⟨.vote .any neg, ty, [some dv], [.reg a], some (.reg r)⟩) ≠
      .ub f := by
  have hm := electMember_full (Nat.mod_lt (g % L.block) (show 0 < 32 by decide))
  have hw' : maskInWarp L g 4294967295 := by
    unfold maskInWarp; rw [hw]; decide
  have hw2 : (truncBits 32 (BitVec.ofNat 64 4294967295)).toNat = 4294967295 := by decide
  have hw : eventTmpl A L g t (.warp ⟨.vote .any neg, ty, [some dv], [.reg a], some (.reg r)⟩) =
      voteModeTmpl L g t .any dv a neg (.reg r) := rfl
  rw [hw]
  simp only [voteModeTmpl, readBits, readReg, readPred, hr, hp, b32, bind, Except.bind, pure,
    Except.pure, hw2]
  simp [PTX.laneOf, hm, hw']

/-- Every lane of a launch of the kernel's blocks is in a whole warp. -/
theorem warpSize_eq (hp : Pre P L m) : warpSize L g = 32 := by
  unfold warpSize
  rw [hp.block]
  omega

/-- What the vote's payload needs: its predicate register holds a predicate. -/
def PayVote (t : TState) (ins : Instr) : Prop :=
  ∀ wi, ins.op = .warp wi → ∀ r, Opnd.reg r ∈ wi.srcs → ∃ p, t.regs r = some (.pred p)

/-- The obligation of the vote. -/
abbrev W0NoUbVote (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) : Prop :=
  ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
    (code P L g w).AtD d t → (code P L g w).inv d → kernel.code[(code P L g w).pc d]? = some ins →
    Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o →
    PayVote t ins → ∀ f, e.kind ≠ .ub f

theorem noUbAt_vote (hp : Pre P L m) (d : D) (hs : d.site = .vote) : W0NoUbVote P L g w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  intro hpay f hk
  obtain ⟨pr, hpr⟩ := hpay _ rfl 109 (by simp)
  exact vote_any_ok (rg 1112) hpr (warpSize_eq hp) f (fires_ub hf hk)

/-! ### The output -/

theorem noUbAt_oel (d : D) (hs : ∃ c, d.site = .oel c) : W0NoUbAt P L g w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c <;> w0_shape
  · exact fun f hk => elect_ok (rg 1912) f (fires_ub hf hk)
  · exact fun f hk => elect_ok (rg 2081) f (fires_ub hf hk)
  · exact fun f hk => elect_ok (rg 2250) f (fires_ub hf hk)
  · exact fun f hk => elect_ok (rg 2420) f (fires_ub hf hk)

theorem noUbAt_dealloc (hp : Pre P L m) (d : D) (hs : d.site = .dealloc) :
    W0NoUbAt P L g w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact fun f hk => tcDealloc_ok (by rw [hp.block]) (rg 2427) (rg 2428) f (fires_ub hf hk)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

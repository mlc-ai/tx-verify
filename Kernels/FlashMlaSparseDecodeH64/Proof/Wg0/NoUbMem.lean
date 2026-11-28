-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Shape
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PollNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Lemmas.Flow.Step.RdNoUb
import Lemmas.Flow.Step.ShapeAsync
import Lemmas.Flow.StoreSrc
import Lemmas.Flow.TmplOkMore
import Lemmas.Flow.UbStop

@[expose] public section

/-! # Warpgroup 0's states fire no undefined behaviour: the shared reads and writes

The words of the row's address registers name workspace offsets (`Wg0/Addr.lean`) that are
multiples of the access, so an access of the table (`RdAt`, `WrAt`) is no fault; a store also
needs its payload registers to hold values of the element's width (`PayMem`). -/

/-! # Warpgroup 0's states fire no undefined behaviour: the control sites

`W0NoUbAt P L g w d`: the event fired from a state of the control machine at the site of `d` is no
fault. The sites whose row of the shape table (`EvK`) has no fault alternative are no fault by the
table (`noUbAt_pure`); the others need the address or the pointer the state's words fix. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The obligation of one site: the event is no fault. -/
abbrev W0NoUbAt (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) : Prop :=
  (code P L g w).ShapeAt (fun _ e => ∀ f, e.kind ≠ .ub f) d

/-- The sites whose row of the shape table has no fault alternative. -/
def Site.pure : Site → Bool
  | .smr | .bwait | .bar0 | .bar2 | .ebar0 | .ebar1 | .obar _ | .bar1 | .ebar | .tcfa | .rsf
  | .efa | .tcfb | .rsfb | .fpx | .ofpx _ | .sldw | .rldw _ | .oldw _ | .commit | .exit => true
  | _ => false

theorem noUbAt_pure (hp : Pre P L m) (d : D) (hs : d.site.pure = true) : W0NoUbAt P L g w d := by
  intro t ins e o hat hi hc hf f hk
  have h := shapeK hp hat hi hc hf
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp_all [Site.pure, EvK]

/-! ### The mbarrier sites -/

/-- A release arrival through a register holding an 8-aligned word is no fault. -/
theorem arrive_nonub {A : List Assumption} {t : TState} {base pc : Nat} {e : Event}
    {o : Option TState} {x : BitVec 64}
    (hb : t.regs base = some (.bits 32 x))
    (hal : (smLoc L g x 0).addr % 8 = 0)
    (hf : Fires pc (eventTmpl A L g t
      (.mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  intro f hk
  have hm := mbarLoc_bits (L := L) (g := g) (t := t) (off := 0) hb hal
  have h0 : readBits L g t 32 (.imm 0) = .ok (truncBits 32 (BitVec.ofInt 64 0)) := by
    simp [readBits, pure, Except.pure]
  have h1 : readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) := by
    simp [readBits, pure, Except.pure]
  exact arrive_loc_ok (cluster := false) (tx := .imm 0) (count := .imm 1) hm h0 h1 f
    (fires_ub hf hk)

/-- The word of a ring slot, `c` bytes above the slot `j`'s place, is 8-byte aligned. -/
theorem slot_al (hp : Pre P L m) {j c : Nat} (hj : j < 4) (hc : c + 8 * j ≤ 222944)
    (h8 : c % 8 = 0) : (smLoc L g (slotW L (W j) c) 0).addr % 8 = 0 := by
  rw [smLoc_slotW hp hj hc]
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  simp only
  omega

/-- The words of the ring sites are 8-byte aligned (`SlotOk` for the slot-indexed ones). -/
theorem arrW_al (hp : Pre P L m) : (smLoc L g (arrW L) 0).addr % 8 = 0 := by
  have h := smLoc_base (g := g) hp (c := 222768) (by decide)
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  simp only [Nat.cast_ofNat] at h
  change (smLoc L g (addi (sbw L) 222768) 0).addr % 8 = 0
  rw [h]
  show (L.sharedBase + 222768) % 8 = 0
  omega

theorem noUbAt_arrL (hp : Pre P L m) (d : D) (hs : d.site = .arrL) : W0NoUbAt P L g w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact arrive_nonub (rg 938) (arrW_al hp) hf

theorem noUbAt_ringV (hp : Pre P L m) (d : D) (hs : d.site = .wv ∨ d.site = .arrV)
    (hv : ∃ v < 4, d.vs = W v) : W0NoUbAt P L g w d := by
  obtain ⟨v, hv4, hvs⟩ := hv
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain rfl : vs = W v := hvs
  rcases hs with hs | hs <;> cases hs <;> w0_shape
  · exact poll_nonub (by rw [hpc]; decide) (rg 974) (rg 975)
      (slot_al hp (c := 222840) hv4 (by omega) (by omega)) hf
  · exact arrive_nonub (rg 1000) (slot_al hp (c := 222872) hv4 (by omega) (by omega)) hf

theorem noUbAt_ringS (hp : Pre P L m) (d : D)
    (hs : d.site = .wq ∨ d.site = .arrS ∨ d.site = .wsv) (hb : ∃ b < 2, d.sl = W b) :
    W0NoUbAt P L g w d := by
  obtain ⟨b, hb2, hsl⟩ := hb
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain rfl : sl = W b := hsl
  rcases hs with hs | hs | hs <;> cases hs <;> w0_shape
  · exact poll_nonub (by rw [hpc]; decide) (rg 977) (rg 978)
      (slot_al hp (c := 222904) (by omega) (by omega) (by omega)) hf
  · exact arrive_nonub (rg 1717) (slot_al hp (c := 222920) (by omega) (by omega) (by omega)) hf
  · exact poll_nonub (by rw [hpc]; decide) (rg 1736) (rg 2954)
      (slot_al hp (c := 222936) (by omega) (by omega) (by omega)) hf

/-! ### The loads through the launch's pointers -/

/-- The pointers the state's site loads through are set. -/
def PtrOk (P : Params) (d : D) : Prop :=
  (d.site = .sink → eqz64 (pw8 (P.sinkBase.getD 0)) = false) ∧
    (d.site = .lenA → eqz64 (pw8 (P.topkLenBase.getD 0)) = false) ∧
    (d.site = .lenB → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false)

theorem noUbAt_nc (hp : Pre P L m) (d : D) (hl : PtrOk P d)
    (hs : d.site = .sink ∨ d.site = .lenA ∨ d.site = .lenB) : W0NoUbAt P L g w d := by
  intro t ins e o hat hi hc hf
  obtain ⟨h0, h1, h2⟩ := hl
  rcases hs with hs | hs | hs
  · obtain ⟨x, hx⟩ := len_ptr (h0 hs)
    obtain ⟨bs, hk, -⟩ := sink_read hp hx hs hat hi hc hf
    rw [hk]; intro f h; cases h
  · obtain ⟨x, hx⟩ := len_ptr (h1 hs)
    obtain ⟨bs, hk, -⟩ := topk_read hp hx hs hat hi hc hf
    rw [hk]; intro f h; cases h
  · obtain ⟨x, hx⟩ := len_ptr (h2 hs)
    obtain ⟨bs, hk, -⟩ := extra_read hp hx hs hat hi hc hf
    rw [hk]; intro f h; cases h

/-! ### The Tensor Memory sites -/

/-- A `32x32b` Tensor Memory load at a column below `2 ^ 16` (lane field zero) is no fault. -/
theorem tcld_nonub {A : List Assumption} {t : TState} {ds : List Nat} {ta a pc : Nat} {e : Event}
    {o : Option TState} (hb : L.block % 32 = 0) (hn : TcShape.s32x32b.countOk ds.length = true)
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 16) (hs : TcShape.s32x32b.splitOk a = true)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta .s32x32b none)) e o) :
    ∀ f, e.kind ≠ .ub f := fun f hk =>
  tcLd_ok hb hn hr (by omega) (tcDataAddressOk_of_row_zero hs (Nat.div_eq_of_lt ha)) f
    (fires_ub hf hk)

theorem noUbAt_tcld (hp : Pre P L m) (d : D)
    (hs : (∃ a k, d.site = .sld a k) ∨ (∃ c, d.site = .rld c) ∨ ∃ c, d.site = .old c) :
    W0NoUbAt P L g w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  have hb : L.block % 32 = 0 := by rw [hp.block]
  rcases hs with ⟨a, k, hs⟩ | ⟨c, hs⟩ | ⟨c, hs⟩ <;> cases hs
  · cases a <;> fin_cases k <;> w0_shape
    · exact tcld_nonub hb (by decide) (rg 986) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 987) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 984) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 985) (by decide) (by decide) hf
  · fin_cases c <;> w0_shape
    · exact tcld_nonub hb (by decide) (rg 1263) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 1392) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 1521) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 1650) (by decide) (by decide) hf
  · fin_cases c <;> w0_shape
    · exact tcld_nonub hb (by decide) (rg 1809) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 1980) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 2150) (by decide) (by decide) hf
    · exact tcld_nonub hb (by decide) (rg 2319) (by decide) (by decide) hf

theorem noUbAt_rstw (hp : Pre P L m) (d : D) (hs : ∃ c, d.site = .rstw c) : W0NoUbAt P L g w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c <;> w0_shape <;>
    exact fun f hk => plainOk_tmpl (by rw [hp.block]) rfl f (fires_ub hf hk)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- A word naming a workspace offset that is a multiple of `n` is `n`-byte aligned. -/
theorem wsLoc_al (hp : Pre P L m) {x : BitVec 64} {off : Int} {c o n : Nat}
    (h : smLoc L g x off = wsLoc L c o) (hn : n ∣ 1024) (ho : n ∣ o) :
    (smLoc L g x off).addr % n = 0 := by
  rw [h]
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  show (L.sharedBase + o) % n = 0
  rw [h2]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hn (Nat.dvd_of_mod_eq_zero h1)) ho)

/-- `fires_rd_nonub` with the access size named. -/
theorem rd_nonub' {t : TState} {w base pc n : Nat} {ds : List Nat} {off : Int} {x : BitVec 64}
    {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 32 x)) (hw : w / 8 ≠ 0)
    (hn : w / 8 * ds.length = n) (hal : (smLoc L g x off).addr % n = 0)
    (hf : Fires pc (loadTmpl Assumptions.all L g t .shared false w ds base off) e o) :
    ∀ f, e.kind ≠ .ub f := by
  subst hn
  exact fires_rd_nonub hr hw hal hf

theorem noUbAt_vm (hp : Pre P L m) (d : D) (hs : d.site = .vm) (hw : w = warpW L g)
    (ht : tidOf L g < 128) (hv : ∃ v < 4, d.vs = W v) : W0NoUbAt P L g w d := by
  obtain ⟨v, hv4, hvs⟩ := hv
  have hal := wsLoc_al hp (vm_loc hp ht hvs hv4) (n := 4) (by decide) (by omega)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  subst hw
  cases hs
  w0_shapeS
  change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
  exact rd_nonub' (rg 1001) (by decide) (by decide) hal hf

theorem xor4 (a : Nat) : (4 * a ^^^ 256) % 4 = 0 := by
  have h := Nat.xor_mod_two_pow (n := 2) (a := 4 * a) (b := 256)
  rw [h, Nat.mul_mod_right]
  norm_num

theorem noUbAt_row (hp : Pre P L m) (d : D) (hs : d.site = .mld ∨ d.site = .eld)
    (hw : w = warpW L g) (ht : tidOf L g < 128) : W0NoUbAt P L g w d := by
  have hal := wsLoc_al hp (r14_loc (g := g) hp ht) (n := 4) (by decide)
    (by have := xor4 (tidOf L g); omega)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  subst hw
  rcases hs with hs | hs <;> cases hs <;> w0_shapeS <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 472) (by decide) (by decide) hal hf

theorem noUbAt_pld (hp : Pre P L m) (d : D) (hs : ∃ k, d.site = .pld k)
    (hw : w = warpW L g) (ht : tidOf L g < 128) : W0NoUbAt P L g w d := by
  obtain ⟨k, hs⟩ := hs
  have hal : ∀ j : Nat, j < 8 →
      (smLoc L g (r17W L g (warpW L g)) (204800 + 512 * (j : Int))).addr % 16 = 0 :=
    fun j hj => wsLoc_al hp (r17_loc (g := g) hp ht hj) (n := 16) (by decide) (by omega)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  subst hw
  cases hs
  fin_cases k <;> w0_shapeS
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 0 (by decide)) hf
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 1 (by decide)) hf
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 2 (by decide)) hf
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 3 (by decide)) hf
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 4 (by decide)) hf
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 5 (by decide)) hf
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 6 (by decide)) hf
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact rd_nonub' (rg 475) (by decide) (by decide) (hal 7 (by decide)) hf

/-! ### The stores -/

/-- What a store's payload needs: its source registers hold values of the element's width. -/
def PayMem (t : TState) (ins : Instr) : Prop :=
  ∀ a, ins.op = .mem a → ∀ r, Opnd.reg r ∈ a.srcs →
    ∃ v, t.regs r = some v ∧ v.bytes = a.elem.width / 8

/-- The obligation of a store site: no fault when the payload registers hold their values. -/
abbrev W0NoUbPay (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) : Prop :=
  ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
    (code P L g w).AtD d t → (code P L g w).inv d → kernel.code[(code P L g w).pc d]? = some ins →
    Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o →
    PayMem t ins → ∀ f, e.kind ≠ .ub f

/-- **A weak shared store at an aligned address of a payload of the element's width is no
fault.** -/
theorem store_nonub {t : TState} {w base pc n : Nat} {off : Int} {srcs : List Opnd}
    {x : BitVec 64} {e : Event} {o : Option TState}
    (hr : t.regs base = some (.bits 32 x)) (hw : w / 8 ≠ 0) (hn : w / 8 * srcs.length = n)
    (hal : (smLoc L g x off).addr % n = 0) (hsub : t.sub < srcs.length)
    (hall : ∀ o ∈ srcs, ∃ r, o = .reg r)
    (hpay : ∀ r, Opnd.reg r ∈ srcs → ∃ v, t.regs r = some v ∧ v.bytes = w / 8)
    (hf : Fires pc (storeTmpl L g t .shared w base off srcs) e o) :
    ∀ f, e.kind ≠ .ub f := by
  subst hn
  intro f he
  have h := fires_ub hf he
  obtain ⟨r, hr'⟩ := hall _ (List.getElem_mem hsub)
  have hs : srcs[t.sub]? = some (.reg r) := by rw [List.getElem?_eq_getElem hsub, hr']
  obtain ⟨v, hv, hb⟩ := hpay r (hr' ▸ List.getElem_mem hsub)
  have hal' : ¬ (w / 8 = 0 ∨ (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat %
      (w / 8 * srcs.length) ≠ 0) := by
    intro hh
    rcases hh with hh | hh
    · exact hw hh
    · exact hh hal
  simp only [storeTmpl, effAddr_shared32 hr, elemAcc, bind, Except.bind, hal', ↓reduceIte, pure,
    Except.pure, hs, readValue, readReg, hv, storeValue_of_bytes hb] at h
  cases h

theorem noUbAt_mst (hp : Pre P L m) (d : D) (hs : d.site = .mst ∨ d.site = .est)
    (hw : w = warpW L g) (ht : tidOf L g < 128) : W0NoUbPay P L g w d := by
  have hal := wsLoc_al hp (r13_loc (g := g) hp ht) (n := 4) (by decide) (by omega)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  subst hw
  rcases hs with hs | hs <;> cases hs <;> w0_shapeS <;>
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 471) (by decide) (by decide) hal
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf

theorem noUbAt_pst (hp : Pre P L m) (d : D) (hs : ∃ k, d.site = .pst k)
    (hw : w = warpW L g) (ht : tidOf L g < 128) : W0NoUbPay P L g w d := by
  obtain ⟨k, hs⟩ := hs
  have hal : ∀ j : Fin 8, (smLoc L g (pstW L g (warpW L g) j) 0).addr % 16 = 0 :=
    fun j => wsLoc_al hp (pst_loc (g := g) hp ht j) (n := 16) (by decide) (by omega)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  subst hw
  cases hs
  fin_cases k <;> w0_shapeS
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 988) (by decide) (by decide) (hal ⟨0, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 989) (by decide) (by decide) (hal ⟨1, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 990) (by decide) (by decide) (hal ⟨2, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 991) (by decide) (by decide) (hal ⟨3, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 992) (by decide) (by decide) (hal ⟨4, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 993) (by decide) (by decide) (hal ⟨5, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 994) (by decide) (by decide) (hal ⟨6, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 995) (by decide) (by decide) (hal ⟨7, by decide⟩)
      (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf

theorem noUbAt_ost (hp : Pre P L m) (d : D) (hs : ∃ k, d.site = .ost k)
    (hw : w = warpW L g) (ht : tidOf L g < 128) : W0NoUbPay P L g w d := by
  obtain ⟨k, hs⟩ := hs
  have hal : ∀ j : Nat, j < 4 →
      (smLoc L g (r16W L g (warpW L g)) (204800 + 1024 * (j : Int))).addr % 16 = 0 :=
    fun j hj => wsLoc_al hp (r16_loc (g := g) hp ht hj) (n := 16) (by decide) (by omega)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  subst hw
  cases hs
  fin_cases k <;> w0_shapeS
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 474) (by decide) (by decide) (hal 0 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 474) (by decide) (by decide) (hal 1 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 474) (by decide) (by decide) (hal 2 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf
  · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    intro hpay
    exact store_nonub (rg 474) (by decide) (by decide) (hal 3 (by decide))
      (by have h1 : el < 4 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
      (fun r hr => hpay _ rfl r hr) hf

/-- **A weak global store of one element at an aligned address, of a payload of the element's
width, is no fault.** -/
theorem gstore_nonub {t : TState} {w base pc n : Nat} {srcs : List Opnd} {x : BitVec 64}
    {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 64 x)) (hw : w / 8 ≠ 0)
    (hn : w / 8 * srcs.length = n) (hal : (truncBits 64 x + BitVec.ofInt 64 0).toNat % n = 0)
    (hsub : t.sub < srcs.length) (hall : ∀ o ∈ srcs, ∃ r, o = .reg r)
    (hpay : ∀ r, Opnd.reg r ∈ srcs → ∃ v, t.regs r = some v ∧ v.bytes = w / 8)
    (hf : Fires pc (storeTmpl L g t .global w base 0 srcs) e o) : ∀ f, e.kind ≠ .ub f := by
  subst hn
  intro f he
  have h := fires_ub hf he
  obtain ⟨r, hr'⟩ := hall _ (List.getElem_mem hsub)
  have hs : srcs[t.sub]? = some (.reg r) := by rw [List.getElem?_eq_getElem hsub, hr']
  obtain ⟨v, hv, hb⟩ := hpay r (hr' ▸ List.getElem_mem hsub)
  have hal' : ¬ (w / 8 = 0 ∨ (truncBits 64 x + BitVec.ofInt 64 0).toNat %
      (w / 8 * srcs.length) ≠ 0) := by
    intro hh
    rcases hh with hh | hh
    · exact hw hh
    · exact hh hal
  simp only [storeTmpl, effAddr_global_bits hr, elemAcc, bind, Except.bind, hal', ↓reduceIte,
    pure, Except.pure, hs, readValue, readReg, hv, storeValue_of_bytes hb] at h
  cases h

/-- The LSE word is 4-byte aligned. -/
theorem lse_al (hp : Pre P L m) :
    (truncBits 64 (lseAddr P L g) + BitVec.ofInt 64 0).toNat % 4 = 0 := by
  rw [lseAddr_eq hp]
  have h := hp.lseAlign
  have e0 : BitVec.ofInt 64 0 = 0 := rfl
  simp only [truncBits, W, e0, add_zero, BitVec.toNat_ofNat, Nat.mod_mod]
  omega

theorem noUbAt_lse (hp : Pre P L m) (d : D) (hs : d.site = .lse) : W0NoUbPay P L g w d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shapeS
  change Fires _ (storeTmpl L g t .global _ _ _ _) e o at hf
  intro hpay
  exact gstore_nonub (rg 3574) (by decide) (by decide) (lse_al hp)
    (by have h1 : el < 1 := hi; have h2 : t.sub = el := hsub; simp; omega) (by simp)
    (fun r hr => hpay _ rfl r hr) hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Loader.Ref
public import Kernels.InklingRelDecode.Proof.Loader.Inputs
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Lemmas.Flow.Step.ShapeRegs
import Kernels.InklingRelDecode.Proof.Lib.IterRange
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Flow.Code.Part037
import Lemmas.Flow.Arith32Word
import Lemmas.Flow.LoadAl
import Lemmas.Flow.UbStop

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

private theorem value_page0 (L : Launch) (g : Nat) (w : Value) (regs : Nat → Value)
    (i n a b : Value) :
    valueOf L g w regs ⟨.page false, i, n, a, b⟩ 2053 = .bits 64
      (wide (shrs (shl (mad32 (bits (regs 532)) (bits i)
        (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .x)))) 7) 6)
      (wide (mul32 (bits (regs 528))
        (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .z))))
        ((regs 2020).regBits.getD 0))) := rfl

private theorem shl7_W {a : Nat} (h : a * 128 < 2 ^ 32) : shl (W a) 7 = W (128 * a) := by
  have hi : (i32 (7 : Int)).toNat = 7 := by decide
  simp only [shl]
  rw [hi]
  split_ifs with h8
  · exact absurd h8 (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, r32, W, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  rw [Nat.shiftLeft_eq]
  have ha : a < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a % 2 ^ 32 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt ha]
  omega

private theorem wide_W {a c : Nat} (ha : a < 2 ^ 31) (hc : 4 * a + c < 2 ^ 64) :
    wide (W a) (W c) = W (4 * a + c) := by
  have h1 : toSigned 32 (r32 (W a)) = a := by rw [r32_W (by omega)]; exact toSigned_W ha
  simp only [wide, intOf, ite_true, h1]
  have hc64 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  have h2 : toSigned 64 (truncBits 64 (W c)) = c ∨
      toSigned 64 (truncBits 64 (W c)) = c - 2 ^ 64 := by
    simp only [toSigned, truncBits, W, BitVec.toNat_ofNat, hc64]
    split_ifs <;> simp_all
  apply BitVec.eq_of_toNat_eq
  rcases h2 with h2 | h2 <;> rw [h2] <;>
    simp only [intBits, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_ofInt] <;> omega

private theorem page_word {sp j x z sb bt B : Nat} (hs : sp * j + x < B) (hB : B * 128 < 2 ^ 31)
    (hsp : sp < 2 ^ 32) (hj : j < 2 ^ 32) (_hx : x < 2 ^ 32) (hz : z < 2 ^ 32) (hsb : sb < 2 ^ 32)
    (hzs : sb * z < 2 ^ 31) (hbt : bt + 4 * (sb * z) + 8 * (sp * j + x) + 8 ≤ 2 ^ 64) :
    wide (shrs (shl (mad32 (W sp) (W j) (W x)) 7) 6)
      (wide (mul32 (W sb) (W z)) (W bt)) = W (bt + 4 * (sb * z) + 8 * (sp * j + x)) := by
  have hn : sp * j + x < 2 ^ 24 := by omega
  rw [mad32_W hsp hj (by omega), shl7_W (by omega), mul32_W hsb hz (by omega)]
  have hsh : shrs (W (128 * (sp * j + x))) ((6 : Nat) : Int) = W (2 * (sp * j + x)) := by
    rw [toNat_shrs_W (by omega) (by omega)]
    congr 2
    omega
  rw [show (6 : Int) = ((6 : Nat) : Int) from rfl, hsh]
  rw [wide_W hzs (by omega), wide_W (by omega) (by omega)]
  congr 1
  omega

private theorem page_site (s : Site) :
    s.pc = 2382 ∨ s.pc = 2399 → s = .page false ∨ s = .page true := by
  cases s <;> decide +revert

private theorem page_loop : ∀ b, (Site.page b).inLoop = true := by decide

private theorem value_page1 (L : Launch) (g : Nat) (w : Value) (regs : Nat → Value)
    (i n a b : Value) :
    valueOf L g w regs ⟨.page true, i, n, a, b⟩ 2054 = .bits 64 (truncBits 64
      (truncBits 64 (wide (shrs (shl (mad32 (bits (regs 532)) (bits i)
        (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .x)))) 7) 6)
      (wide (mul32 (bits (regs 528))
        (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .z))))
        ((regs 2020).regBits.getD 0))) + 4)) :=
  rfl

private theorem input_regs (Q : Params) (L : Launch) (g : Nat) (rest : Nat → Value) :
    inputs Q L g rest 532 = b32 (Q.splits % 2 ^ 32) ∧
    inputs Q L g rest 528 = b32 (Q.strideBt % 2 ^ 32) ∧
    (inputs Q L g rest 2020).regBits.getD 0 = BitVec.ofNat 64 Q.btBase := ⟨rfl, rfl, rfl⟩

/-- The block-table word pair of loop index `j`: the address and the slab bounds. -/
theorem page_value {Q L m g j} (hp : Pre Q L m) (hg : g < L.threads)
    (hj : j < Lib.blocksOf Q L (g / L.block)) :
    ∃ A, wide (shrs (shl (mad32 (bits (b32 (Q.splits % 2 ^ 32))) (bits (b32 j))
        (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .x)))) 7) 6)
      (wide (mul32 (bits (b32 (Q.strideBt % 2 ^ 32)))
        (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .z)))) (BitVec.ofNat 64 Q.btBase))
        = BitVec.ofNat 64 A ∧
      A = Q.btBase + 4 * (Q.strideBt * (L.ctaidOf (g / L.block)).get .z) +
        8 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x) ∧
      Q.splits * j + (L.ctaidOf (g / L.block)).get .x <
        Q.blocks ((L.ctaidOf (g / L.block)).get .z) ∧
      ∀ δ < 2, ∀ kk < 4, Q.reads (A + 4 * δ + kk) ∧ A + 4 * δ + kk < 2 ^ 64 := by
  obtain ⟨hx, -, hz⟩ := Lib.coordinate_bounds hp hg
  generalize hxx : (L.ctaidOf (g / L.block)).get .x = x at hx ⊢
  generalize hzz : (L.ctaidOf (g / L.block)).get .z = z at hz ⊢
  have hnum : j < Q.numIters z x := by rw [← hxx, ← hzz]; exact hj
  have hsp := hp.splitsRange
  have hsc := hp.scalarsRange
  have hseq := hp.seqRange z hz
  have hb := hp.bRange
  have hlt : Q.splits * j + x < Q.blocks z := by
    unfold Params.numIters at hnum
    have := (Nat.le_div_iff_mul_le hp.splitsPos).mp hnum
    rw [Nat.succ_mul, Nat.mul_comm j] at this
    omega
  have hB : Q.blocks z * 128 < 2 ^ 31 := by unfold Params.blocks; omega
  have hidx := hp.btIndexRange z hz 0 (by omega)
  rw [Nat.add_zero, Nat.mul_comm] at hidx
  have hjr : j < 2 ^ 31 := by
    have := Lib.iter_range hp hg
    rw [hxx, hzz] at this
    omega
  have hbound : ∀ δ < 2, ∀ kk < 4, Q.reads (Q.btBase + 4 * (Q.strideBt * z) + 8 * (Q.splits * j + x)
      + 4 * δ + kk) := by
    intro δ hδ kk hk
    right; right; right; right; right
    refine ⟨z, hz, 2 * (Q.splits * j + x) + δ, by omega, kk, hk, ?_⟩
    rw [Nat.mul_comm Q.strideBt z]
    omega
  have hrange := fun δ hδ kk hk => hp.readsRange _ (hbound δ hδ kk hk)
  have last := hrange 1 (by omega) 3 (by omega)
  refine ⟨Q.btBase + 4 * (Q.strideBt * z) + 8 * (Q.splits * j + x), ?_, rfl, hlt,
    fun δ hδ kk hk => ⟨hbound δ hδ kk hk, hrange δ hδ kk hk⟩⟩
  have e1 : Q.splits % 2 ^ 32 = Q.splits := Nat.mod_eq_of_lt (by omega)
  have e2 : Q.strideBt % 2 ^ 32 = Q.strideBt := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, bits_b32 (j := Q.splits) (by omega), bits_b32 (j := j) (by omega),
    bits_b32 (j := Q.strideBt) (by omega), r32_W (n := x) (by omega),
    r32_W (n := z) (by omega)]
  exact page_word hlt hB (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)


/-- **A block-table load of the loader reads the table entry of an existing slab.** -/
theorem page_acc {Q L m g w rest a bs lo hi} {d : D} {t : TState} {ins o}
    (hp : Pre Q L m) (hg : g < L.threads)
    (hat : (code L g w (inputs Q L g rest)).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (fire : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨d.site.pc, .rd a bs⟩ o)
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hr : Ref lo hi d)
    (site : d.site.pc = 2382 ∨ d.site.pc = 2399) :
    ∃ j s, d.counter = b32 j ∧ j < 2 ^ 31 ∧
      s = 2 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x) +
        (if d.site.pc = 2382 then 0 else 1) ∧
      s < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z) ∧
      a = wordAcc (Q.btBase + 4 * (Q.strideBt * (L.ctaidOf (g / L.block)).get .z + s)) := by
  obtain ⟨s,i,n,a',b'⟩ := d
  obtain hs := page_site s site
  obtain ⟨_,sub,_,_,regs⟩ := hat
  have hsub : t.sub = 0 := by
    revert sub
    rcases hs with rfl | rfl <;> intro sub <;> simpa [code] using sub
  have hrefs := ref_loop hr (by rcases hs with rfl | rfl <;> exact page_loop _)
  obtain ⟨j,-,hjl,hcnt,-⟩ := hrefs
  change i = b32 j at hcnt
  have hj31 : j < 2 ^ 31 := by
    have := Lib.iter_range hp hg
    have e : hi = Q.numIters ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) := hh
    omega
  subst hcnt
  obtain ⟨A,hA,hAe,hlt,hok⟩ := page_value (j := j) hp hg (hh ▸ hjl)
  obtain ⟨r532,r528,r2020⟩ := input_regs Q L g rest
  have conv (δ : Nat) : A + 4 * δ = Q.btBase + 4 * (Q.strideBt *
      (L.ctaidOf (g / L.block)).get .z + (2 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x)
      + δ)) := by rw [hAe]; ring
  rcases hs with rfl | rfl
  · have reg := holds_mem regs (mem_factsFrom (val := valueOf L g w _ _)
      (show 2053 ∈ Flow.live (Site.page false).pc by decide +kernel))
    rw [value_page0, r532, r528, r2020, hA] at reg
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2382)
    rcases fires_load_reg hsub reg fire with ⟨_,h⟩ | ⟨_,h⟩
    · have eq := (Kind.rd.inj h).1
      have := (hok 0 (by decide) 3 (by decide)).2
      refine ⟨j, 2 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x) + 0, rfl, hj31,
        by simp [Site.pc], by omega, ?_⟩
      rw [← conv 0, eq]
      simp only [Nat.mul_zero, Nat.add_zero] at this ⊢
      simp [truncBits, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by omega)]
    · cases h
  · have reg := holds_mem regs (mem_factsFrom (val := valueOf L g w _ _)
      (show 2054 ∈ Flow.live (Site.page true).pc by decide +kernel))
    rw [value_page1, r532, r528, r2020, hA] at reg
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2399)
    rcases fires_load_reg hsub reg fire with ⟨_,h⟩ | ⟨_,h⟩
    · have eq := (Kind.rd.inj h).1
      have := (hok 1 (by decide) 3 (by decide)).2
      refine ⟨j, 2 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x) + 1, rfl, hj31,
        by simp [Site.pc], by omega, ?_⟩
      rw [← conv 1, eq]
      simp only [truncBits, BitVec.toNat_ofNat]
      simp
      rw [Nat.mod_eq_of_lt (show A + 4 < 18446744073709551616 by omega)]
    · cases h

/-- The block-table load's address register holds a 4-aligned address. -/
private theorem page_pre {Q L m g w rest lo hi} {d : D} {t : TState}
    (hp : Pre Q L m) (hg : g < L.threads) (hat : (code L g w (inputs Q L g rest)).AtD d t)
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hr : Ref lo hi d)
    (site : d.site.pc = 2382 ∨ d.site.pc = 2399) :
    t.sub = 0 ∧ ∃ r x, ((d.site.pc = 2382 ∧ r = 2053) ∨ (d.site.pc = 2399 ∧ r = 2054)) ∧
      t.regs r = some (.bits 64 x) ∧ x.toNat % 4 = 0 := by
  obtain ⟨s,i,n,a',b'⟩ := d
  obtain hs := page_site s site
  obtain ⟨_,sub,_,_,regs⟩ := hat
  have hsub : t.sub = 0 := by
    revert sub
    rcases hs with rfl | rfl <;> intro sub <;> simpa [code] using sub
  refine ⟨hsub, ?_⟩
  have hrefs := ref_loop hr (by rcases hs with rfl | rfl <;> exact page_loop _)
  obtain ⟨j,-,hjl,hcnt,-⟩ := hrefs
  change i = b32 j at hcnt
  subst hcnt
  obtain ⟨A,hA,hAe,-,hok⟩ := page_value (j := j) hp hg (hh ▸ hjl)
  obtain ⟨r532,r528,r2020⟩ := input_regs Q L g rest
  have h4 := hp.btAlign
  have last := (hok 1 (by decide) 3 (by decide)).2
  have hAl : A % 4 = 0 := by omega
  rcases hs with rfl | rfl
  · have reg := holds_mem regs (mem_factsFrom (val := valueOf L g w _ _)
      (show 2053 ∈ Flow.live (Site.page false).pc by decide +kernel))
    rw [value_page0, r532, r528, r2020, hA] at reg
    exact ⟨2053, _, Or.inl ⟨rfl, rfl⟩, reg, by simp [BitVec.toNat_ofNat]; omega⟩
  · have reg := holds_mem regs (mem_factsFrom (val := valueOf L g w _ _)
      (show 2054 ∈ Flow.live (Site.page true).pc by decide +kernel))
    rw [value_page1, r532, r528, r2020, hA] at reg
    refine ⟨2054, _, Or.inr ⟨rfl, rfl⟩, reg, ?_⟩
    simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat]
    have h44 : BitVec.toNat (4 : BitVec 64) = 4 := rfl
    omega

/-- **A block-table load of the loader is not undefined behaviour**: its address is the table's
base plus multiples of four. -/
theorem page_safe {Q L m g w rest lo hi} {d : D} {t : TState} {ins}
    (hp : Pre Q L m) (hg : g < L.threads)
    (hat : (code L g w (inputs Q L g rest)).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hr : Ref lo hi d)
    (site : d.site.pc = 2382 ∨ d.site.pc = 2399) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain ⟨hsub, r, x, hs, reg, hal⟩ := page_pre hp hg hat hh hr site
  rcases hs with ⟨hp', rfl⟩ | ⟨hp', rfl⟩
  · obtain rfl := Option.some.inj (hc.symm.trans (hp' ▸ Flow.code_2382))
    refine not_ub_of_fires (pc := 2382) (fun f' hf => ?_) f
    have := fires_load_reg_al hsub reg hf rfl
    simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
      Int.zero_emod, Int.toNat_zero] at this
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans (hp' ▸ Flow.code_2399))
    refine not_ub_of_fires (pc := 2399) (fun f' hf => ?_) f
    have := fires_load_reg_al hsub reg hf rfl
    simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
      Int.zero_emod, Int.toNat_zero] at this
    omega

/-- A non-undefined-behaviour event of a block-table load is a read. -/
theorem page_rd {Q L m g w rest lo hi} {d : D} {t : TState} {ins} {o : Option TState} {v : Event}
    (hp : Pre Q L m) (hg : g < L.threads)
    (hat : (code L g w (inputs Q L g rest)).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hr : Ref lo hi d)
    (site : d.site.pc = 2382 ∨ d.site.pc = 2399)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) v o)
    (hu : ∀ f, v.kind ≠ .ub f) : ∃ ac bs, v.kind = .rd ac bs := by
  obtain ⟨hsub, r, x, hs, reg, -⟩ := page_pre hp hg hat hh hr site
  rcases hs with ⟨hp', rfl⟩ | ⟨hp', rfl⟩
  · obtain rfl := Option.some.inj (hc.symm.trans (hp' ▸ Flow.code_2382))
    rcases fires_load_reg hsub reg hf with ⟨bs, h⟩ | ⟨f, h⟩
    · exact ⟨_, _, h⟩
    · exact absurd h (hu f)
  · obtain rfl := Option.some.inj (hc.symm.trans (hp' ▸ Flow.code_2399))
    rcases fires_load_reg hsub reg hf with ⟨bs, h⟩ | ⟨f, h⟩
    · exact ⟨_, _, h⟩
    · exact absurd h (hu f)

end PTX.Kernels.InklingRelDecode.Proof.Loader

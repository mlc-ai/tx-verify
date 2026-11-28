-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.KvSlab
public import Kernels.InklingRelDecode.Proof.Iface.CopyIndex
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyDest
import Kernels.InklingRelDecode.Proof.Loader.CopyFoot
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Flow.Code.Part037
import Lemmas.Flow.Arith32Word

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof Arith32

/-- The coordinate registers of the eight copies: the column of the half tile and the row of the
page word. -/
private theorem shape (p : Fin 4) (half : Bool) :
    ∃ guard dst rc rr, kernel.code[(Site.copy p half).pc]? = some ⟨guard,
      .cpTensor false false dst 0 (.reg 1949) [.reg rc, .reg rr] 580 0 none .tile none⟩ ∧
      rc = [583, 586, 588, 590].getD (2 * (p.val % 2) + half.toNat) 0 ∧
      ((rr = 584 ∧ p.val < 2) ∨ (rr = 593 ∧ ¬ p.val < 2)) ∧
      rc ∈ Flow.live (Site.copy p half).pc ∧ rr ∈ Flow.live (Site.copy p half).pc := by
  fin_cases p <;> cases half
  · exact ⟨_, _, _, _, Flow.code_2389, by simp, by simp, by decide +kernel⟩
  · exact ⟨_, _, _, _, Flow.code_2391, by simp, by simp, by decide +kernel⟩
  · exact ⟨_, _, _, _, Flow.code_2394, by simp, by simp, by decide +kernel⟩
  · exact ⟨_, _, _, _, Flow.code_2396, by simp, by simp, by decide +kernel⟩
  · exact ⟨_, _, _, _, Flow.code_2404, by simp, by simp, by decide +kernel⟩
  · exact ⟨_, _, _, _, Flow.code_2406, by simp, by simp, by decide +kernel⟩
  · exact ⟨_, _, _, _, Flow.code_2410, by simp, by simp, by decide +kernel⟩
  · exact ⟨_, _, _, _, Flow.code_2412, by simp, by simp, by decide +kernel⟩

private theorem col_value {Q L m g} (hp : Pre Q L m) (hg : g < L.threads) (w : Value)
    (rest : Nat → Value) (p : Fin 4) (half : Bool) (i n a b : Value) {rc c : Nat}
    (hc : c < 4) (hrc : rc = [583, 586, 588, 590].getD c 0) :
    valueOf L g w (inputs Q L g rest) ⟨.copy p half, i, n, a, b⟩ rc =
      b32 ((L.ctaidOf (g / L.block)).get .y * Q.headCols + 64 * c) := by
  obtain ⟨-, hy, -⟩ := Lib.coordinate_bounds hp hg
  have hc := hp.kvCols _ hy
  have hc1 := hp.kvCols 1 (by unfold kvHeads; omega)
  have hs := hp.slotStrideRange
  unfold headDim at hc hc1
  unfold kvHeads at hy
  have hmul : mul32 (bits (inputs Q L g rest 531))
      (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .y))) =
      W ((L.ctaidOf (g / L.block)).get .y * Q.headCols) := by
    rw [show inputs Q L g rest 531 = b32 (Q.headCols % 2 ^ 32) from rfl, bits_b32 (by omega),
      r32_W (by omega), Nat.mul_comm _ Q.headCols]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact mul32_W (by omega) (by omega)
      (by rw [Nat.mul_comm]; omega)
  interval_cases c <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hrc <;> subst hrc
  · change Value.bits 32 _ = _
    rw [hmul]
    rfl
  · change Value.bits 32 (addi _ 64) = _
    rw [hmul]
    exact congrArg (Value.bits 32) (addi_W (n := 64) (by omega) (by omega))
  · change Value.bits 32 (addi _ 128) = _
    rw [hmul]
    exact congrArg (Value.bits 32) (addi_W (n := 128) (by omega) (by omega))
  · change Value.bits 32 (addi _ 192) = _
    rw [hmul]
    exact congrArg (Value.bits 32) (addi_W (n := 192) (by omega) (by omega))

private theorem row_value {Q L m g} (hp : Pre Q L m) (hg : g < L.threads) (w : Value)
    (rest : Nat → Value) (p : Fin 4) (half : Bool) (i n a b : Value) {rr : Nat}
    (hrr : (rr = 584 ∧ Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) 0 i a) ∨
      (rr = 593 ∧ Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) 1 i b)) :
    ∃ j s, i = b32 j ∧ j < 2 ^ 31 ∧ s = 2 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x) +
        (if rr = 584 then 0 else 1) ∧ s < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z) ∧
      valueOf L g w (inputs Q L g rest) ⟨.copy p half, i, n, a, b⟩ rr =
        b32 (Q.page ((L.ctaidOf (g / L.block)).get .z) s * Q.pageRows +
          (L.ctaidOf (g / L.block)).get .y * Q.headRows) := by
  obtain ⟨-, hy, hz⟩ := Lib.coordinate_bounds hp hg
  obtain ⟨-, -, -, hpr, hhr, -⟩ := hp.scalarsRange
  have hpos := hp.pageRowsPos
  have hr := hp.rowsRange
  have hmul : ∀ (s : Nat) (hs : s < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z)),
      mad32 (bits (b32 (Q.page ((L.ctaidOf (g / L.block)).get .z) s)))
        (bits (inputs Q L g rest 529))
        (mul32 (bits (inputs Q L g rest 530))
          (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .y)))) =
      W (Q.page ((L.ctaidOf (g / L.block)).get .z) s * Q.pageRows +
        (L.ctaidOf (g / L.block)).get .y * Q.headRows) := by
    intro s hs
    have hin := hp.slabInside _ hz s hs _ hy
    have hpg := Nat.le_mul_of_pos_right (Q.page ((L.ctaidOf (g / L.block)).get .z) s) hpos
    unfold kvHeads at hy
    rw [show inputs Q L g rest 529 = b32 (Q.pageRows % 2 ^ 32) from rfl,
      show inputs Q L g rest 530 = b32 (Q.headRows % 2 ^ 32) from rfl, bits_b32 (by omega),
      bits_b32 (by omega), bits_b32 (by omega), r32_W (by omega),
      Nat.mod_eq_of_lt (show Q.pageRows < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show Q.headRows < 2 ^ 32 by omega),
      mul32_W (by omega) (by omega) (by rw [Nat.mul_comm]; omega)]
    rw [mad32_W (by omega) (by omega) (by rw [Nat.mul_comm Q.headRows]; omega),
      Nat.mul_comm Q.headRows]
  rcases hrr with ⟨rfl, j, hj, hjb, hs, rfl⟩ | ⟨rfl, j, hj, hjb, hs, rfl⟩
  · exact ⟨j, _, hj, hjb, rfl, hs, congrArg (Value.bits 32) (hmul _ hs)⟩
  · exact ⟨j, _, hj, hjb, rfl, hs, congrArg (Value.bits 32) (hmul _ hs)⟩

/-- **A loader copy is the copy of a box of the slab its loop counter names**: the block `j` of the
CTA's split is the one the loop has reached, the columns come from the KV head of the CTA and the
half tile of the copy's index, the row from the block-table word of slab `2 (splits j + x) + i / 4`;
the box lands in the slot `j % 3` of the ring. -/
public theorem copy_slab_at {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) :
    ∃ j D, j + 1 = pollRound 2374 ((X.tr g).take k) + Iface.preloadCount Q L (g / L.block) ∧
      D = L.sharedBase + 32768 * (j % 3) + Iface.copyOff pc ∧
      2 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x) + Iface.copyIndex pc / 4 <
        2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z) ∧
      sp = Lib.kvCopySpec Q (g / L.block)
        ((L.ctaidOf (g / L.block)).get .y * Q.headCols + 128 * (Iface.copyIndex pc / 2 % 2) +
          64 * (Iface.copyIndex pc % 2))
        (Q.page ((L.ctaidOf (g / L.block)).get .z)
          (2 * (Q.splits * j + (L.ctaidOf (g / L.block)).get .x) + Iface.copyIndex pc / 4) *
            Q.pageRows + (L.ctaidOf (g / L.block)).get .y * Q.headRows) D sp.mbar := by
  have warp := copy_warp hp hX hf he site
  have range : 2344 < pc ∧ pc < 2422 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at site
    omega
  have hg := Frame.lt_of_get hX he
  obtain ⟨w,x,⟨s,i,n,a,b⟩,t,ins,o,hat,hpc,hc,fire,hr,hq,pg⟩ :=
    loader_event hp hX hf warp he (by simp) range.1 range.2
  change pc = s.pc at hpc
  obtain ⟨p,half,rfl⟩ := copy_site s (hpc ▸ site)
  subst hpc
  have key : Iface.copyIndex (Site.copy p half).pc = 2 * p.val + half.toNat ∧
      Iface.copyOff (Site.copy p half).pc = boxOffset p half := by
    fin_cases p <;> cases half <;> decide +kernel
  obtain ⟨guard,dst,rc,rr,hop,hrc,hrr,lrc,lrr⟩ := shape p half
  obtain rfl := Option.some.inj (hc.symm.trans hop)
  obtain ⟨desc,-,-,base⟩ := copy_footprint (regs := Loader.inputs Q L g (dispatchRegs Q L g w x))
    (w := w) hp rfl hat hc fire rfl
  have load := fires_cpTensor_copy fire rfl
  obtain ⟨_,_,_,_,hregs⟩ := hat
  have hc4 : 2 * (p.val % 2) + half.toNat < 4 := by
    have := p.isLt
    cases half <;> simp <;> omega
  have hcv := col_value hp hg w (dispatchRegs Q L g w x) p half i n a b hc4 hrc
  obtain ⟨hpa, hpb⟩ := pg
  have hrr' : (rr = 584 ∧ Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) 0 i a) ∨
      (rr = 593 ∧ Lib.PageAt Q ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) 1 i b) := by
    rcases hrr with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact .inl ⟨rfl, hpa (by simp [Site.pages, h])⟩
    · exact .inr ⟨rfl, hpb (by simp [Site.pages, h])⟩
  obtain ⟨j', sl, hj', hjb', hsl, hlt, hrv⟩ := row_value hp hg w (dispatchRegs Q L g w x) p half
    i n a b hrr'
  have r0 := holds_mem hregs (mem_factsFrom lrc)
  have r1 := holds_mem hregs (mem_factsFrom lrr)
  change t.regs rc = some (valueOf L g w _ _ rc) at r0
  change t.regs rr = some (valueOf L g w _ _ rr) at r1
  rw [hcv] at r0
  rw [hrv] at r1
  have small : (bits i).toNat < 2 ^ 31 := ref_counter_lt hr (by rfl) (Lib.iter_range hp hg)
  obtain ⟨j, hlo, hjh, hcnt, -⟩ := ref_loop hr (by rfl)
  change i = b32 j at hcnt
  have hhi : iterCount Q L (g / L.block) < 2 ^ 31 := Lib.iter_range hp hg
  have hjj : j' = j := by
    have e := congrArg bits (hj'.symm.trans hcnt)
    rw [bits_b32 (by omega), bits_b32 (by omega)] at e
    have e2 := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at e2
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e2
  rw [hjj] at hsl
  have hrr0 : (if rr = 584 then 0 else 1) = Iface.copyIndex (Site.copy p half).pc / 4 := by
    have := p.isLt
    rcases hrr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rw [key.1] <;> cases half <;> simp at * <;> omega
  rw [hrr0] at hsl
  subst hsl
  have hoff : ∀ p half, boxOffset p half % 1024 = 0 := by decide +kernel
  have := hp.sharedAlignment
  have := hoff p half
  have bnd := Lib.kv_coord_lt hp hg hlt (isV := (2 * (p.val % 2) + half.toNat) / 2)
    (hh := (2 * (p.val % 2) + half.toNat) % 2) (by omega) (by omega)
  obtain ⟨cta, d', hsp⟩ := Lib.kvCopySpec_of_load load desc r0 r1 (by omega) bnd.2.2
  have hb := base small
  rw [hsp] at hb
  obtain ⟨rfl, hd'⟩ : cta = g / L.block ∧ d' = L.sharedBase + 32768 * ((bits i).toNat % 3) +
      boxOffset p half := by simpa [Lib.kvCopySpec] using hb
  have hbj : (bits i).toNat = j := by
    rw [hcnt, bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hq' : pollRound 2374 ((X.tr g).take k) = (bits i).toNat - Iface.preloadCount Q L
      (g / L.block) + 1 := hq
  refine ⟨j, d', by omega, by rw [hd', hbj, key.2], hlt, ?_⟩
  refine hsp.trans ?_
  have e : (L.ctaidOf (g / L.block)).get .y * Q.headCols +
      64 * (2 * (p.val % 2) + half.toNat) =
      (L.ctaidOf (g / L.block)).get .y * Q.headCols +
        128 * (Iface.copyIndex (Site.copy p half).pc / 2 % 2) +
        64 * (Iface.copyIndex (Site.copy p half).pc % 2) := by
    rw [key.1]
    cases half <;> simp <;> omega
  rw [e]

/-- **A loader copy is the copy of a box of an existing slab**: the columns come from the KV
head of the CTA and the half tile, the row from the block-table word the loop has read. -/
public theorem copy_slab {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) :
    Lib.KvSlab Q (g / L.block) sp := by
  obtain ⟨j, D, -, hD, hl, hsp⟩ := copy_slab_at hp hX hf he site
  have hidx : Iface.copyIndex pc < 8 := Iface.copyIndex_lt site
  have hoff := hp.sharedAlignment
  have hal : Iface.copyOff pc % 1024 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at site
    rcases site with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨-, hy, hz⟩ := Lib.coordinate_bounds hp (Frame.lt_of_get hX he)
  exact ⟨D, sp.mbar, _, _, _, Iface.copyIndex pc / 2 % 2, Iface.copyIndex pc % 2, hz, hl, hy,
    by omega, by omega, by omega, hsp⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export

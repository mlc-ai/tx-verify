-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaBox
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SmemElements
public import Lemmas.Tcgen05.TcSharedAddress
public import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-! # Which ring byte an MMA reads for each operand element

With the MMA warp's descriptors (`MmaSmemFacts`): the instruction descriptors decode to `qkDesc`
and `pvDesc` (M = 256, N = 128 over the CTA pair, `kind::f16`; B transposed for PV), and

* QK MMA `j` reads A row `128 r + y` (B row `64 r + y`), contraction `k`, byte `z` from CTA `r`
  of the pair at element `(16 (j % 4) + k, y)` of box `j / 4` of the Q stage (of the K block of
  the KV slot): the K-major 128-byte-swizzled descriptor advanced by `16 (j % 4)` columns selects
  the TMA box's byte (`TcShared.k128_tma_byte`; `qk_a_byteLoc`, `qk_b_byteLoc`);
* PV MMA `j` reads B column `64 r + y`, contraction `k` from CTA `r` at element `(y, 16 j + k)`
  of the V box of the KV slot: the MN-major layout of 64 columns is the box's packed 128-byte
  rows (`pv_b_byteLoc`).

So every shared byte an MMA reads is in a ring region (`mmaReadsRings`, the premise
`MmaReadsRings`; `smemElements_of_descs`), and, with `smem_element`, element `(row, k)` of B of
a QK MMA is the FP16 value of K at row `copyRow + row % 64`, column `copyCol + 16 (j % 4) + k`
of the copy of its use (`qk_b_element`), of A the Q value at row `copyRow + row % 128`
(`qk_a_element`), and of B of a PV MMA the V value at row `copyRow + 16 j + k`, column
`copyCol + row % 64` (`pv_b_element`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace SmemElements

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An operand element at a box byte** is the FP16 value of the input element of the copy of
the read's use that loads box `jb` at element `(x0, y0)`. -/
theorem element_at (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : Rings.RingInit L X)
    (hcp : RingCopies P L X) (ha : AsyncFacts P L X) (hun : InputsUnwritten P X)
    (htc : TcFacts L X) (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (isB : Bool) {m : Nat} {b : FBar} (hb : b.isFull)
    {cta jb x0 y0 : Nat} (hj : jb < b.copies) (hx : x0 < 64) (hy : y0 < b.copyBytes / 128)
    (hbl : s.byteLoc (if isB then .b else .a) (2 * m) = some ⟨.shared, cta,
      Rings.boxBase L b jb + TensorSwizzle.offset .b128 (Rings.boxBase L b jb)
        (128 * y0 + 2 * x0 + 0)⟩) :
    ∃ g k cnt pc al,
      cnt = ((X.tr g).take k).countP (issuesTo (b.loc L (2 * (cta / 2)))) ∧
      X.get (g, k) = some ⟨pc, .tensorIssue al (copySpec P L g b cnt)⟩ ∧ ctaOf L g = cta ∧
      cnt / b.copies = Rings.readUse L X (cta / 2) b i ∧ cnt % b.copies = jb ∧
      ∀ z, z < 2 → (if isB then ops.b else ops.a)[2 * m + z]? =
        some (some ((Value.float .f16 (inputValue P b (copyBatch P L g b cnt)
          (copyHead P L g b cnt) (copyRow P L g b cnt + y0) (copyCol L g b cnt + x0))).byteAt
            z)) := by
  obtain ⟨g, k, cnt, pc, al, x, y, hcnt, hget, hcta, huse, hx', hy', hwl, -, -, -, -, hz⟩ :=
    smem_element hpre hX ht htm hinit hcp ha hun htc htt hi hops isB hbl hb
      (box_inRegion hb hj hx hy (by decide))
  obtain ⟨-, -, -, hl⟩ := Rings.copy_box hb hwl
  simp only [Loc.mk.injEq, true_and] at hl
  obtain ⟨-, hl⟩ := hl
  obtain ⟨hjj, hoo⟩ := Rings.box_eq hb hj (Nat.mod_lt _ (Rings.copies_pos hb))
    (Rings.box_offset_lt' hb _ hx hy (by decide)) (Rings.box_offset_lt' hb _ hx' hy' (by decide))
    hl
  rw [← hjj] at hoo
  obtain ⟨rfl, rfl, -⟩ := TensorCopy.box_offset_inj (base := Rings.boxBase L b jb) hx
    (by decide) hx' (by decide) hoo
  exact ⟨g, k, cnt, pc, al, hcnt, hget, hcta, huse, hjj.symm, hz⟩

/-! ### The operand elements of the QK and PV MMAs -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X)
    (htm : TmemFacts L X) (hinit : Rings.RingInit L X) (hcp : RingCopies P L X)
    (ha : AsyncFacts P L X) (hun : InputsUnwritten P X) (htc : TcFacts L X)
    (htt : TcMmaThreadFacts L X) (hsm : MmaSmemFacts L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops)
include hpre hX ht htm hinit hcp ha hun htc htt hsm hi hops

end

/-- **MmaReadsRings**: every shared byte an MMA reads is in a Q or KV ring region. -/
theorem mmaReadsRings (hpre : Pre P L mem0) (hsc : ScoreFacts L X)
    (htt : TcMmaThreadFacts L X) (hsm : MmaSmemFacts L X) : MmaReadsRings L X := by
  rintro i isB idx l ⟨a, w, ⟨-, hsz, hfp⟩, hcov⟩ -
  have hl := Rings.covers_one hcov hsz
  subst hl
  rcases hfp with ⟨d, s, acc, mask, hi, hbl⟩ | ⟨a', src, cta, hci, -⟩
  · have hlt := OperandSpec.byteLoc_index_lt hbl
    have hidx : idx = 32 * (idx / 32) + 2 * (idx / 2 % 16) + idx % 2 := by omega
    have hz : idx % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk : idx / 2 % 16 < 16 := Nat.mod_lt _ (by decide)
    cases haT : s.aTmem with
    | none =>
      have hD : s.descriptor = qkDesc := qkDesc_eq ((htt.mma_desc hi).2.1 haT)
      obtain ⟨st, sl, j, hs, hsa, hsb⟩ := hsm.qk hi haT
      have hj := j.isLt
      cases isB
      · simp only [Bool.false_eq_true, ↓reduceIte] at hbl hlt
        simp [Operand.rows, hD, qkDesc, Operand.extent, Kind.k, Kind.width] at hlt
        rw [qStepStart_eq] at hsa
        rw [hidx, show idx / 32 = 128 * (idx / 32 / 128) + idx / 32 % 128 by omega,
          qk_a_byteLoc hD haT hsa (boxBase_mod hpre (b := .qFull st) rfl _) (by omega)
            (by omega) hk hz] at hbl
        rw [← Option.some.inj hbl]
        exact ⟨_, _, rfl, box_inRegion rfl (by simp only [FBar.copies]; omega) (by omega)
          (by simp only [FBar.copyBytes]; omega) hz⟩
      · simp only [↓reduceIte] at hbl hlt
        simp [Operand.rows, hD, qkDesc, Operand.extent, Kind.k, Kind.width] at hlt
        rw [kStepStart_eq hs] at hsb
        rw [hidx, show idx / 32 = 64 * (idx / 32 / 64) + idx / 32 % 64 by omega,
          qk_b_byteLoc hD hsb (boxBase_mod hpre (b := .kvFull sl) rfl _) (by omega)
            (by omega) hk hz] at hbl
        rw [← Option.some.inj hbl]
        exact ⟨_, _, rfl, box_inRegion rfl (by simp only [FBar.copies, hs, ↓reduceIte]; omega)
          (by omega) (by simp only [FBar.copyBytes, hs, ↓reduceIte]; omega) hz⟩
    | some ad =>
      have haT' : s.aTmem.isSome = true := by simp [haT]
      cases isB
      · simp only [Bool.false_eq_true, ↓reduceIte] at hbl
        rw [byteLoc_a_tmem haT'] at hbl
        cases hbl
      · have hD : s.descriptor = pvDesc := pvDesc_eq ((htt.mma_desc hi).2.2 haT')
        obtain ⟨sl, j, hs, hsb⟩ := hsm.pv hi haT'
        have hj := j.isLt
        have hs' : ¬ sl.val % 2 = 0 := by omega
        simp only [↓reduceIte] at hbl hlt
        simp [Operand.rows, hD, pvDesc, Operand.extent, Kind.k, Kind.width] at hlt
        rw [vStepStart_eq] at hsb
        rw [hidx, show idx / 32 = 64 * (idx / 32 / 64) + idx / 32 % 64 by omega,
          pv_b_byteLoc hD hsb (boxBase_mod hpre (b := .kvFull sl) rfl _) (by omega)
            (by omega) hk hz] at hbl
        rw [← Option.some.inj hbl]
        exact ⟨_, _, rfl, box_inRegion (jb := 0) rfl
          (by simp only [FBar.copies, hs', ↓reduceIte]; omega) (by omega)
          (by simp only [FBar.copyBytes, hs', ↓reduceIte]; omega) hz⟩
  · exact (hsc.no_cp _ _ hci).elim

/-- **SmemElements** from the MMA warp's descriptors (`MmaSmemFacts`) in place of the premise
`MmaReadsRings`. -/
theorem smemElements_of_descs (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : Rings.RingInit L X)
    (hcp : RingCopies P L X) (ha : AsyncFacts P L X) (hun : InputsUnwritten P X)
    (hsc : ScoreFacts L X) (htc : TcFacts L X) (htt : TcMmaThreadFacts L X)
    (hsm : MmaSmemFacts L X) : TcMmaSources.SmemElements X :=
  smemElements hpre hX ht htm hinit hcp ha hun htc htt (mmaReadsRings hpre hsc htt hsm)

end SmemElements

end
end PTX.Kernels.FlashAttn4Fwd.Proof

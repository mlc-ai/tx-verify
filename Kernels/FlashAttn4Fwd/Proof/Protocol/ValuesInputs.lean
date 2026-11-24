-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaUses
public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesOperands
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SmemElementsMma

@[expose] public section

/-! # The shared operand elements of the MMAs are the tile's inputs

`SmemElements.element_at` gives each shared operand element of a completed MMA as the FP16 value
of the input element that the ring copy of the MMA's read use (`Rings.readUse`: its thread's
earlier commits to the slot's empty barrier) loaded at the descriptor's box and slot. With the
MMA thread's facts of the uses it reads (`MmaUseFacts`) the premise `SmemInputs` follows:

* the descriptor step is the K step: QK MMA `qkStep` (PV MMA `pvStep`) reads that K step of its
  Q stage and KV slot, box `j / 4` at head-dimension columns `16 (j % 4)` on (key rows `16 j` on
  for V);
* the read use is the tile's: before QK MMA of score tile `u` the thread committed `u / n` times
  to the Q stage's empty barrier, and `c` times to the KV slot's, with `6 c + sl = 2 u` (for PV
  of tile `u`, `2 u + 1`), so the copy's item is `u / n` and its KV block the visit's,
  `n - 1 - u % n` (`kv_use`);
* the copy's coordinates are the tile's: the copying thread's CTA is the half `r` of the MMA's
  pair that the operand row names (`pair_half`), so it walks the MMA thread's items, and its
  rank `r` places the rows `128 r` (Q) or `64 r` (K) and the V columns `64 r`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma SmemElements

noncomputable section

namespace ValuesInputs

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An operand element whose two bytes are those of an FP16 value is that value. -/
theorem element_of_bytes {op : TcMma.Operand} {bs : List (Option Byte)} {row k : Nat} {x : ℝ}
    (hz : ∀ z, z < 2 →
      bs[2 * (row * 16 + k) + z]? = some (some ((Value.float .f16 x).byteAt z))) :
    Assumption.idealMmaElement (.f16 .f16 .f32) op bs row k = .ok x := by
  have ha : Assumption.idealMmaElement (.f16 .f16 .f32) .a bs row k = .ok x := by
    refine idealMmaElement_of_bytes ?_
    have h0 := hz 0 (by decide)
    rw [Nat.add_zero] at h0
    rw [take_two h0 (hz 1 (by decide))]
    simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]
  -- an FP16 kind reads both operands alike
  cases op <;> exact ha

/-- **The half `r` of an MMA's pair**: a thread of CTA `lowCta` (`r = 0`) or `highCta` has the
MMA issuer's CTA as its pair's even CTA, rank `r` and the issuer's cluster; the issuer has
rank 0. -/
theorem pair_half (hpre : Pre P L mem0) (hsc : ScoreFacts L X) (htc : TcFacts L X)
    (htt : TcMmaThreadFacts L X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d s acc mask) {r g : Nat} (hr : r < 2)
    (hg : ctaOf L g = if r = 0 then s.lowCta else s.highCta) :
    2 * (ctaOf L g / 2) = ctaOf L i.1 ∧ ctaOf L g % 2 = r ∧ clusterOf L g = clusterOf L i.1 ∧
      rankOf L i.1 = 0 := by
  obtain ⟨hl, hh, he⟩ := ValuesOps.mma_ctas hpre hsc htc htt hi
  have hcl := hpre.cluster
  have hgc : ctaOf L g = ctaOf L i.1 + r := by
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> simp [hl, hh] at hg <;> omega
  unfold clusterOf rankOf
  have h1d := hpre.oneDimLaunch.1
  rw [Launch.oneDim_clusterOfCta h1d, Launch.oneDim_clusterOfCta h1d, Launch.oneDim_rankOfCta h1d,
    hcl, hgc]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The read use of an MMA of the pair whose even CTA is `2 c`: its thread's commits to the
partner empty barrier of its CTA. -/
theorem readUse_eq {c : Nat} {b : FBar} {i : EvId} (h : 2 * c = ctaOf L i.1) :
    Rings.readUse L X c b i = ringCommits L X i.1 b.partner i.2 := by
  unfold Rings.readUse ringCommits
  rw [h]

/-- A copy of use `u` by a thread of cluster `clusterOf g'` loads for item `useItem u` of
`g'`. -/
theorem copyCoords_eq {g g' : Nat} {b : FBar} {cnt u : Nat} (hc : clusterOf L g = clusterOf L g')
    (hu : cnt / b.copies = u) :
    copyCoords P L g b cnt = coordsOf L (workOf L g' (useItem P b u)) := by
  simp only [copyCoords, hu, Schedule.work_of_cluster hc]

/-- **KV ring use `2 u` or `2 u + 1`** is of item `u / n` and of its visit `u % n`. -/
theorem kv_use {n t w : Nat} (hn : 0 < n) (h : w = 2 * t ∨ w = 2 * t + 1) :
    w / (2 * n) = t / n ∧ w % (2 * n) / 2 = t % n := by
  have hd := Nat.mod_add_div t n
  have hm := Nat.mod_lt t hn
  have hsum : w - 2 * t + 2 * (t % n) + 2 * n * (t / n) = w := by
    rw [Nat.mul_assoc]
    generalize n * (t / n) = p at hd ⊢
    generalize t % n = a at hd hm ⊢
    omega
  have hlt : w - 2 * t + 2 * (t % n) < 2 * n := by
    generalize t % n = a at hd hm ⊢
    omega
  obtain ⟨h1, h2⟩ := (Nat.div_mod_unique (a := w) (b := 2 * n) (d := t / n)
    (c := w - 2 * t + 2 * (t % n)) (by omega)).mpr ⟨hsum, hlt⟩
  refine ⟨h1, ?_⟩
  rw [h2]
  generalize t % n = a at hd hm ⊢
  omega

theorem kvBlocks_pos (hpre : Pre P L mem0) : 0 < kvBlocks P := by
  have := hpre.skPos
  unfold kvBlocks
  omega

section Inputs

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : RingFacts L X)
  (htm : TmemFacts L X) (hinit : Rings.RingInit L X) (hcp : RingCopies P L X)
  (ha : AsyncFacts P L X) (hun : InputsUnwritten P X) (hsc : ScoreFacts L X) (htc : TcFacts L X)
  (htt : TcMmaThreadFacts L X) (hms : MmaStepFacts P L X) (hu : MmaUseFacts P L X)
include hpre hX ht htm hinit hcp ha hun hsc htc htt hms hu

/-- **Element `(row, kk)` of A of a QK MMA** of stage `st` is `Q` of its tile's row `row` at
head-dimension index `16 qkStep + kk`. -/
theorem qk_a {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {cell : Cell} {st row kk : Nat} (hst : st < 2)
    (hi : X.MmaIssue i d s acc mask) (hops : X.async.mmaOperands i = some ops)
    (hc : X.MmaCell i cell) (hS : InS st cell) (hrow : row < 256) (hkk : kk < 16) :
    Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row kk = .ok
      (P.q (tileBatch L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
        (tileHead L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
        (tileRow L i.1 (sCommits L X i.1 st i.2 / kvBlocks P) st + row)
        (16 * qkStep L X i.1 st i.2 + kk)) := by
  have haT := htc.qk_smem hst hi hc hS
  obtain ⟨-, -, hsa, -, hq, -⟩ := hu.qk hst hi hc hS
  have hj := (hms.qk_step hst hi hc hS).1
  have hD : s.descriptor = qkDesc := qkDesc_eq ((htt.mma_desc hi).2.1 haT)
  rw [qStepStart_eq] at hsa
  have hbl := qk_a_byteLoc hD haT hsa (boxBase_mod hpre (b := .qFull ⟨st, hst⟩) rfl _)
    (r := row / 128) (y := row % 128) (k := kk) (z := 0) (by omega) (by omega) hkk (by decide)
  rw [show 32 * (128 * (row / 128) + row % 128) + 2 * kk + 0 = 2 * (row * 16 + kk) by omega]
    at hbl
  obtain ⟨g, -, cnt, -, -, -, -, hcta, huse, hjb, hz⟩ :=
    element_at hpre hX ht htm hinit hcp ha hun htc htt hi hops false (b := .qFull ⟨st, hst⟩) rfl
      (jb := qkStep L X i.1 st i.2 / 4) (x0 := 16 * (qkStep L X i.1 st i.2 % 4) + kk)
      (y0 := row % 128) (by simp only [FBar.copies]; omega) (by omega)
      (by simp only [FBar.copyBytes]; omega) hbl
  obtain ⟨h2c, hr, hcl, hrk⟩ := pair_half hpre hsc htc htt hi (r := row / 128) (by omega) hcta
  rw [← hcta, readUse_eq h2c, show (FBar.qFull ⟨st, hst⟩).partner = .qEmpty ⟨st, hst⟩ from rfl,
    hq] at huse
  have hcc := copyCoords_eq (P := P) hcl huse
  simp only [FBar.copies] at huse hjb
  refine element_of_bytes fun z hz2 => ?_
  have h := hz z hz2
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [h]
  simp only [inputValue, copyBatch, copyHead, copyRow, copyCol, hcc, useItem, FBar.copies, hjb,
    hr, tileBatch, tileHead, tileRow, tileBlock, hrk]
  congr 5 <;> omega

/-- **Element `(col, kk)` of B of a QK MMA** of stage `st` is `K` of its visit's key `col` at
head-dimension index `16 qkStep + kk`. -/
theorem qk_b {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {cell : Cell} {st col kk : Nat} (hst : st < 2)
    (hi : X.MmaIssue i d s acc mask) (hops : X.async.mmaOperands i = some ops)
    (hc : X.MmaCell i cell) (hS : InS st cell) (hcol : col < 128) (hkk : kk < 16) :
    Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b col kk = .ok
      (P.k (tileBatch L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
        (tileHead L i.1 (sCommits L X i.1 st i.2 / kvBlocks P))
        (visitKey P (sCommits L X i.1 st i.2 % kvBlocks P) col)
        (16 * qkStep L X i.1 st i.2 + kk)) := by
  have haT := htc.qk_smem hst hi hc hS
  obtain ⟨sl, hsl, -, hsb, -, hkv⟩ := hu.qk hst hi hc hS
  have hj := (hms.qk_step hst hi hc hS).1
  have hD : s.descriptor = qkDesc := qkDesc_eq ((htt.mma_desc hi).2.1 haT)
  rw [kStepStart_eq hsl] at hsb
  have hbl := qk_b_byteLoc hD hsb (boxBase_mod hpre (b := .kvFull sl) rfl _)
    (r := col / 64) (y := col % 64) (k := kk) (z := 0) (by omega) (by omega) hkk (by decide)
  rw [show 32 * (64 * (col / 64) + col % 64) + 2 * kk + 0 = 2 * (col * 16 + kk) by omega] at hbl
  have hcp2 : (FBar.kvFull sl).copies = 2 := by simp [FBar.copies, hsl]
  obtain ⟨g, -, cnt, -, -, -, -, hcta, huse, hjb, hz⟩ :=
    element_at hpre hX ht htm hinit hcp ha hun htc htt hi hops true (b := .kvFull sl) rfl
      (jb := qkStep L X i.1 st i.2 / 4) (x0 := 16 * (qkStep L X i.1 st i.2 % 4) + kk)
      (y0 := col % 64) (by rw [hcp2]; omega) (by omega)
      (by simp only [FBar.copyBytes, hsl, ↓reduceIte]; omega) hbl
  obtain ⟨h2c, hr, hcl, -⟩ := pair_half hpre hsc htc htt hi (r := col / 64) (by omega) hcta
  rw [← hcta, readUse_eq h2c, show (FBar.kvFull sl).partner = .kvEmpty sl from rfl] at huse
  have hcc := copyCoords_eq (P := P) hcl huse
  obtain ⟨hit, hvis⟩ := kv_use (kvBlocks_pos hpre) (.inl hkv)
  rw [hcp2] at huse hjb
  refine element_of_bytes fun z hz2 => ?_
  have h := hz z hz2
  simp only [↓reduceIte] at h
  rw [h]
  simp only [inputValue, copyBatch, copyHead, copyRow, copyCol, hcc, useItem, useBlock, hsl,
    ↓reduceIte, hcp2, huse, hjb, hr, hit, hvis, tileBatch, tileHead, visitKey]
  congr 5 <;> omega

/-- **Element `(col, kk)` of B of a PV MMA** of stage `st` is `V` of its visit's key
`16 pvStep + kk` at head-dimension index `col`. -/
theorem pv_b {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {cell : Cell} {st col kk : Nat} (hst : st < 2)
    (hi : X.MmaIssue i d s acc mask) (hops : X.async.mmaOperands i = some ops)
    (hc : X.MmaCell i cell) (hO : InO st cell) (hcol : col < 128) (hkk : kk < 16) :
    Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b col kk = .ok
      (P.v (tileBatch L i.1 ((pPolls L X i.1 st i.2 - 1) / kvBlocks P))
        (tileHead L i.1 ((pPolls L X i.1 st i.2 - 1) / kvBlocks P))
        (visitKey P ((pPolls L X i.1 st i.2 - 1) % kvBlocks P)
          (16 * pvStep L X i.1 st i.2 + kk)) col) := by
  have haT : s.aTmem.isSome = true := (hsc.pv_polls hi hc hO).2.2.1
  obtain ⟨sl, hsl, hsb, hkv⟩ := hu.pv hst hi hc hO
  have hj := (hms.pv_step hst hi hc hO).1
  have hD : s.descriptor = pvDesc := pvDesc_eq ((htt.mma_desc hi).2.2 haT)
  rw [vStepStart_eq] at hsb
  have hbl := pv_b_byteLoc hD hsb (boxBase_mod hpre (b := .kvFull sl) rfl _)
    (r := col / 64) (y := col % 64) (k := kk) (z := 0) (by omega) (by omega) hkk (by decide)
  rw [show 32 * (64 * (col / 64) + col % 64) + 2 * kk + 0 = 2 * (col * 16 + kk) by omega] at hbl
  have hs' : ¬ sl.val % 2 = 0 := by omega
  have hcp1 : (FBar.kvFull sl).copies = 1 := by simp [FBar.copies, hs']
  obtain ⟨g, -, cnt, -, -, -, -, hcta, huse, -, hz⟩ :=
    element_at hpre hX ht htm hinit hcp ha hun htc htt hi hops true (b := .kvFull sl) rfl
      (jb := 0) (x0 := col % 64) (y0 := 16 * pvStep L X i.1 st i.2 + kk) (by rw [hcp1]; omega)
      (by omega) (by simp only [FBar.copyBytes, hs', ↓reduceIte]; omega) hbl
  obtain ⟨h2c, hr, hcl, -⟩ := pair_half hpre hsc htc htt hi (r := col / 64) (by omega) hcta
  rw [← hcta, readUse_eq h2c, show (FBar.kvFull sl).partner = .kvEmpty sl from rfl] at huse
  have hcc := copyCoords_eq (P := P) hcl huse
  obtain ⟨hit, hvis⟩ := kv_use (kvBlocks_pos hpre) (.inr hkv)
  refine element_of_bytes fun z hz2 => ?_
  have h := hz z hz2
  simp only [↓reduceIte] at h
  rw [h]
  simp only [inputValue, copyBatch, copyHead, copyRow, copyCol, hcc, useItem, useBlock, hs',
    ↓reduceIte, huse, hr, hit, hvis, tileBatch, tileHead, visitKey]
  congr 5
  omega

/-- **SmemInputs**: the shared operand elements of every completed MMA are the FP16 inputs of
its tile and K step. -/
theorem smemInputs : ValuesOps.SmemInputs P L X where
  qkA hst hi _ hops hc hS hrow hkk :=
    qk_a hpre hX ht htm hinit hcp ha hun hsc htc htt hms hu hst hi hops hc hS hrow hkk
  qkB hst hi _ hops hc hS hcol hkk :=
    qk_b hpre hX ht htm hinit hcp ha hun hsc htc htt hms hu hst hi hops hc hS hcol hkk
  pvB hst hi _ hops hc hO hcol hkk :=
    pv_b hpre hX ht htm hinit hcp ha hun hsc htc htt hms hu hst hi hops hc hO hcol hkk

end Inputs

end ValuesInputs

end
end PTX.Kernels.FlashAttn4Fwd.Proof

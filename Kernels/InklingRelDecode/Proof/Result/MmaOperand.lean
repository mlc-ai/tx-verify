-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaEvents
public import Kernels.InklingRelDecode.Proof.Result.MmaCopy
public import Kernels.InklingRelDecode.Proof2.Lib.LoaderPage

@[expose] public section

/-!
# The operands of the MMAs are the intended data (part (a))

The bytes the MMA warp's MMAs read from shared memory are the bf16 values `Spec` names:

* `qk_b_element`: element `(n, kk)` of the B operand of QK MMA `j` of iteration `i`, key row
  `n < 128` and `kk < 16`, is the cache's K value `kVal r kvh (128 (split + i · num_splits) + n)
  (16 j + kk)`: key `n` of block `i` of the split, head-dimension index `16 j + kk`;
* `pv_b_element`: element `(n, kk)` of the B operand of PV MMA `j` of iteration `i`, head-dimension
  column `n < 128` and `kk < 16`, is the V value `vVal r kvh (128 (split + (i - 1) · num_splits) +
  16 j + kk) n`: key `16 j + kk` of block `i - 1`, column `n`;
* `qk_a_element`: element `(r, kk)` of the A operand of QK MMA `j`, a valid row `r`, is the query
  `qElem` of the row's token and head at index `16 j + kk`.

All three read the byte of the one write that precedes the read, so each is the byte-level chain
`MMA read ← (order) ← write ← value`: the K/V bytes through `KvCopies`, `KvOrder` and the copy's
tile semantics (`kv_copy_written`: the swizzle `copy_loc_kv` and the operand address
`qk_b_loc_eq`, `pv_b_loc_eq` agree), the Q bytes through `QTile`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof PTX.TcMma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc)
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The cache element of key `n` (`< 128`) and head-dimension index `d` of block `i` of the
thread's CTA, K (`isV = 0`) or V (`isV = 1`): the slab `n / 64` of the block's page, row
`n % 64`. -/
def kvElem (Q : Params) (L : Launch) (g i isV n d : Nat) : ℝ :=
  Q.kv (Q.page (reqOf L g) (2 * blkOf Q L g i + n / 64) * Q.pageRows + kvhOf L g * Q.headRows +
    n % 64) (kvhOf L g * Q.headCols + 128 * isV + d)

theorem kvElem_k (Q : Params) (L : Launch) (g i n d : Nat) :
    kvElem Q L g i 0 n d = Q.kVal (reqOf L g) (kvhOf L g) (128 * blkOf Q L g i + n) d := by
  simp only [kvElem, Params.kVal, Params.kvRow]
  have e1 : (128 * blkOf Q L g i + n) / 64 = 2 * blkOf Q L g i + n / 64 := by omega
  have e2 : (128 * blkOf Q L g i + n) % 64 = n % 64 := by omega
  rw [e1, e2]
  simp

theorem kvElem_v (Q : Params) (L : Launch) (g i n d : Nat) :
    kvElem Q L g i 1 n d = Q.vVal (reqOf L g) (kvhOf L g) (128 * blkOf Q L g i + n) d := by
  simp only [kvElem, Params.vVal, Params.kvRow, headDim]
  have e1 : (128 * blkOf Q L g i + n) / 64 = 2 * blkOf Q L g i + n / 64 := by omega
  have e2 : (128 * blkOf Q L g i + n) % 64 = n % 64 := by omega
  rw [e1, e2]

/-- **The K/V byte an MMA reads.** An MMA of block `i < num_iters` of thread `g`'s CTA reads, at
operand byte `idx` of B, the location of byte `z` of element `(n, d)` of the K or V tile of ring
slot `i % 3`: it observes byte `z` of the bf16 value `kvElem` of the element. -/
theorem kv_byte (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hc : KvCopies Q L X) (ho : KvOrder Q L X)
    {g i : Nat} (hg : g < L.threads) (hi : i < Q.numIters (reqOf L g) (splitOf L g))
    {m : EvId} {d : Mma.D} (hAt : AtMma Q L X m d)
    (hblk : MmaBlock d i) {pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (hissue : X.get m = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {ops : AsyncCopy.MmaOperands}
    (hops : X.async.mmaOperands m = some ops) {isV n e z idx : Nat} (hV : isV ≤ 1)
    (hn : n < 128) (he : e < 128) (hz : z < 2)
    (hl : sp.byteLoc .b idx = some ⟨.shared, g / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩) :
    ops.b[idx]? = some (some ((Value.float .bf16 (kvElem Q L g i isV n e)).byteAt z)) := by
  obtain ⟨obs, hr, hget⟩ := hX.mma_read_exists (isB := true) ⟨pc, hissue⟩ hops (by simpa using hl)
  simp only [↓reduceIte] at hget
  obtain ⟨c, o, a, bar, hc1, hc2, hTI, hobs, hcb, hspec⟩ := hc.exists_copy isV (n / 64) (e / 64)
    hg hi hV (by omega) (by omega)
  have hsb := hpre.sharedAlignment
  have hwl : TensorCopy.writeLoc o.spec (e % 64) (n % 64) z =
      some ⟨.shared, g / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩ := by
    rw [hspec]
    exact copy_loc_kv Q _ _ isV _ _ _ bar (by omega) hn he hz
  obtain ⟨⟨b, hwb⟩, hv, horder⟩ := ho.order hAt hblk hcb hobs hTI hwl hr
  have hobsb : obs = some b := by
    have hw : X.MemWrites (.async c (.write (.load (e % 64) (n % 64) z)))
        { loc := ⟨.shared, g / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩, size := 1 } [b] :=
      ⟨o, a, b, hobs, hTI, hwl, hwb, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have := read_byte_of_write hX hr hw (by simp [Acc.Covers, Loc.InRange]) hv horder
    simpa [wbyte] using this
  obtain ⟨hgx, hgy, hgz⟩ := ProA.cta_lt hpre hg
  have hspl := hpre.splitsPos
  have hblk' := blk_lt (s := splitOf L g) hspl hi
  have hbq : 2 * blkOf Q L g i + n / 64 < 2 * Q.blocks (reqOf L g) := by
    unfold blkOf
    omega
  have hval := kv_copy_written hpre hf hX (r := reqOf L g) (s := 2 * blkOf Q L g i + n / 64)
    (kvh := kvhOf L g) (isV := isV) (hh := e / 64) hgz hbq hgy hV (by omega) hobs
    (by rw [hspec]) (by omega) (by omega) hz hwb
  rw [hget, hobsb, hval]
  simp only [kvElem, Option.some.injEq]
  congr 3
  omega

/-- The index of byte `z` of element `(n, kk)` of an operand: `32 n + 2 kk + z`, two bytes per
element and 16 elements per row. -/
theorem idx_eq (n kk z : Nat) : 32 * n + 2 * kk + z = 2 * (n * 16 + kk) + z := by ring

/-- **The B operand of a QK MMA is the K tile.** Element `(n, kk)` of QK MMA `j` of iteration `i`
(`n` a key row of the block, `kk` an index within the MMA's 16 head-dimension indices) is the
cache's K value of key `128 (split + i · num_splits) + n` at head-dimension index `16 j + kk`. -/
theorem qk_b_element (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hc : KvCopies Q L X) (ho : KvOrder Q L X)
    (hw : MmaWords Q L X) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    {d : Mma.D} {P : Loader.Pro} (hσ : St Q L X g k = some (some (.w (.mma d P)))) {j : Fin 8}
    (hs : d.site = .qk j) {ops : AsyncCopy.MmaOperands}
    (hops : X.async.mmaOperands (g, k) = some ops) {n kk : Nat} (hn : n < 128) (hk : kk < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b n kk =
      .ok (Q.kVal (reqOf L g) (kvhOf L g) (128 * blkOf Q L g d.i + n) (16 * j.val + kk)) := by
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d', P', j', hσ', hI, hs', hq, -, -, -⟩ | ⟨d', P', j', hσ', hI, hs', -⟩
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    have hjj : j = j' := by
      have := hs.symm.trans hs'
      simpa using this
    subst hjj
    have hi : d.i < Q.numIters (reqOf L g) (splitOf L g) := by
      rw [← hw.iters (m := (g, k)) hg ⟨P, hσ⟩ (Or.inl (by simp [Mma.QkSite, hs]))]
      exact (hI.qk (by simp [Mma.QkSite, hs])).1
    have hE := EvW.mmEnv_of_pre hpre
    have hbyte : ∀ z, z < 2 → ops.b[2 * (n * 16 + kk) + z]? =
        some (some ((Value.float .bf16 (kvElem Q L g d.i 0 n (16 * j.val + kk))).byteAt z)) := by
      intro z hz
      rw [← idx_eq]
      refine kv_byte hpre hf hX hc ho hg hi (m := (g, k)) ⟨P, hσ⟩ (Or.inl ⟨j, hs, rfl⟩) he hops
        (isV := 0) (by omega) hn (by omega) hz ?_
      rw [qk_b_loc_eq hE hq.desc (Nat.mod_lt _ (by omega)) j.isLt hq.b hn hk hz, hq.low]
    rw [← kvElem_k]
    exact element_bf16 (hbyte 0 (by omega)) (hbyte 1 (by omega))
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    rw [hs] at hs'
    exact absurd hs' (by simp)

/-- **The B operand of a PV MMA is the V tile.** Element `(n, kk)` of PV MMA `j` of iteration `i`
(`n` a head-dimension column, `kk` an index within the MMA's 16 keys) is the cache's V value of
key `128 (split + (i - 1) · num_splits) + 16 j + kk` of block `i - 1`, at column `n`. -/
theorem pv_b_element (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hc : KvCopies Q L X) (ho : KvOrder Q L X)
    (hw : MmaWords Q L X) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    {d : Mma.D} {P : Loader.Pro} (hσ : St Q L X g k = some (some (.w (.mma d P)))) {j : Fin 8}
    (hs : d.site = .pv j) {ops : AsyncCopy.MmaOperands}
    (hops : X.async.mmaOperands (g, k) = some ops) {n kk : Nat} (hn : n < 128) (hk : kk < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b n kk =
      .ok (Q.vVal (reqOf L g) (kvhOf L g) (128 * blkOf Q L g (d.i - 1) + (16 * j.val + kk)) n) := by
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d', P', j', hσ', hI, hs', -⟩ | ⟨d', P', j', hσ', hI, hs', hq, -, -, -⟩
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    rw [hs] at hs'
    exact absurd hs' (by simp)
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    have hjj : j = j' := by
      have := hs.symm.trans hs'
      simpa using this
    subst hjj
    obtain ⟨h1, h2, -⟩ := hI.pv (by simp [Mma.PvSite, hs])
    have hi : d.i - 1 < Q.numIters (reqOf L g) (splitOf L g) := by
      rw [← hw.iters (m := (g, k)) hg ⟨P, hσ⟩ (Or.inr (by simp [Mma.PvSite, hs]))]
      omega
    have hE := EvW.mmEnv_of_pre hpre
    have hbyte : ∀ z, z < 2 → ops.b[2 * (n * 16 + kk) + z]? =
        some (some ((Value.float .bf16
          (kvElem Q L g (d.i - 1) 1 (16 * j.val + kk) n)).byteAt z)) := by
      intro z hz
      rw [← idx_eq]
      refine kv_byte hpre hf hX hc ho hg hi (m := (g, k)) ⟨P, hσ⟩
        (Or.inr ⟨j, hs, by omega⟩) he hops (isV := 1) (by omega) (by omega) hn hz ?_
      rw [pv_b_loc_eq hE hq.desc (Nat.mod_lt _ (by omega)) j.isLt hq.b hn hk hz, hq.low]
    rw [← kvElem_v]
    exact element_bf16 (hbyte 0 (by omega)) (hbyte 1 (by omega))

/-- **The A operand of a QK MMA is the Q tile.** Element `(r, kk)` of QK MMA `j`, a valid row `r`
of the tile and an index `kk` within the MMA's 16 head-dimension indices, is the bf16 query of the
row's token and head at index `16 j + kk`. -/
theorem qk_a_element (hpre : Pre Q L mem0) (hf : ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hq : QTile Q L X) {g k pc dst : Nat}
    {sp : OperandSpec} {acc : Bool} {mask : List Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) {j : Fin 8} (hs : d.site = .qk j)
    {ops : AsyncCopy.MmaOperands} (hops : X.async.mmaOperands (g, k) = some ops) {r kk : Nat}
    (hr : QRowValid Q L g r) (hk : kk < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk =
      .ok (qElem Q L g r (16 * j.val + kk)) := by
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d', P', j', hσ', hI, hs', hqo, -, -, -⟩ | ⟨d', P', j', hσ', hI, hs', -⟩
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    have hjj : j = j' := by
      have := hs.symm.trans hs'
      simpa using this
    subst hjj
    have hE := EvW.mmEnv_of_pre hpre
    have hbyte : ∀ z, z < 2 → ops.a[2 * (r * 16 + kk) + z]? =
        some (some ((Value.float .bf16 (qElem Q L g r (16 * j.val + kk))).byteAt z)) := by
      intro z hz
      rw [← idx_eq]
      obtain ⟨w, a, bs, hwr, hcov, hbw, hord⟩ := hq.tile hg hr (d := 16 * j.val + kk)
        (by omega) hz
      have hl : sp.byteLoc .a (32 * r + 2 * kk + z) =
          some ⟨.shared, g / L.block, qAddr L.sharedBase r (16 * j.val + kk) z⟩ := by
        rw [qk_a_loc_eq hE hqo.desc j.isLt hqo.a hqo.aTmem (by have := hr.1; omega) hk hz,
          hqo.low]
      obtain ⟨obs, hrd, hget⟩ := hX.mma_read_exists (isB := false) ⟨pc, he⟩ hops
        (by simpa using hl)
      simp only [Bool.false_eq_true, ↓reduceIte] at hget
      obtain ⟨hv, horder⟩ := hord (m := (g, k)) ⟨P, hσ⟩ ⟨j, hs⟩ rfl hrd
      have hmw : X.MemWrites (.thread w) a bs := by
        show X.Writes w a bs ∨ ∃ old, X.Rmw w a old (some bs)
        exact Or.inl hwr
      have := read_byte_of_write hX hrd hmw hcov hv horder
      rw [hget, this, hbw]
    exact element_bf16 (hbyte 0 (by omega)) (hbyte 1 (by omega))
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    rw [hs] at hs'
    exact absurd hs' (by simp)

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma

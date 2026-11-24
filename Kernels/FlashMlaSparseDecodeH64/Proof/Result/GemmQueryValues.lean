-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmQuery
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmResults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GlobalFrame
import Lemmas.Order.Order
import Lemmas.Tensor.TensorReadSources

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Wg1Mma MmaDataTrace
open PTX.AsyncCopy

noncomputable section
set_option maxRecDepth 100000

section
variable {L : Launch}

private theorem queryCopy_snapshot_shape {g : Nat} {issue : Fin 16} {X : Execution} {e : EvId}
    {ops : MmaOperands} (ht : TcEffectsOk X) (hi : X.CpIssue e (queryCopySpec L g issue))
    (ho : X.async.mmaOperands e = some ops) : ops.a.length = 4096 := by
  have hstarted : X.async.mmaStarted e = true := by
    simp only [Snapshot.mmaStarted, ho, Option.isSome_some]
  obtain ⟨_, hget⟩ := hi
  rcases ht.1 e hstarted with
    ⟨_, _, _, _, _, ⟨_, he⟩, _, _, _, _⟩ |
    ⟨_, _, ⟨_, he⟩, ho', ha, _⟩ | ⟨_, _, ⟨_, he⟩, _, _, _⟩
  · cases Option.some.inj (hget.symm.trans he)
  · cases Option.some.inj (hget.symm.trans he)
    cases Option.some.inj (ho'.symm.trans ho)
    exact ha
  · cases Option.some.inj (hget.symm.trans he)

/-- Each byte of the query copy snapshot is the value of its actual shared read. -/
theorem queryCopy_read {g : Nat} {issue : Fin 16} {X : Execution} {e : EvId} {ops : MmaOperands}
    (ht : TcEffectsOk X) (hi : X.CpIssue e (queryCopySpec L g issue))
    (ho : X.async.mmaOperands e = some ops) (row : Fin 128) (k : Fin 16) (b : Fin 2) :
    let n := 2 * (row.val * 16 + k.val) + b.val
    let l : Loc := ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
      (kvLinearByte L 0 (row.val % 64) (qkFeature issue row k) b.val)⟩
    ∃ byte, X.MemReads (.async e (.mmaRead false n)) { loc := l, size := 1 } [byte] ∧
      ops.a[n]? = some byte := by
  let n := 2 * (row.val * 16 + k.val) + b.val
  have hlim : n < 4096 := by unfold n; omega
  have hn : n < ops.a.length := (queryCopy_snapshot_shape ht hi ho).symm ▸ hlim
  have hget : ops.a[n]? = some (ops.a[n]'hn) := List.getElem?_eq_getElem hn
  have hdiv : n / 4096 = 0 := Nat.div_eq_of_lt hlim
  have hmod : n % 4096 = n := Nat.mod_eq_of_lt hlim
  refine ⟨_, ⟨_, ⟨.inr ⟨queryCopySpec L g issue, 0, ctaOf L g, hi, rfl, rfl, hdiv, ?_⟩,
    ops, ho, hget⟩, rfl, rfl⟩, hget⟩
  change TcCopy.byteLoc .s128x256b (keyDescriptor L 0 issue) (ctaOf L g) (n % 4096) = _
  rw [hmod]
  exact queryCopyByteLoc L g issue row k b

/-- A one-byte operand read that selects the actual one-byte producer gets its stored payload. -/
theorem mmaByte_of_rf {X : Execution} {mem0 : Mem0}
    (hX : Consistent L kernel Assumptions.all mem0 X) {e w : Ref} {l : Loc} {observed : Option Byte}
    {value : Byte} (hr : X.MemReads e { loc := l, size := 1 } [observed])
    (hw : X.MemWrites w { loc := l, size := 1 } [value]) (hf : X.rf e 0 = some w) :
    observed = some value := by
  have h := (hX.rf e _ _ hr).2 0 (by exact Nat.zero_lt_succ 0)
  rw [hf] at h
  obtain ⟨dst, written, hw', _, hv⟩ := h
  obtain ⟨hfp, rfl⟩ := hw.unique hw'
  have hl : dst.loc = l := hfp.1.symm
  simpa only [List.getElem?_cons_zero, wbyte, hl, Loc.at, Nat.add_zero, Nat.sub_self,
    Option.some.injEq] using hv

private def queryWord (lo hi : ℝ) : Value :=
  .pair (.pair (TcCopy.byteValue (.float .bf16 lo, 0)) (TcCopy.byteValue (.float .bf16 lo, 1)))
    (.pair (TcCopy.byteValue (.float .bf16 hi, 0)) (TcCopy.byteValue (.float .bf16 hi, 1)))

private theorem queryWord_byte (lo hi : ℝ) (half byte : Fin 2) :
    (queryWord lo hi).byteAt (2 * half.val + byte.val) =
      (.float .bf16 (if half.val = 0 then lo else hi), byte.val) := by
  fin_cases half <;> fin_cases byte <;> rfl

/-- Two BF16 elements in a copy snapshot leave their four original bytes together in one cell. -/
private theorem queryCopy_word {g : Nat} {X : Execution} {e : EvId} {issue : Fin 16}
    {ops : MmaOperands} {row : Fin 128} {q : Nat → ℝ} (hi : X.CpIssue e (queryCopySpec L g issue))
    (ho : X.async.mmaOperands e = some ops) (hq : Bf16Operand ops.a row.val q) (w : Fin 8) :
    let sp := queryCopySpec L g issue
    let cell := TcCopy.cell sp.shape sp.address (ctaOf L g) row.val (32 * row.val + 4 * w.val)
    TcMma.CpValue X e cell (queryWord (q (2 * w.val)) (q (2 * w.val + 1))) := by
  let base := row.val * 32 + 4 * w.val
  have hget (half byte : Fin 2) :
      ops.a.getD (base + (2 * half.val + byte.val)) none =
        some (.float .bf16 (q (2 * w.val + half.val)), byte.val) := by
    have hk : 2 * w.val + half.val < 16 := by omega
    have heq : base + (2 * half.val + byte.val) =
        2 * (row.val * 16 + (2 * w.val + half.val)) + byte.val := by
      unfold base
      omega
    rw [List.getD_eq_getElem?_getD, heq, hq _ hk _ byte.isLt]
    rfl
  refine ⟨queryCopySpec L g issue, 0, ctaOf L g, ops, row.val, w.val, row.val, hi,
    rfl, ho, row.isLt, (by simp [queryCopySpec, TcCpShape.rowBytes]),
    by simp [queryCopySpec, TcCpShape.lanes], ?_, ?_⟩
  · change TcCopy.cell .s128x256b (qCopyCol issue) (ctaOf L g) row.val
      (32 * row.val + 4 * w.val) =
      TcCopy.cell .s128x256b (qCopyCol issue) (ctaOf L g) row.val (row.val * 32 + 4 * w.val)
    rw [Nat.mul_comm 32]
  · rw [TcCopy.cpWord_none rfl]
    have a : ops.a.getD base none = some (.float .bf16 (q (2 * w.val)), 0) := by
      simpa using hget 0 0
    have b : ops.a.getD (base + 1) none = some (.float .bf16 (q (2 * w.val)), 1) := by
      simpa using hget 0 1
    have c : ops.a.getD (base + 2) none = some (.float .bf16 (q (2 * w.val + 1)), 0) := by
      simpa using hget 1 0
    have d : ops.a.getD (base + 3) none = some (.float .bf16 (q (2 * w.val + 1)), 1) := by
      simpa using hget 1 1
    change TcCopy.word .s128x256b ops.a row.val w.val = _
    unfold TcCopy.word
    change (do
      let x0 ← ops.a.getD base none
      let x1 ← ops.a.getD (base + 1) none
      let x2 ← ops.a.getD (base + 2) none
      let x3 ← ops.a.getD (base + 3) none
      pure (Value.pair (.pair (TcCopy.byteValue x0) (TcCopy.byteValue x1))
        (.pair (TcCopy.byteValue x2) (TcCopy.byteValue x3)))) = _
    rw [a, b, c, d]
    rfl

private theorem query_copy_cell_value {g : Nat} {X : Execution} {issue : Fin 16} {cp : EvId}
    {qOps : MmaOperands} {row : Fin 128} {q : Nat → ℝ} (hc : X.CpIssue cp (queryCopySpec L g issue))
    (hco : X.async.mmaOperands cp = some qOps) (hq : Bf16Operand qOps.a row.val q) (w : Fin 8) :
    TcMma.CpValue X cp ⟨ctaOf L g, row.val, qkACol issue + w.val⟩
      (queryWord (q (2 * w.val)) (q (2 * w.val + 1))) := by
  have hCell : TcCopy.cell (queryCopySpec L g issue).shape (queryCopySpec L g issue).address
      (ctaOf L g) row.val (32 * row.val + 4 * w.val) =
      ⟨ctaOf L g, row.val, qkACol issue + w.val⟩ := by
    dsimp [queryCopySpec, TcCopy.cell, TcCpShape.rowBytes, qCopyCol, qkACol, tmemQ]
    congr 1 <;> omega
  exact hCell ▸ queryCopy_word hc hco hq w

/-- Every actual query-copy cell contains the two query elements of its word. -/
theorem exists_query_copy_cell_value {g : Nat} {X : Execution} {issue : Fin 16} {cp : EvId}
    {qOps : MmaOperands} {row : Fin 128} {q : Nat → ℝ} (hc : X.CpIssue cp (queryCopySpec L g issue))
    (hco : X.async.mmaOperands cp = some qOps) (hq : Bf16Operand qOps.a row.val q) (w : Fin 8) :
    ∃ v, TcMma.CpValue X cp ⟨ctaOf L g, row.val, qkACol issue + w.val⟩ v :=
  ⟨_, query_copy_cell_value hc hco hq w⟩

/-- The A operand of QK recovers the logical BF16 elements from the actual query-copy cells if
the observed TMEM sources are those copies. -/
theorem queryA_from_copy {g block : Nat} {mem0 : Mem0} {X : Execution} {issue : Fin 16}
    {cp mma : EvId} {qOps mmaOps : MmaOperands} {row : Fin 128} {q : Nat → ℝ}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hc : X.CpIssue cp (queryCopySpec L g issue))
    (hm : X.MmaIssue mma tmemP (qkOperands L g block issue) (qkAccum issue) [0, 0, 0, 0])
    (hco : X.async.mmaOperands cp = some qOps) (hmo : X.async.mmaOperands mma = some mmaOps)
    (hq : Bf16Operand qOps.a row.val q)
    (hs : ∀ k : Fin 16,
      TcMma.ReadSource L X .a cp mma ⟨ctaOf L g, row.val, qkACol issue + k.val / 2⟩) :
    Bf16Operand mmaOps.a row.val q := by
  intro k hk b hb
  let k' : Fin 16 := ⟨k, hk⟩
  let b' : Fin 2 := ⟨b, hb⟩
  let w : Fin 8 := ⟨k / 2, by omega⟩
  let half : Fin 2 := ⟨k % 2, Nat.mod_lt _ (by decide)⟩
  let cell : TcMma.Cell := ⟨ctaOf L g, row.val, qkACol issue + k / 2⟩
  have hw : TcMma.Wrote L Assumptions.all X cp cell (queryWord (q (2 * w.val))
      (q (2 * w.val + 1))) := .inr (.inr (.inl (query_copy_cell_value hc hco hq w)))
  have hp : 2 * (k % 2) + b < (queryWord (q (2 * w.val)) (q (2 * w.val + 1))).bytes := by
    change 2 * (k % 2) + b < 4
    omega
  have hv := hX.tcRead.2 mma (2 * (row.val * 16 + k) + b) cell (2 * (k % 2) + b)
    cp _ mmaOps ⟨_, _, _, _, hm, qkQueryByte L g block issue row k' b'⟩ (hs k') hw hmo hp
  have hbyte := queryWord_byte (q (2 * w.val)) (q (2 * w.val + 1)) half b'
  change (queryWord (q (2 * w.val)) (q (2 * w.val + 1))).byteAt (2 * (k % 2) + b) =
    (.float .bf16 (if k % 2 = 0 then q (2 * (k / 2)) else q (2 * (k / 2) + 1)), b) at hbyte
  rw [hbyte] at hv
  have hval : (if k % 2 = 0 then q (2 * (k / 2)) else q (2 * (k / 2) + 1)) = q k := by
    split <;> congr 1 <;> omega
  rw [hval] at hv
  exact hv
end

/-- Output stores never cover a source byte of a query tile. -/
theorem queryTile_globalNoWrite {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (tile : Fin 8) (x h : Fin 64) (b : Fin 2) {addr : Nat}
    (haddr : (queryTmaSpec P L g tile).toTensorBox.globalAddress (queryTileSlot P L g tile x h b)
      = some addr) :
    ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers ⟨.global, 0, addr⟩ := by
  have hd : qCoord tile + x.val < 512 := by unfold qCoord; omega
  let Q := { P with outBase := P.qBase }
  let l := (oLoc Q (batchOf L g) (queryOf L g) h.val (qCoord tile + x.val)).at b.val
  have hl : l = ⟨.global, 0, addr⟩ := by
    rw [queryTile_global hpre hg] at haddr
    have he := Option.some.inj haddr
    simp only [l, oLoc, Loc.at, Q]
    rw [← he]
    congr 1
    omega
  have hself : l.InRange 1 l := ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩
  have hr := outputRange (P := Q) (batchOf_lt hpre hg) (queryOf_lt hpre hg)
    h.isLt hd b.isLt hself
  change P.qBase ≤ l.addr ∧ l.addr < P.qBase + tensorBytes P at hr
  intro w a bytes hw hc
  rw [← hl] at hc
  rcases actual_global_write_range hpre hs hX hw hc rfl with ho | hlse
  · rcases hpre.qApartO <;> omega
  · rcases hpre.inputApartLse <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

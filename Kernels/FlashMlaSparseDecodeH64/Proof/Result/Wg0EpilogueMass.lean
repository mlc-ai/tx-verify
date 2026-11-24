-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPvRun
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0RunningPeak
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Inf
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ReferencePrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RowTotalHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount

@[expose] public section

/-! # The final row normalization and the actual LSE word -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0EpilogueMass

open PTX PTX.Proof PTX.Flow Wg0

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem length_bounds (hpre : Pre P L mem0) (g : Nat) :
    P.topkLen (Wg1Mma.batchOf L g) ≤ P.topk ∧
      P.extraTopkLen (Wg1Mma.batchOf L g) ≤ P.extra_topk := by
  have he := Wg1Mma.eOf_lt_b hpre (g := g)
  exact ⟨Wg2.topkLen_le hpre he, Wg2.extraTopkLen_le hpre he⟩

private theorem row_sum_nonneg (P : Params) (batch query head : Nat) :
    0 ≤ rowSum P batch query head :=
  add_nonneg (Finset.sum_nonneg (fun j _ => weight_nonneg P batch query head false j))
    (Finset.sum_nonneg (fun j _ => weight_nonneg P batch query head true j))

/-- The numerical row data shared by the LSE store and the normalized output cells. -/
structure RowMass (P : Params) (L : Launch) (X : Execution) (g : Nat) (d : Wg0.D) : Prop where
  last : d.block + 1 = blocksOf P L g
  ref : reference d = (actualRowRun P L X g (head L g)).c d.block
  mass : d.li = (actualRowRun P L X g (head L g)).l d.block
  empty : d.peak = ⊥ ↔ rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0

theorem RowMass.block_eq {g : Nat} {d : Wg0.D} (h : RowMass P L X g d) :
    d.block = blocks P (Wg1Mma.batchOf L g) - 1 := by
  have hb : d.block + 1 = blocks P (Wg1Mma.batchOf L g) := h.last
  omega

/-- Every actual output epilogue state retains the mass and the chosen final reference. -/
theorem of_state {g i : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site.needsRowTotal = true) : RowMass P L X g d := by
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  have hinv : Inv P L g d := hInv
  have hEpi : d.site.inEpilogue = true := by
    cases h : d.site <;> simp_all [Site.inEpilogue]
  have hLast := hinv.epilogueLast hEpi
  have hOrd : Wg0VoteCount.ordinal d = d.block + 1 := by
    cases h : d.site <;> simp_all [Wg0VoteCount.ordinal, Wg0VoteCount.afterVote]
  obtain ⟨_, v, _, _, mid, _, hVote, hState, hVoteSite, hBlock, hUpdate, hRef, _, _⟩ :=
    Wg0ReferencePrefix.after_vote hX hs ht he hd hOrd
  have hCanon : reference d = (actualRowRun P L X g (head L g)).c d.block := by
    exact hRef.trans (canonical_pv_vote_reference hpre hX hs ht _ _ rfl hVote
      ⟨.any, 2 ^ 32 - 1, v.voteTest, rfl⟩ hState hVoteSite hBlock hUpdate)
  obtain ⟨j, old, new, f, a, values, _, hOld, hReadSite, _, hKind, hRead, hNext,
      hLi, hPreserveRef, _, _⟩ :=
    Wg0RowTotalHistory.source ht (Frame.lt_of_get hX he) (PTX.len_of_get he).le hd hSite
  obtain ⟨hMass, _⟩ :=
    Wg0RunningPeak.lse_read_updates hpre hX hs ht hRead hKind hOld hReadSite hNext
  have hScaled : d.li = (2 : ℝ) ^ (-reference d) *
      rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) := by
    rw [hLi, hPreserveRef]
    exact hMass
  have hEmpty : d.peak = ⊥ ↔ rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0 := by
    rw [← (hinv.rowTotal hSite).2, hScaled, mul_eq_zero,
      or_iff_right (PTX.Numeric.two_rpow_pos _).ne']
  have hBound : d.block < blocks P (Wg1Mma.batchOf L g) := by
    exact Nat.lt_of_succ_le hLast.le
  obtain ⟨hMain, hExtra⟩ := length_bounds hpre g
  have hSum := (actualRowRun P L X g (head L g)).sum hBound
  rw [hLast, show blocksOf P L g = blocks P (Wg1Mma.batchOf L g) from rfl,
    sum_blockWeight_eq_rowSum P _ _ _ hMain hExtra, ← hCanon] at hSum
  exact ⟨hLast, hCanon, hScaled.trans hSum.symm, hEmpty⟩

/-- The actual LSE register is the specification on both branches of the empty-row selection. -/
theorem lse_register {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0) (h : RowMass P L X g d) :
    lseReg d = if rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0 then posInf
      else .float .f32 (lse P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g)) := by
  by_cases hz : rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0
  · simp [lseReg, h.empty.mpr hz, hz]
  · have hpos := lt_of_le_of_ne (row_sum_nonneg P _ _ _) (Ne.symm hz)
    have hPeak : d.peak ≠ ⊥ := fun hp => hz (h.empty.mp hp)
    obtain ⟨hMain, hExtra⟩ := length_bounds hpre g
    have hVal : lseValue d = lse P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) := by
      rw [lseValue, h.ref, h.mass, h.block_eq]
      exact (actualRowRun P L X g (head L g)).final_lse hMain hExtra hpos
    simp [lseReg, hPeak, hz, hVal]

/-- The actual global LSE write contains the specification's four bytes. -/
theorem lse_bytes_of_write {g i : Nat} {d : Wg0.D} {a : Acc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .lseStore) (hw : X.Writes (g, i) a (lseReg d).toBytes) (k : Fin 4) :
    (lseReg d).toBytes[k.val]? =
      some (if rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0 then infByte k.val
        else (Value.float .f32
          (lse P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g))).byteAt k.val) := by
  have h := of_state hpre hX hs ht hw.choose_spec hd (by simp [hsite])
  rw [lse_register hpre h]
  by_cases hz : rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0
  · simp [hz, Value.toBytes, infByte_eq, posInf, Value.bytes, Value.byteAt, k.isLt]
  · simp [hz, Value.toBytes, Value.bytes, FloatFmt.bytes, k.isLt]

/-- A final PV accumulator cell is normalized using the actual row total and reference. -/
theorem normalize_cell {g col : Nat} {d : Wg0.D} {v : ℝ}
    (hpre : Pre P L mem0) (h : RowMass P L X g d)
    (hv : v = (actualRowRun P L X g (head L g)).O d.block col) :
    oScale P L g d * v = attn P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) col := by
  let run := actualRowRun P L X g (head L g)
  obtain ⟨hMain, hExtra⟩ := length_bounds hpre g
  by_cases hz : rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0
  · have hl : d.li = 0 := by
      rw [h.mass, h.block_eq]
      have hsum := run.sum (lastBlock_lt P (Wg1Mma.batchOf L g))
      rwa [lastBlock_succ, sum_blockWeight_eq_rowSum P _ _ _ hMain hExtra, hz, mul_zero] at hsum
    rw [(run.final_empty hMain hExtra hz col).1]
    simp [oScale, hl]
  · have hpos := lt_of_le_of_ne (row_sum_nonneg P _ _ _) (Ne.symm hz)
    have hl : d.li ≠ 0 := by
      rw [h.mass, h.block_eq]
      exact run_l_ne_zero hMain hExtra hpos
    have hScale : oScale P L g d = 1 / (d.li + sinkTerm P L g d) := by simp [oScale, hl]
    rw [hScale, hv, one_div_mul_eq_div]
    cases hsink : P.sink (head L g) with
    | none =>
      simp only [sinkTerm, hsink, add_zero, h.mass, h.block_eq]
      exact run.final_noSink hMain hExtra hpos hsink col
    | some s =>
      simp only [sinkTerm, hsink, h.mass, h.ref, h.block_eq]
      exact run.final_sink hMain hExtra hpos hsink col

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0EpilogueMass

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualKvOperands
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.QueryActualOperands
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QkAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QkWriteOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmScoreLoads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerQkValues

@[expose] public section

/-! # The dot product of a completed actual QK block -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy Protocol MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A completed Tensor Core issue has a recorded operand snapshot. -/
theorem observed_operands_of_done (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} (hd : X.AsyncPresent i .mmaDone) :
    ∃ ops, X.async.mmaOperands i = some ops := by
  have hstarted := hX.tma.2.1.2 i hd
  cases hobs : X.async.mmaOperands i with
  | none => simp [Snapshot.mmaStarted, hobs] at hstarted
  | some ops => exact ⟨ops, rfl⟩

/-- Every output cell of the last QK issue of a notified commit has its actual FP32 value.
The two halves add to the full sparse dot product. -/
theorem qk_block_of_commit {g c tag : Nat} {d : Wg1Mma.D} {sp : TcCommit.Spec}
    {rank : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hc : X.get (g, c) = some ⟨tag, .tc (.commit sp)⟩)
    (hd : Frame.stateAt (Machine.code P L) X g c = some (some (.mma d)))
    (hsite : d.site = .qkCommit) (hn : rank ∈ X.tcNotified (g, c))
    (head slot : Fin 64) :
    ∃ j lo hi,
      j + 1 = c ∧
      TcMma.Result L Assumptions.all X (g, j)
        ⟨ctaOf L g, head.val, Wg1Mma.tmemP + slot.val⟩ (.float .f32 lo) ∧
      TcMma.Result L Assumptions.all X (g, j)
        ⟨ctaOf L g, head.val + 64, Wg1Mma.tmemP + slot.val⟩ (.float .f32 hi) ∧
      lo + hi = blockDot P L g head.val slot.val (Wg2.gatheredByte P L g d.i) ∧
      lo = blockHalfDot P L g head slot 0 (Wg2.gatheredByte P L g d.i) ∧
      hi = blockHalfDot P L g head slot 1 (Wg2.gatheredByte P L g d.i) := by
  classical
  obtain ⟨visit, hVisit, hPrevious⟩ := QkAccumulatorSource.of_commit hpre hX hs hc hd hsite
  have hObs (k : Fin 16) : ∃ ops, X.async.mmaOperands (g, visit k) = some ops := by
    have hk := k.isLt
    have hLess := (hVisit k).1
    have hTrack : TracksMma X (g, visit k) (g, c) :=
      ⟨rfl, by omega, .inl ⟨_, _, _, _, (hVisit k).2.2⟩, sp, tag, hc⟩
    exact observed_operands_of_done hX ((hX.tcCommit _ _ hn).2 _ hTrack)
  let ops : Fin 16 → MmaOperands := fun k => (hObs k).choose
  let inputs : BlockQkInputs P L X g d.i (Wg2.gatheredByte P L g d.i) :=
    { event := fun k => (g, visit k)
      operands := ops
      issue := fun k => (hVisit k).2.2
      observed := fun k => (hObs k).choose_spec
      query := fun k h col => qk_query_operand (d := ⟨.qkMma k, d.i⟩)
        hpre hX hs (hVisit k).2.2 (hVisit k).2.1 rfl (hObs k).choose_spec h col
      key := fun k col => qk_key_operand (d := ⟨.qkMma k, d.i⟩)
        hpre hX hs (hVisit k).2.1 rfl (hVisit k).2.2 (hObs k).choose_spec col
      previous := hPrevious }
  obtain ⟨hLo, hHi⟩ := qk_block_halves hX.tma.2.1 inputs head slot
  exact ⟨visit 15, _, _, (hVisit 15).1, hLo, hHi, blockHalfDot_sum P L g head slot _, rfl, rfl⟩

/-- The two result cells of the last QK issue observed by a mask read add to the row dot product. -/
theorem qk_pair_for_mask {cta issuer j src : Nat} {lane : Fin 128} {out : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) j =
      some (some (.wg0 out))) (hsite : out.site = .maskRead)
    (hlen : j ≤ (X.tr (GemmRing.softmax L cta lane)).length)
    (hSrc : Frame.stateAt (Machine.code P L) X issuer src =
      some (some (.mma ⟨.qkMma 15, out.block⟩)))
    (hIssue : X.MmaIssue (issuer, src) Wg1Mma.tmemP (qkOperands L issuer out.block 15)
      (qkAccum 15) [0, 0, 0, 0]) (head slot : Fin 64) :
    ∃ lo hi,
      TcMma.Result L Assumptions.all X (issuer, src)
        ⟨cta, head.val, Wg1Mma.tmemP + slot.val⟩ (.float .f32 lo) ∧
      TcMma.Result L Assumptions.all X (issuer, src)
        ⟨cta, head.val + 64, Wg1Mma.tmemP + slot.val⟩ (.float .f32 hi) ∧
      lo + hi = blockDot P L issuer head.val slot.val (Wg2.gatheredByte P L issuer out.block) ∧
      lo = blockHalfDot P L issuer head slot 0 (Wg2.gatheredByte P L issuer out.block) ∧
      hi = blockHalfDot P L issuer head slot 1 (Wg2.gatheredByte P L issuer out.block) := by
  let g := GemmRing.softmax L cta lane
  have hCta : ctaOf L g = cta := by
    have hl := lane.isLt
    simp only [g, GemmRing.softmax, ctaOf, hpre.block]
    omega
  obtain ⟨w, q, _, _, tag, _, scope, _, hq, hQk, hBlock, hw, _, _, _, _, _, _, _⟩ :=
    Wg0ScoreEventHistory.waits_of_mask hpre hX hs hd hsite hlen
  have hWait : X.get (g, w) = some ⟨tag, .wait (GemmRing.qk L cta (rawSlot q.block))
      (out.block / 2 % 2) true true scope⟩ := by
    rw [hBlock]
    rw [hCta] at hw
    exact hw
  obtain ⟨c, ctag, spec, rank, d, hc, _, hD, hIssuer, hCommit, hCommitBlock, hObs⟩ :=
    ScoreReadback.commit_of_qk_wait hpre hX hs hmma hq hQk hWait
  obtain ⟨hNov, _⟩ := hObs.waitObserves_tcNotify hWait
  obtain ⟨last, hLast, hLastState, hLastIssue⟩ :=
    QkIssueHistory.qk_issue_of_commit hpre hX hs hc hD hCommit 15
  have hb : d.i = out.block := hCommitBlock.trans hBlock
  have hLe : src ≤ last :=
    QkWriteOrder.no_later_same_block_writer hLastIssue.choose_spec hLastState hSrc
      rfl rfl hb.ge (PTX.len_of_get hIssue.choose_spec).le
  have hGe : last ≤ src :=
    QkWriteOrder.no_later_same_block_writer hIssue.choose_spec hSrc hLastState
      rfl rfl hb.le (PTX.len_of_get hLastIssue.choose_spec).le
  have hEq : src = last := Nat.le_antisymm hLe hGe
  obtain ⟨i, lo, hi, hIndex, hLo, hHi, hSum, hLower, hHigher⟩ :=
    qk_block_of_commit hpre hX hs hc hD hCommit hNov head slot
  have hIndexEq : i = last := by
    change last + 1 = c at hLast
    omega
  rw [hEq]
  rw [hIndexEq, hIssuer] at hLo hHi
  rw [hb] at hSum hLower hHigher
  exact ⟨lo, hi, hLo, hHi, hSum, hLower, hHigher⟩

/-- The score-value provider at a mask read follows from its actual completed QK block. -/
theorem qk_values_of_mask {cta issuer j : Nat} {lane : Fin 128} {out : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) j =
      some (some (.wg0 out))) (hsite : out.site = .maskRead)
    (hlen : j ≤ (X.tr (GemmRing.softmax L cta lane)).length) :
    ScoreMaskStep.QkScoreValues P L X cta issuer out.block lane := by
  let g := GemmRing.softmax L cta lane
  have hCta : ctaOf L g = cta := by
    have hl := lane.isLt
    simp only [g, GemmRing.softmax, ctaOf, hpre.block]
    omega
  have hTid : tidOf L g = lane.val := by
    have hl := lane.isLt
    simp only [g, GemmRing.softmax, tidOf_eq hpre, hpre.block]
    omega
  intro part reg src hSrc hIssue
  let head : Fin 64 := ⟨lane.val % 64, by omega⟩
  let slot : Fin 64 := ⟨32 * part.val + reg.val, by
    have := part.isLt
    have := reg.isLt
    omega⟩
  obtain ⟨lo, hi, hLo, hHi, _⟩ :=
    qk_pair_for_mask hpre hX hs hmma hd hsite hlen hSrc hIssue head slot
  rw [scoreLoad_cell hpre (g := g) (by rw [hTid]; exact lane.isLt), hTid]
  change ∃ value, TcMma.Result L Assumptions.all X (issuer, src)
    ⟨ctaOf L g, lane.val, Wg1Mma.tmemP + slot.val⟩ value
  rw [hCta]
  by_cases hLane : lane.val < 64
  · have hHead : head.val = lane.val := Nat.mod_eq_of_lt hLane
    rw [hHead] at hLo
    exact ⟨_, hLo⟩
  · have hHead : head.val + 64 = lane.val := by
      have := lane.isLt
      dsimp [head]
      omega
    rw [hHead] at hHi
    exact ⟨_, hHi⟩

/-- All followed softmax lanes obtain their score values from actual QK products. -/
theorem qk_values (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    Wg0PeerQkValues.QkValues P L X :=
  fun _ _ _ _ _ hmma hd hsite hlen => qk_values_of_mask hpre hX hs hmma hd hsite hlen.le

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

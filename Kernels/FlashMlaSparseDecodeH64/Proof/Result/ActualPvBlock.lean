-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualQkBlock
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPvProbability
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvAccumulatorSource

@[expose] public section

/-! # The inputs of a completed actual PV block -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy Protocol MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The row recurrence at actual votes supplies the updated reference and both masked scores
of every packed pair. The raw cache data already comes from the launch's gathered rows. -/
def PvVoteValues (P : Params) (L : Launch) (X : Execution) (g block : Nat)
    (valid : Nat → Bool) (ref : Nat → ℝ) : Prop :=
  ∀ {lane j : Nat} {v mid : Wg0.D} {e : Event} {take : Bool},
    ctaOf L lane = ctaOf L g →
    X.get (lane, j) = some e →
    (∃ mode mask arg, e.kind = .voteMode mode mask arg take) →
    Frame.stateAt (Machine.code P L) X lane j = some (some (.wg0 v)) →
    v.site = .rescaleVote → v.block = block →
    Wg0.afterReferenceVote v take = some mid →
    let head := tidOf L lane % 64
    let base := 32 * Wg0.half L lane
    let score := fun slot => blockScore P L g head slot (Wg2.gatheredByte P L g block) valid
    Wg0.reference mid = ref head ∧
      ∀ p : Fin 16, v.scoreSums p.val =
        .pair (Wg0.peakVal (score (base + 2 * p.val)))
          (Wg0.peakVal (score (base + 2 * p.val + 1)))

/-- An actual PV A row is the packed probability of its selected sparse slots. -/
theorem pv_probability_operand {g i block : Nat} {k : Fin 8} {ops : MmaOperands}
    {valid : Nat → Bool} {ref : Nat → ℝ}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hi : PvAccumulatorSource.Issue L X g i block k)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩)))
    (hOps : X.async.mmaOperands (g, i) = some ops)
    (hv : PvVoteValues P L X g block valid ref)
    (head : Fin 64) (col : Fin 256) :
    Bf16Operand ops.a (head.val + 64 * (col.val / 128)) fun m =>
      blockProbability P L g head.val (ref head.val) (Wg2.gatheredByte P L g block) valid
        (16 * (k.val / 2) + m) := by
  let row : Fin 128 := ⟨head.val + 64 * (col.val / 128), by omega⟩
  have hRow : row.val % 64 = head.val := by dsimp [row]; omega
  apply actual_pv_probability_of_vote (d := ⟨.pvMma k, block⟩) hpre hX hs ht
    hi hd rfl hOps row
    (fun slot => blockScore P L g head.val slot (Wg2.gatheredByte P L g block) valid) (ref head.val)
  intro m j v mid e take
  dsimp only
  intro he hVote hState hSite hBlock hRef
  let slot : Fin 64 := ⟨pvSlot k m, by unfold pvSlot; omega⟩
  obtain ⟨hCta, hHead, _⟩ := probabilityLane_coords hpre (ctaOf L g) row slot
  have h := hv hCta he hVote hState hSite hBlock hRef
  change tidOf L (probabilityLane L (ctaOf L g) row slot) % 64 = row.val % 64 at hHead
  rw [hRow] at hHead
  simpa only [hHead] using h

variable {g c tag observe : Nat} {d : Wg1Mma.D} {sp observed : TcCommit.Spec} {rank : Fin 16}
    {valid : Nat → Bool} {ref : Nat → ℝ} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hc : X.get (g, c) = some ⟨tag, .tc (.commit sp)⟩)
    (hd : Frame.stateAt (Machine.code P L) X g c = some (some (.mma d)))
    (hsite : d.site = .pvCommit) (hObserve : X.Commit (g, observe) observed) (hLater : c ≤ observe)
    (hn : rank ∈ X.tcNotified (g, observe)) (hv : PvVoteValues P L X g d.i valid ref)
include hpre hX hs ht hc hd hsite hObserve hLater hn hv

/-- The block's issued PV commit determines its eight issues. An observed commit of the same
issuer at or after it supplies completion for all eight. -/
theorem pv_inputs_of_observed_block :
    ∃ (visit : Fin 8 → Nat)
      (inputs : BlockPvInputs P L X g d.i (Wg2.gatheredByte P L g d.i) valid ref),
      (∀ k, visit k + (8 - k.val) = c) ∧ inputs.event = fun k => (g, visit k) := by
  classical
  obtain ⟨visit, hVisit, hPrevious⟩ := PvAccumulatorSource.of_commit hpre hX hs ht hc hd hsite
  have hObs (k : Fin 8) : ∃ ops, X.async.mmaOperands (g, visit k) = some ops := by
    have hk := k.isLt
    have hLess := (hVisit k).1
    have hTrack : TracksMma X (g, visit k) (g, observe) :=
      ⟨rfl, by omega, .inl ⟨_, _, _, _, (hVisit k).2.2⟩, observed, hObserve⟩
    exact observed_operands_of_done hX ((hX.tcCommit _ _ hn).2 _ hTrack)
  let ops : Fin 8 → MmaOperands := fun k => (hObs k).choose
  let inputs : BlockPvInputs P L X g d.i (Wg2.gatheredByte P L g d.i) valid ref :=
    { event := fun k => (g, visit k)
      operands := ops
      issue := fun k => (hVisit k).2.2
      observed := fun k => (hObs k).choose_spec
      probability := fun k => pv_probability_operand hpre hX hs ht
        (hVisit k).2.2 (hVisit k).2.1 (hObs k).choose_spec hv
      value := fun k col => pv_value_operand (d := ⟨.pvMma k, d.i⟩)
        hpre hX hs (hVisit k).2.1 rfl (hVisit k).2.2 (hObs k).choose_spec col
      previous := hPrevious }
  exact ⟨visit, inputs, fun k => (hVisit k).1, rfl⟩

/-- An observed PV cell contains its rescaled seed and the 64 weighted values of its sparse
block. The block's own issued commit fixes the source event even if a later commit is observed. -/
theorem pv_result_of_observed_block (head : Fin 64) (half : Fin 2) (col : Fin 256) (prior gain : ℝ)
    (hseed : ∀ i, i + (8 - (pvHalfIssue half 0).val) = c →
      GemmAccumulator L X (g, i)
        ⟨ctaOf L g, head.val + 64 * (col.val / 128), Wg1Mma.tmemO + 128 * half.val + col.val % 128⟩
        (pvAccum d.i (pvHalfIssue half 0)) (prior * gain)) :
    let raw := Wg2.gatheredByte P L g d.i
    ∃ i, i + (8 - (pvHalfIssue half 3).val) = c ∧
      TcMma.Result L Assumptions.all X (g, i)
        ⟨ctaOf L g, head.val + 64 * (col.val / 128), Wg1Mma.tmemO + 128 * half.val + col.val % 128⟩
        (.float .f32 (prior * gain + ∑ s ∈ Finset.range 64,
          blockProbability P L g head.val (ref head.val) raw valid s *
            dequant (raw s) (256 * half.val + col.val))) := by
  obtain ⟨visit, inputs, hdist, hEvents⟩ :=
    pv_inputs_of_observed_block hpre hX hs ht hc hd hsite hObserve hLater hn hv
  have hSeed := hseed (visit (pvHalfIssue half 0)) (hdist _)
  have h := pv_block_update hX.tma.2.1 inputs head half col prior gain
    (by rw [hEvents]; exact hSeed)
  rw [hEvents] at h
  exact ⟨visit (pvHalfIssue half 3), hdist _, h⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

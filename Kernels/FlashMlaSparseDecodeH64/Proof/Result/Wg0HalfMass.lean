-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MassHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualScoreSums
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingObjects
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmBlockMass
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.SparseBlockTerms
import Lemmas.Flow.ArithCore
import Lemmas.Flow.Ex2Core
import Lemmas.Flow.Recip
import Lemmas.Flow.Scalars
import Lemmas.Real.BlockSums
import Lemmas.Order.OrderWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The half-row softmax mass of the actual followed lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0HalfMass

open PTX PTX.Proof PTX.Flow Wg0 Wg0MassHistory Protocol MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The unnormalized weights of this half's 32 logical slots in a block. -/
def blockWeightSum (P : Params) (batch query head half block : Nat) : ℝ :=
  ∑ s ∈ Finset.range 32, Result.blockWeight P batch query head block (32 * half + s)

/-- The specification weights of the first `n` blocks of one half-row. -/
def prefixWeight (P : Params) (batch query head half n : Nat) : ℝ :=
  ∑ b ∈ Finset.range n, blockWeightSum P batch query head half b

/-- Both the numerical half sum and its initialized flag agree with the blocks already added. -/
def MassAt (P : Params) (L : Launch) (g : Nat) (d : Wg0.D) : Prop :=
  d.lh = (2 : ℝ) ^ (-reference d) * prefixWeight P (Wg1Mma.batchOf L g)
    (Wg1Mma.queryOf L g) (head L g) (half L g) (blocksAdded d) ∧
    d.sumUpd = decide (0 < blocksAdded d)

private theorem empty {g : Nat} {d : Wg0.D} (h : EmptyMass d) : MassAt P L g d := by
  obtain ⟨hn, hl, hs⟩ := h
  simp [MassAt, hn, hl, hs, prefixWeight]

private theorem retained {g : Nat} {old d : Wg0.D} (hOld : MassAt P L g old)
    (h : Retained old d) : MassAt P L g d := by
  obtain ⟨hn, hl, hs, hr⟩ := h
  simpa only [MassAt, hn, hl, hs, hr] using hOld

private theorem vote_fields {d mid : Wg0.D} {take : Bool}
    (hv : afterReferenceVote d take = some mid) :
    mid.lh = d.lh ∧ mid.sumUpd = d.sumUpd ∧ mid.scoreSums = d.scoreSums ∧
      valFloat .f32 mid.gainWord = .ok ((2 : ℝ) ^ (reference d - reference mid)) := by
  cases take
  · change some { d with gainWord := b32 1065353216 } = some mid at hv
    cases hv
    refine ⟨rfl, rfl, rfl, ?_⟩
    change valFloat .f32 (b32 1065353216) = .ok ((2 : ℝ) ^ (reference d - reference d))
    rw [sub_self, Real.rpow_zero]
    exact valFloat_one
  · simp only [afterReferenceVote, ↓reduceIte] at hv
    obtain ⟨ref, _, h⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨mi, hmi, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hre
      obtain ⟨delta, hdelta, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨gain, hgain, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hsub : subE true (miVal d) ref = .ok (fl (reference d - mi)) := by
        rw [hre]
        exact subE_fin (valFloat_miVal d) (valFloat_fl mi)
      rw [hsub] at hdelta
      have hDelta : fl (reference d - mi) = delta := Option.some.inj hdelta
      have hpow : ex2E true delta = .ok (fl ((2 : ℝ) ^ (reference d - mi))) := by
        rw [← hDelta]
        exact ex2E_fin (valFloat_fl _)
      rw [hpow] at hgain
      have hGain : fl ((2 : ℝ) ^ (reference d - mi)) = gain := Option.some.inj hgain
      refine ⟨rfl, rfl, rfl, ?_⟩
      change valFloat .f32 gain = .ok ((2 : ℝ) ^ (reference d - mi))
      rw [← hGain]
      exact valFloat_fl _
    · cases h

private theorem update_reference {g : Nat} {d out : Wg0.D}
    (hp : probabilityUpdate L g d = some out) : reference out = reference d := by
  unfold probabilityUpdate at hp
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  rfl

private theorem probabilities_spec {g block : Nat} (ref : ℝ) :
    (∑ s ∈ Finset.range 32, blockProbability P L g (head L g) ref
      (Wg2.gatheredByte P L g block) (gatheredValid P L g block) (32 * half L g + s)) =
      (2 : ℝ) ^ (-ref) * blockWeightSum P (Wg1Mma.batchOf L g)
        (Wg1Mma.queryOf L g) (head L g) (half L g) block := by
  rw [blockWeightSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => gathered_probability_spec P L g _ block _ ref

private theorem added_with_scores {g : Nat} {old d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (ha : Added L g old d e)
    (hScores : ∀ k : Fin 16, old.scoreSums k.val =
      .pair (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * k.val)
        (Wg2.gatheredByte P L g old.block) (gatheredValid P L g old.block)))
      (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * k.val + 1)
        (Wg2.gatheredByte P L g old.block) (gatheredValid P L g old.block)))) :
    d.sumUpd = true ∧ d.lh =
      (if old.sumUpd then old.lh else 0) * ((2 : ℝ) ^ (reference old - reference d)) +
        (2 : ℝ) ^ (-reference d) * blockWeightSum P (Wg1Mma.batchOf L g)
          (Wg1Mma.queryOf L g) (head L g) (half L g) old.block := by
  obtain ⟨_, _, mode, mask, arg, take, mid, out, _, hv, hp, hLh, hSum, hRef⟩ := ha
  obtain ⟨hOldMass, hOldSum, hOldScores, hGain⟩ := vote_fields hv
  let v : Wg0.D := { mid with voteTaken := take }
  have hValues (k : Fin 16) : v.scoreSums k.val = old.scoreSums k.val := by
    change mid.scoreSums k.val = _
    rw [hOldScores]
  have hGain' : valFloat .f32 v.gainWord = .ok ((2 : ℝ) ^ (reference old - reference v)) := hGain
  obtain ⟨actual, hActual, hActualSum, hMass, _⟩ := block_probability_update hpre v
    (Wg2.gatheredByte P L g old.block) (gatheredValid P L g old.block)
    _ (fun k => (hValues k).trans (hScores k)) hGain'
  change probabilityUpdate L g v = some out at hp
  obtain rfl := Option.some.inj (hActual.symm.trans hp)
  have hReference : reference d = reference v := hRef.trans (update_reference hp)
  have hOldMass' : v.lh = old.lh := hOldMass
  have hOldSum' : v.sumUpd = old.sumUpd := hOldSum
  rw [probabilities_spec, hOldMass', hOldSum', ← hReference] at hMass
  exact ⟨hSum.trans hActualSum, hLh.trans hMass⟩

/-- A successful actual vote rescales the older half-row mass and adds this block's true
32 masked probabilities. -/
theorem actual_added {g i issuer : Nat} {old d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hIssuer : ctaOf L issuer = ctaOf L g)
    (he : X.get (g, i) = some e)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 old)))
    (ha : Added L g old d e) :
    d.sumUpd = true ∧ d.lh =
      (if old.sumUpd then old.lh else 0) * ((2 : ℝ) ^ (reference old - reference d)) +
        (2 : ℝ) ^ (-reference d) * blockWeightSum P (Wg1Mma.batchOf L g)
          (Wg1Mma.queryOf L g) (head L g) (half L g) old.block := by
  apply added_with_scores hpre ha
  intro k
  have hraw : Wg2.gatheredByte P L issuer old.block = Wg2.gatheredByte P L g old.block := by
    funext pos off
    exact Wg2.gatheredByte_same_cta hIssuer
  have hScore := actual_vote_scores_from_indices hpre hX hs ht hmma hIssuer
    (Frame.lt_of_get hX he) (PTX.len_of_get he).le hstate ha.1 k
  simpa only [hraw] using hScore

private theorem add_mass {g : Nat} {old d : Wg0.D} {e : Event}
    (hOld : MassAt P L g old) (ha : Added L g old d e)
    (hAdded : d.sumUpd = true ∧ d.lh =
      (if old.sumUpd then old.lh else 0) * ((2 : ℝ) ^ (reference old - reference d)) +
        (2 : ℝ) ^ (-reference d) * blockWeightSum P (Wg1Mma.batchOf L g)
          (Wg1Mma.queryOf L g) (head L g) (half L g) old.block) : MassAt P L g d := by
  obtain ⟨hFlag, hMass⟩ := hAdded
  have hCountOld := blocksAdded_vote ha.1
  have hCountNew := ha.2.1
  obtain ⟨hOldMass, hOldFlag⟩ := hOld
  have hEffective : (if old.sumUpd then old.lh else 0) = old.lh := by
    rw [hOldFlag]
    by_cases h : 0 < blocksAdded old
    · simp [h]
    · have hz : blocksAdded old = 0 := by omega
      simp [hz, prefixWeight] at hOldMass ⊢
      exact hOldMass.symm
  refine ⟨?_, by simp [hFlag, hCountNew]⟩
  rw [hMass, hEffective, hOldMass, hCountOld, hCountNew]
  simp only [prefixWeight, Finset.sum_range_succ]
  have hScale : (2 : ℝ) ^ (-reference old) * (2 : ℝ) ^ (reference old - reference d) =
      (2 : ℝ) ^ (-reference d) := by
    rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    congr 1
    ring
  simp only [← hScale]
  ring

/-- Every reached WG0 state records the contributions of its actual updated blocks. -/
theorem mass_at_state {g i issuer : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hIssuer : ctaOf L issuer = ctaOf L g)
    (hi : i ≤ (X.tr g).length)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) : MassAt P L g d := by
  induction i generalizing d with
  | zero => rw [Frame.stateAt_zero] at hstate; cases hstate
  | succ i ih =>
    have hi' : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨q, hq⟩ := Frame.stateAt_live ht hg hstate (Nat.le_succ i)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hstate, hq] at hn
    obtain hz | ⟨old, rfl, hret | hadd⟩ := composed_step hn.symm
    · exact empty hz
    · exact retained (ih hi'.le hq) hret
    · exact add_mass (ih hi'.le hq) hadd (actual_added hpre hX hs ht hmma hIssuer he hq hadd)

/-- A followed lane's half mass is determined by the causally prior votes and their scores. -/
theorem causal_mass_at_state {g i issuer cut : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hg : g < L.threads)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hIssuer : ctaOf L issuer = ctaOf L g)
    (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t)
    (hi : i ≤ cut)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) : MassAt P L g d := by
  induction i generalizing d with
  | zero => rw [Frame.stateAt_zero] at hstate; cases hstate
  | succ i ih =>
    have hi' : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨q, hq⟩ := FollowedPrefix.state_at hstate (Nat.le_succ i)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hstate, hq] at hn
    obtain hz | ⟨old, rfl, hret | hadd⟩ := composed_step hn.symm
    · exact empty hz
    · exact retained (ih (by omega) hq) hret
    · refine add_mass (ih (by omega) hq) hadd (added_with_scores hpre hadd ?_)
      intro k
      have hraw : Wg2.gatheredByte P L issuer old.block = Wg2.gatheredByte P L g old.block := by
        funext pos off
        exact Wg2.gatheredByte_same_cta hIssuer
      have hScore := causal_vote_scores_from_indices hpre hX hs hmma hIssuer hg
        (show i ≤ cut by omega) hLen hPrior hq hadd.1 k
      simpa only [hraw] using hScore

/-- The finished half-row retains all blocks, at the reference used by the epilogue. -/
theorem mass_in_epilogue {g : Nat} {d : Wg0.D}
    (h : MassAt P L g d) (hi : Wg0.Inv P L g d) (he : d.site.inEpilogue = true) :
    d.lh = (2 : ℝ) ^ (-reference d) * prefixWeight P (Wg1Mma.batchOf L g)
      (Wg1Mma.queryOf L g) (head L g) (half L g) (blocksOf P L g) ∧ d.sumUpd = true := by
  have hcount : blocksAdded d = blocksOf P L g :=
    (blocksAdded_epilogue he).trans (hi.epilogueLast he)
  obtain ⟨hm, hs⟩ := h
  rw [hcount] at hm hs
  exact ⟨hm, hs.trans (decide_eq_true (blocksOf_pos P L g))⟩

/-- Each half-row prefix is a sum of nonnegative specification weights. -/
theorem prefixWeight_nonneg (P : Params) (batch query head half n : Nat) :
    0 ≤ prefixWeight P batch query head half n := by
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro s _
  exact Result.weight_nonneg P batch query head _ _

/-- The two disjoint 32-slot halves fill the 64 logical slots of every block. -/
theorem halves_eq_rowSum (P : Params) (batch query head : Nat)
    (htopk : P.topkLen batch ≤ P.topk) (hextra : P.extraTopkLen batch ≤ P.extra_topk) :
    prefixWeight P batch query head 0 (Result.blocks P batch) +
      prefixWeight P batch query head 1 (Result.blocks P batch) = rowSum P batch query head := by
  rw [← Result.sum_blockWeight_eq_rowSum P batch query head htopk hextra]
  unfold prefixWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [show Result.topkBlock = 32 + 32 from rfl, Finset.sum_range_add]
  simp [blockWeightSum, Nat.add_comm]

/-- An empty row contributes zero to each of its two halves. -/
theorem half_zero_of_rowSum_zero (P : Params) (batch query head half : Nat) (hh : half < 2)
    (htopk : P.topkLen batch ≤ P.topk) (hextra : P.extraTopkLen batch ≤ P.extra_topk)
    (hz : rowSum P batch query head = 0) :
    prefixWeight P batch query head half (Result.blocks P batch) = 0 := by
  have hp := halves_eq_rowSum P batch query head htopk hextra
  have h0 := prefixWeight_nonneg P batch query head 0 (Result.blocks P batch)
  have h1 := prefixWeight_nonneg P batch query head 1 (Result.blocks P batch)
  rw [hz] at hp
  interval_cases half <;> linarith

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0HalfMass

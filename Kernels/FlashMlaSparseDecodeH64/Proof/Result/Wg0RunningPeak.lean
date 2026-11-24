-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0HalfMass
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeakHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerContinuation
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ReferencePrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedBlockMax
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0LseReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.CanonicalPvReference
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.SparseBlockTerms
import Lemmas.Real.BlockSums
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The empty-row selection in the actual softmax epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0RunningPeak

open PTX PTX.Proof PTX.Flow Wg0 Wg0PeakHistory Protocol MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem valid_same_cta {g w : Nat} (hc : ctaOf L w = ctaOf L g)
    (b s : Nat) : gatheredValid P L w b s = gatheredValid P L g b s := by
  simp only [gatheredValid_spec, Wg1Mma.batchOf_eq_ctaidY, Wg1Mma.queryOf_eq_ctaidX,
    ctaidY, ctaidX, hc]
  rfl

private theorem score_bot {valid : Nat → Bool} {raw : Nat → Nat → Nat} {g h s : Nat} :
    blockScore P L g h s raw valid = ⊥ ↔ valid s = false := by
  cases hv : valid s <;> simp [blockScore, hv]

private def LocalPeakMatchesValidity (P : Params) (L : Launch) (g : Nat)
    (d : Wg0.D) : Prop :=
  ∃ m : WithBot ℝ, rowLocalMax L d = peakVal m ∧
    (m = ⊥ ↔ ∀ k < 32, gatheredValid P L g d.block (32 * half L g + k) = false)

/-- A half publishes an empty maximum exactly when all its actual validity bits are clear. -/
private theorem local_peak_with_scores {g issuer : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0)
    (hScores : ∀ k : Fin 16, d.scoreSums k.val =
      .pair (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * k.val)
        (Wg2.gatheredByte P L issuer d.block) (gatheredValid P L g d.block)))
      (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * k.val + 1)
        (Wg2.gatheredByte P L issuer d.block) (gatheredValid P L g d.block)))) :
    LocalPeakMatchesValidity P L g d := by
  obtain ⟨m, hm, hMasked⟩ := rowLocalMax_bot_iff hpre (fun k hk => by
    rw [hScores ⟨k, hk⟩]
    exact ⟨_, _, rfl⟩)
  refine ⟨m, hm, hMasked.trans ?_⟩
  have hPair (k : Fin 16) :
      d.scoreSums k.val = .pair negInf negInf ↔
        gatheredValid P L g d.block (32 * half L g + 2 * k.val) = false ∧
        gatheredValid P L g d.block (32 * half L g + 2 * k.val + 1) = false := by
    rw [hScores k, Value.pair.injEq, peakVal_eq_negInf, peakVal_eq_negInf, score_bot, score_bot]
  constructor
  · intro h k hk
    let j : Fin 16 := ⟨k / 2, by omega⟩
    obtain ⟨h0, h1⟩ := (hPair j).mp (h j.val j.isLt)
    dsimp [j] at h0 h1
    by_cases he : k % 2 = 0
    · rwa [show 2 * (k / 2) = k by omega] at h0
    · rwa [show 32 * half L g + 2 * (k / 2) + 1 = 32 * half L g + k by omega] at h1
  · intro h k hk
    exact (hPair ⟨k, hk⟩).mpr ⟨h _ (by omega),
      by simpa only [Nat.add_assoc] using h (2 * k + 1) (by omega)⟩

section
variable {g i issuer : Nat} {d : Wg0.D}

/-- The maximum actually published by one half is masked precisely when that half has no slot. -/
private theorem local_peak (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hIssuer : ctaOf L issuer = ctaOf L g)
    (hg : g < L.threads) (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .rowMax)
    :
    LocalPeakMatchesValidity P L g d :=
  local_peak_with_scores (issuer := issuer) hpre
    (fun k => actual_rowMax_scores_from_indices hpre hX hs ht hmma hIssuer hg hi hd hsite k)

private theorem block_peak_from_halves {g : Nat} {own peer : Wg0.D} {m : Value}
    (hpre : Pre P L mem0) (hwarp : warpOf L g < 4)
    (hA : LocalPeakMatchesValidity P L g own)
    (hB : LocalPeakMatchesValidity P L (Wg0PeerSources.partner L g) peer)
    (hBlock : peer.block = own.block)
    (hMax : peerMaxE (rowLocalMax L own) (rowLocalMax L peer) = .ok m) :
    ∃ peak : WithBot ℝ, m = peakVal peak ∧
      (peak = ⊥ ↔ ∀ k < 64, gatheredValid P L g own.block k = false) := by
  let mate := Wg0PeerSources.partner L g
  obtain ⟨hCta, _, hOther, _⟩ := partner_coordinates hpre hwarp
  obtain ⟨a, ha, haBot⟩ := hA
  obtain ⟨b, hb, hbBot⟩ := hB
  rw [ha, hb, peerMaxE_peak] at hMax
  refine ⟨max a b, (Except.ok.inj hMax).symm, ?_⟩
  rw [max_eq_bot, haBot, hbBot, hBlock, hOther]
  have hv : gatheredValid P L mate = gatheredValid P L g :=
    funext fun b => funext fun k => valid_same_cta hCta b k
  change (∀ k < 32, gatheredValid P L g own.block (32 * half L g + k) = false) ∧
    (∀ k < 32, gatheredValid P L mate own.block (32 * (1 - half L g) + k) = false) ↔ _
  rw [hv]
  have hHalf := Wg0.halfLt hwarp
  constructor
  · intro ⟨hA, hB⟩ k hk
    by_cases h : k / 32 = half L g
    · have he := hA (k % 32) (Nat.mod_lt _ (by decide))
      rwa [show 32 * half L g + k % 32 = k by omega] at he
    · have he := hB (k % 32) (Nat.mod_lt _ (by decide))
      have hop : k / 32 = 1 - half L g := by omega
      rwa [show 32 * (1 - half L g) + k % 32 = k by omega] at he
  · intro h
    exact ⟨fun k hk => h _ (by omega), fun k hk => h _ (by omega)⟩

private theorem block_peak_of_visits {g i j issuer : Nat} {own peer : Wg0.D} {m : Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hIssuer : ctaOf L issuer = ctaOf L g) (hg : g < L.threads)
    (hw : Wg0PeerSources.partner L g < L.threads) (hwarp : warpOf L g < 4)
    (hi : i ≤ (X.tr g).length) (hj : j ≤ (X.tr (Wg0PeerSources.partner L g)).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 own)))
    (hq : Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j =
      some (some (.wg0 peer)))
    (hD : own.site = .rowMax) (hQ : peer.site = .rowMax)
    (hBlock : peer.block = own.block)
    (hMax : peerMaxE (rowLocalMax L own) (rowLocalMax L peer) = .ok m) :
    ∃ peak : WithBot ℝ, m = peakVal peak ∧
      (peak = ⊥ ↔ ∀ k < 64, gatheredValid P L g own.block k = false) := by
  let mate := Wg0PeerSources.partner L g
  obtain ⟨hCta, _, hOther, _⟩ := partner_coordinates hpre hwarp
  have hmma' : GemmRing.MmaIssuer P L X (ctaOf L mate) issuer := by rw [hCta]; exact hmma
  exact block_peak_from_halves hpre hwarp (local_peak hpre hX hs ht hmma hIssuer hg hi hd hD)
    (local_peak hpre hX hs ht hmma' (hIssuer.trans hCta.symm) hw hj hq hQ) hBlock hMax

private theorem block_peak_at_vote (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hIssuer : ctaOf L issuer = ctaOf L g)
    (hg : g < L.threads) (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    ∃ peak : WithBot ℝ, d.blockMax = peakVal peak ∧
      (peak = ⊥ ↔ ∀ k < 64, gatheredValid P L g d.block k = false) := by
  obtain ⟨j, k, own, peer, hOwn, hPeer, _, hMax⟩ :=
    Wg0PairedReference.visit_of_vote hpre hX hs ht hg hi hd hsite
  obtain ⟨_, hGet⟩ := hOwn.write
  obtain ⟨_, hPeerGet⟩ := hPeer.write
  have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  obtain ⟨m, hm, hBot⟩ := block_peak_of_visits hpre hX hs ht hmma hIssuer hg
    (Frame.lt_of_get hX hPeerGet.choose_spec) (Wg0.warpLt hpre hWg)
    (PTX.len_of_get hGet.choose_spec).le (PTX.len_of_get hPeerGet.choose_spec).le
    hOwn.state hPeer.state hOwn.site hPeer.site (hPeer.blockEq.trans hOwn.blockEq.symm) hMax
  exact ⟨m, hm, by rw [← hOwn.blockEq]; exact hBot⟩

private theorem causal_block_peak_at_vote {g i cut issuer : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hIssuer : ctaOf L issuer = ctaOf L g) (hg : g < L.threads)
    (hi : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) :
    ∃ peak : WithBot ℝ, d.blockMax = peakVal peak ∧
      (peak = ⊥ ↔ ∀ k < 64, gatheredValid P L g d.block k = false) := by
  obtain ⟨j, k, own, peer, hOwn, hPeer, hj, hCausal, _, hMax⟩ :=
    Wg0PairedReference.causal_visit_of_vote hpre hX hs hg hi hLen hPrior hd hsite
  let mate := Wg0PeerSources.partner L g
  obtain ⟨_, hf⟩ := hPeer.write
  have hw := Frame.lt_of_get hX hf.choose_spec
  have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  have hWarp := Wg0.warpLt hpre hWg
  obtain ⟨hCta, _, _, _⟩ := partner_coordinates hpre hWarp
  have hmma' : GemmRing.MmaIssuer P L X (ctaOf L mate) issuer := by rw [hCta]; exact hmma
  have hA : LocalPeakMatchesValidity P L g own :=
    local_peak_with_scores (issuer := issuer) hpre (fun t =>
      causal_rowMax_scores_from_indices hpre hX hs hmma hIssuer hg hj hLen hPrior
        hOwn.state hOwn.site t)
  have hB : LocalPeakMatchesValidity P L mate peer :=
    local_peak_with_scores (issuer := issuer) hpre (fun t =>
      causal_rowMax_scores_from_indices hpre hX hs hmma' (hIssuer.trans hCta.symm)
        hw le_rfl (PTX.len_of_get hf.choose_spec) (fun v h => hPrior v (h.trans hCausal))
        hPeer.state hPeer.site t)
  obtain ⟨m, hm, hBot⟩ :=
    block_peak_from_halves hpre hWarp hA hB (hPeer.blockEq.trans hOwn.blockEq.symm) hMax
  exact ⟨m, hm, by rw [← hOwn.blockEq]; exact hBot⟩

/-- All slots visited up to, but excluding, the numbered block were masked. -/
def PrefixEmpty (P : Params) (L : Launch) (g n : Nat) : Prop :=
  ∀ b < n, ∀ k < 64, gatheredValid P L g b k = false

private theorem prefix_succ {g n : Nat} :
    PrefixEmpty P L g (n + 1) ↔
      PrefixEmpty P L g n ∧ ∀ k < 64, gatheredValid P L g n k = false := by
  constructor
  · intro h
    exact ⟨fun b hb => h b (by omega), h n (by omega)⟩
  · intro ⟨h, hLast⟩ b hb
    obtain hb | rfl : b < n ∨ b = n := by omega
    · exact h b hb
    · exact hLast

/-- At any followed state the peak is empty exactly when its encountered blocks were empty. -/
theorem peak_at_state (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hIssuer : ctaOf L issuer = ctaOf L g) (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) :
    d.peak = ⊥ ↔ PrefixEmpty P L g (blocksSeen d) := by
  induction i generalizing d with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i ih =>
    have hi' : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨q, hq⟩ := Frame.stateAt_live ht hg hd (Nat.le_succ i)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hq] at hn
    obtain hz | ⟨old, rfl, hKeep | hExt⟩ := composed_step hn.symm
    · rw [hz.1, hz.2]
      exact ⟨fun _ _ hb => (Nat.not_lt_zero _ hb).elim, fun _ => rfl⟩
    · rw [hKeep.1, hKeep.2]
      exact ih hi'.le hq
    · obtain ⟨hOld, hNew, hBlock, hSeen, peer, out, hRun, hPeak, hMax⟩ := hExt
      obtain ⟨b, hb, hbBot⟩ := block_peak_at_vote hpre hX hs ht hmma hIssuer hg hi hd hNew
      have hOut : out.blockMax = peakVal b := hMax.symm.trans hb
      rw [hPeak, extension_peak hRun hOut, max_eq_bot, ih hi'.le hq, hbBot,
        hSeen, prefix_succ, blocksSeen_max_read hOld, hBlock]

/-- The running peak is empty exactly for an empty visited prefix of a causal execution. -/
theorem causal_peak_at_state {g i issuer cut : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hg : g < L.threads)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hIssuer : ctaOf L issuer = ctaOf L g) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t)
    (hi : i ≤ cut)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) :
    d.peak = ⊥ ↔ PrefixEmpty P L g (blocksSeen d) := by
  induction i generalizing d with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i ih =>
    have hi' : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd (Nat.le_succ i)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hq] at hn
    obtain hz | ⟨old, rfl, hKeep | hExt⟩ := composed_step hn.symm
    · rw [hz.1, hz.2]
      exact ⟨fun _ _ hb => (Nat.not_lt_zero _ hb).elim, fun _ => rfl⟩
    · rw [hKeep.1, hKeep.2]
      exact ih (by omega) hq
    · obtain ⟨hOld, hNew, hBlock, hSeen, peer, out, hRun, hPeak, hMax⟩ := hExt
      obtain ⟨b, hb, hbBot⟩ :=
        causal_block_peak_at_vote hpre hX hs hmma hIssuer hg hi hLen hPrior hd hNew
      have hOut : out.blockMax = peakVal b := hMax.symm.trans hb
      rw [hPeak, extension_peak hRun hOut, max_eq_bot, ih (by omega) hq, hbBot,
        hSeen, prefix_succ, blocksSeen_max_read hOld, hBlock]

private theorem row_sum_zero_iff {g : Nat}
    (hb : P.topkLen (Wg1Mma.batchOf L g) ≤ P.topk)
    (hx : P.extraTopkLen (Wg1Mma.batchOf L g) ≤ P.extra_topk) :
    rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0 ↔
      PrefixEmpty P L g (blocksOf P L g) := by
  rw [← sum_blockWeight_eq_rowSum P _ _ _ hb hx]
  simp only [PrefixEmpty, Wg0.blocksOf, blockWeight]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun b _ => Finset.sum_nonneg
    (fun k _ => weight_nonneg P _ _ _ _ _))]
  simp only [Finset.mem_range]
  apply forall_congr'
  intro b
  apply imp_congr_right
  intro _
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => weight_nonneg P _ _ _ _ _)]
  simp only [Finset.mem_range]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro _
  rw [gatheredValid_spec]
  change weight P _ _ _ _ _ = 0 ↔ decide (slotValid P _ _ _ _) = false
  by_cases hv : slotValid P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g)
      (blockExtra P (Wg1Mma.batchOf L g) b) (blockSlot P (Wg1Mma.batchOf L g) b k)
  · have hp : (0 : ℝ) < 2 ^ (P.scale * score P (Wg1Mma.batchOf L g)
        (Wg1Mma.queryOf L g) (head L g) (blockExtra P (Wg1Mma.batchOf L g) b)
        (blockSlot P (Wg1Mma.batchOf L g) b k)) := Real.rpow_pos_of_pos (by norm_num) _
    simp [weight, hv, hp.ne']
  · simp [weight, hv]

private theorem length_bounds (hpre : Pre P L mem0) (g : Nat) :
    P.topkLen (Wg1Mma.batchOf L g) ≤ P.topk ∧
      P.extraTopkLen (Wg1Mma.batchOf L g) ≤ P.extra_topk := by
  have he := Wg1Mma.eOf_lt_b hpre (g := g)
  exact ⟨Wg2.topkLen_le hpre he, Wg2.extraTopkLen_le hpre he⟩


private theorem epilogue_mass_from_histories {g : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0)
    (hInv : Inv P L g d) (hEpi : d.site.inEpilogue = true)
    (hp : d.peak = ⊥ ↔ PrefixEmpty P L g (blocksSeen d))
    (hm : Wg0HalfMass.MassAt P L g d) :
    lseOwnSum d = (2 : ℝ) ^ (-reference d) * Wg0HalfMass.prefixWeight P
      (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) (half L g) (blocksOf P L g) ∧
    (d.peak = ⊥ ↔ rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0) := by
  obtain ⟨hb, hx⟩ := length_bounds hpre g
  rw [blocksSeen_epilogue hEpi, hInv.epilogueLast hEpi] at hp
  have hPeak := hp.trans (row_sum_zero_iff (P := P) (L := L) (g := g) hb hx).symm
  refine ⟨?_, hPeak⟩
  obtain ⟨hMass, hSum⟩ := Wg0HalfMass.mass_in_epilogue hm hInv hEpi
  by_cases h : d.peak = ⊥
  · have hZero := Wg0HalfMass.half_zero_of_rowSum_zero P
      (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) (half L g) (halfLt hInv.warpLt)
      hb hx (hPeak.mp h)
    simp [lseOwnSum, h, Wg0.blocksOf, show Wg0.eOf L g = Wg1Mma.batchOf L g from rfl, hZero]
  · simpa [lseOwnSum, h, hSum] using hMass


/-- The conditional half-sum word in the epilogue equals the full half mass for this lane. -/
theorem epilogue_mass_and_peak (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hIssuer : ctaOf L issuer = ctaOf L g) (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hInv : Inv P L g d)
    (hEpi : d.site.inEpilogue = true) :
    lseOwnSum d = (2 : ℝ) ^ (-reference d) * Wg0HalfMass.prefixWeight P
      (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) (half L g) (blocksOf P L g) ∧
    (d.peak = ⊥ ↔ rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) = 0) :=
  epilogue_mass_from_histories hpre hInv hEpi (peak_at_state hpre hX hs ht hg hmma hIssuer hi hd)
    (Wg0HalfMass.mass_at_state hpre hX hs ht hg hmma hIssuer hi hd)
end

private theorem reference_after_final_vote {g i cta : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hc : ctaOf L g = cta)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hOrd : Wg0VoteCount.ordinal d = d.block + 1) :
    reference d = canonicalPvReference P L X cta d.block (head L g) := by
  obtain ⟨j, v, tag, take, mid, hj, hv, hState, hSite, hBlock, hUpdate, hRef, _, _⟩ :=
    Wg0ReferencePrefix.after_vote hX hs ht he hd hOrd
  exact hRef.trans (canonical_pv_vote_reference hpre hX hs ht cta d.block hc hv
    ⟨.any, 2 ^ 32 - 1, v.voteTest, rfl⟩ hState hSite hBlock hUpdate)

private theorem issuer_at_cta (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (cta : Nat) :
    ∃ issuer, ctaOf L issuer = cta ∧ GemmRing.MmaIssuer P L X cta issuer := by
  obtain ⟨lane, h⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX (fun g hg => (hs g hg).machine)
  refine ⟨cta * L.block + 128 + lane.val, ?_, h⟩
  have hLane := lane.isLt
  change (cta * L.block + 128 + lane.val) / L.block = cta
  rw [hpre.block]
  omega

section
variable {g i j : Nat} {d q : Wg0.D} {e f : Event}

/-- The two actual LSE halves give the full row sum at their common final reference. -/
theorem lse_pair_mass (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hf : X.get (Wg0PeerSources.partner L g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)))
    (hD : d.site = .lseRead) (hQ : q.site = .lseStore0) (hblock : q.block = d.block) :
    lseOwnSum d + lseOwnSum q = (2 : ℝ) ^ (-reference d) *
      rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) ∧
    RowTotal { d with li := lseOwnSum d + lseOwnSum q } := by
  let mate := Wg0PeerSources.partner L g
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  obtain ⟨_, _, _, _, hPeerInv, _, _⟩ := Frame.fired_site hs hX hf hq
  have hdInv : Inv P L g d := hInv
  have hqInv : Inv P L mate q := hPeerInv
  obtain ⟨hCta, hHead, hHalf, _⟩ := partner_coordinates hpre hdInv.warpLt
  obtain ⟨issuer, hIssuer, hmma⟩ := issuer_at_cta hpre hX hs (ctaOf L g)
  have hIssuer' : ctaOf L issuer = ctaOf L mate := hIssuer.trans hCta.symm
  have hmma' : GemmRing.MmaIssuer P L X (ctaOf L mate) issuer := by rw [hCta]; exact hmma
  obtain ⟨hm, hp⟩ := epilogue_mass_and_peak hpre hX hs ht (Frame.lt_of_get hX he) hmma
    hIssuer (PTX.len_of_get he).le hd hdInv (by rw [hD]; rfl)
  obtain ⟨hn, _⟩ := epilogue_mass_and_peak hpre hX hs ht (Frame.lt_of_get hX hf) hmma'
    hIssuer' (PTX.len_of_get hf).le hq hqInv (by rw [hQ]; rfl)
  have hr := reference_after_final_vote hpre hX hs ht rfl he hd
    (by rw [Wg0VoteCount.ordinal, hD]; rfl)
  have hr' := reference_after_final_vote hpre hX hs ht hCta hf hq
    (by rw [Wg0VoteCount.ordinal, hQ]; rfl)
  rw [hblock, hHead, ← hr] at hr'
  have hCtaMate : ctaOf L mate = ctaOf L g := hCta
  have hBatch : Wg1Mma.batchOf L mate = Wg1Mma.batchOf L g := by
    simp only [Wg1Mma.batchOf_eq_ctaidY, ctaidY, hCtaMate]
  have hQuery : Wg1Mma.queryOf L mate = Wg1Mma.queryOf L g := by
    simp only [Wg1Mma.queryOf_eq_ctaidX, ctaidX, hCtaMate]
  have hBlocks : blocksOf P L mate = blocksOf P L g := by
    change blocks P (Wg1Mma.batchOf L mate) = blocks P (Wg1Mma.batchOf L g)
    rw [hBatch]
  obtain ⟨hMain, hExtra⟩ := length_bounds hpre g
  have hParts := Wg0HalfMass.halves_eq_rowSum P _ (Wg1Mma.queryOf L g) (head L g) hMain hExtra
  have hEq : lseOwnSum d + lseOwnSum q = (2 : ℝ) ^ (-reference d) *
      rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) := by
    rw [hm, hn, hr', hBatch, hQuery, hHead, hHalf, hBlocks, ← mul_add]
    change _ * (Wg0HalfMass.prefixWeight P _ _ _ _ (blocks P (Wg1Mma.batchOf L g)) +
      Wg0HalfMass.prefixWeight P _ _ _ _ (blocks P (Wg1Mma.batchOf L g))) = _
    have hh := halfLt hdInv.warpLt
    obtain h0 | h1 : half L g = 0 ∨ half L g = 1 := by omega
    · rw [h0, show 1 - 0 = (1 : Nat) by decide, hParts]
    · rw [h1, Nat.sub_self, add_comm, hParts]
  refine ⟨hEq, ?_⟩
  have hPositive : 0 < (2 : ℝ) ^ (-reference d) := Real.rpow_pos_of_pos (by norm_num) _
  have hNonneg : 0 ≤ rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) := by
    rw [← hParts]
    exact add_nonneg (Wg0HalfMass.prefixWeight_nonneg P _ _ _ _ _)
      (Wg0HalfMass.prefixWeight_nonneg P _ _ _ _ _)
  change 0 ≤ lseOwnSum d + lseOwnSum q ∧ (lseOwnSum d + lseOwnSum q = 0 ↔ d.peak = ⊥)
  rw [hEq, mul_eq_zero, or_iff_right hPositive.ne']
  exact ⟨mul_nonneg hPositive.le hNonneg, hp.symm⟩

/-- The two half masses are nonnegative and vanish together precisely at an empty row.
The guard only needs positivity of each exponent scale. -/
theorem causal_lse_row_total (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hf : X.get (Wg0PeerSources.partner L g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)))
    (hD : d.site = .lseRead) (hQ : q.site = .lseStore0)
    (hBefore : baseCausality L X (Wg0PeerSources.partner L g, j) (g, i))
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    RowTotal { d with li := lseOwnSum d + lseOwnSum q } := by
  let mate := Wg0PeerSources.partner L g
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  obtain ⟨_, _, _, _, hPeerInv, _, _⟩ := Frame.fired_site hs hX hf hq
  have hdInv : Inv P L g d := hInv
  have hqInv : Inv P L mate q := hPeerInv
  obtain ⟨hCta, hHead, hHalf, _⟩ := partner_coordinates hpre hdInv.warpLt
  obtain ⟨issuer, hIssuer, hmma⟩ := issuer_at_cta hpre hX hs (ctaOf L g)
  have hmma' : GemmRing.MmaIssuer P L X (ctaOf L mate) issuer := by rw [hCta]; exact hmma
  have hIssuer' : ctaOf L issuer = ctaOf L mate := hIssuer.trans hCta.symm
  have hg := Frame.lt_of_get hX he
  have hw := Frame.lt_of_get hX hf
  have hi := PTX.len_of_get he
  have hj := PTX.len_of_get hf
  have hMate : ∀ t, baseCausality L X t (mate, j) → ¬ Dismisses P L X t :=
    fun t h => hPrior t (h.trans hBefore)
  obtain ⟨hdMass, hPeak⟩ := epilogue_mass_from_histories hpre hdInv (by rw [hD]; rfl)
    (causal_peak_at_state hpre hX hs hg hmma hIssuer hi hPrior le_rfl hd)
    (Wg0HalfMass.causal_mass_at_state hpre hX hs hg hmma hIssuer hi hPrior le_rfl hd)
  obtain ⟨hqMass, _⟩ := epilogue_mass_from_histories hpre hqInv (by rw [hQ]; rfl)
    (causal_peak_at_state hpre hX hs hw hmma' hIssuer' hj hMate le_rfl hq)
    (Wg0HalfMass.causal_mass_at_state hpre hX hs hw hmma' hIssuer' hj hMate le_rfl hq)
  let own := Wg0HalfMass.prefixWeight P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g)
    (head L g) (half L g) (blocksOf P L g)
  let other := Wg0HalfMass.prefixWeight P (Wg1Mma.batchOf L mate) (Wg1Mma.queryOf L mate)
    (head L mate) (half L mate) (blocksOf P L mate)
  change lseOwnSum d = (2 : ℝ) ^ (-reference d) * own at hdMass
  change lseOwnSum q = (2 : ℝ) ^ (-reference q) * other at hqMass
  have hdScale : 0 < (2 : ℝ) ^ (-reference d) := Real.rpow_pos_of_pos (by norm_num) _
  have hqScale : 0 < (2 : ℝ) ^ (-reference q) := Real.rpow_pos_of_pos (by norm_num) _
  have hOwn : 0 ≤ own := Wg0HalfMass.prefixWeight_nonneg P _ _ _ _ _
  have hOther : 0 ≤ other := Wg0HalfMass.prefixWeight_nonneg P _ _ _ _ _
  have hdNonneg : 0 ≤ lseOwnSum d := hdMass ▸ mul_nonneg hdScale.le hOwn
  have hqNonneg : 0 ≤ lseOwnSum q := hqMass ▸ mul_nonneg hqScale.le hOther
  have hdZero : lseOwnSum d = 0 ↔ own = 0 := by
    rw [hdMass, mul_eq_zero, or_iff_right hdScale.ne']
  have hqZero : lseOwnSum q = 0 ↔ other = 0 := by
    rw [hqMass, mul_eq_zero, or_iff_right hqScale.ne']
  have hCtaMate : ctaOf L mate = ctaOf L g := hCta
  have hBatch : Wg1Mma.batchOf L mate = Wg1Mma.batchOf L g := by
    simp only [Wg1Mma.batchOf_eq_ctaidY, ctaidY, hCtaMate]
  have hQuery : Wg1Mma.queryOf L mate = Wg1Mma.queryOf L g := by
    simp only [Wg1Mma.queryOf_eq_ctaidX, ctaidX, hCtaMate]
  have hBlocks : blocksOf P L mate = blocksOf P L g := by
    change blocks P (Wg1Mma.batchOf L mate) = blocks P (Wg1Mma.batchOf L g)
    rw [hBatch]
  obtain ⟨hMain, hExtra⟩ := length_bounds hpre g
  have hParts := Wg0HalfMass.halves_eq_rowSum P _ (Wg1Mma.queryOf L g) (head L g) hMain hExtra
  have hSum : own + other =
      rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) := by
    dsimp only [own, other]
    rw [hBatch, hQuery, hHead, hHalf, hBlocks]
    have hh := halfLt hdInv.warpLt
    obtain h0 | h1 : half L g = 0 ∨ half L g = 1 := by omega
    · rw [h0, show 1 - 0 = (1 : Nat) by decide]
      exact hParts
    · rw [h1, Nat.sub_self, add_comm]
      exact hParts
  refine ⟨add_nonneg hdNonneg hqNonneg, ?_⟩
  change lseOwnSum d + lseOwnSum q = 0 ↔ d.peak = ⊥
  rw [hPeak, ← hSum]
  constructor
  · intro h
    rw [hdZero.mp (by linarith), hqZero.mp (by linarith), zero_add]
  · intro h
    rw [hdZero.mpr (by linarith), hqZero.mpr (by linarith), zero_add]
end

variable {g i : Nat}

/-- The actual shared read decodes the paired half at the row's final exponent reference. -/
theorem actual_read_total {d : Wg0.D} {a : Acc} {values : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    :
    ∃ peer : ℝ,
      (rebuild 3 values).toOption.bind (fun v => (valFloat .f32 v).toOption) = some peer ∧
      lseOwnSum d + peer = (2 : ℝ) ^ (-reference d) *
        rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) ∧
      RowTotal { d with li := lseOwnSum d + peer } := by
  obtain ⟨j, q, fp, hq, hQ, hBlock, hw, _, _, hDecode⟩ :=
    Wg0LseReadback.readback_value hpre hX hs ht hr hd hsite
  obtain ⟨hSum, hRow⟩ :=
    lse_pair_mass hpre hX hs ht hr.choose_spec hw.choose_spec hd hq hsite hQ hBlock
  exact ⟨lseOwnSum q, hDecode, hSum, hRow⟩

/-- The successful LSE read stores the scaled specification row sum as its actual mass. -/
theorem lse_read_updates {d d' : Wg0.D} {e : Event} {a : Acc} {values : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values) (hk : e.kind = .rd a values)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    (hn : Machine.next P L g (.wg0 d) e = some (some (.wg0 d'))) :
    d'.li = (2 : ℝ) ^ (-reference d') *
      rowSum P (Wg1Mma.batchOf L g) (Wg1Mma.queryOf L g) (head L g) ∧ RowTotal d' := by
  obtain ⟨peer, hPeer, hSum, hTotal⟩ := actual_read_total hpre hX hs ht hr hd hsite
  simp only [Machine.next] at hn
  split at hn
  · rename_i out hNext
    cases hn
    simp only [Wg0.next, nextSite, hsite, hk, hPeer] at hNext
    split at hNext
    · let next : D := { d with
        site := if tidOf L g % 128 < 64 then .lseStore else .svDone
        sub := 0, li := lseOwnSum d + peer, lp := peer }
      change (if RowTotal next then some (some next) else some none) = _ at hNext
      have hRow : RowTotal next := hTotal
      rw [ite_eq_left hRow] at hNext
      have hEq := Option.some.inj (Option.some.inj hNext)
      rw [← hEq]
      exact ⟨hSum, hRow⟩
    · cases hNext
  · split at hn <;> cases hn
  · cases hn

/-- The actual two halves' causal histories supply the LSE guard. -/
theorem causal_lse_read_never_dismiss {d : Wg0.D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .lseRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  rcases Wg0LseReadback.actual_next_of_row_total hpre hX hs he hd hsite hPrior
    (fun j q fp hq hQ _ hw hBefore =>
      causal_lse_row_total hpre hX hs he hw.choose_spec hd hq hsite hQ hBefore hPrior)
    with h | ⟨d', h, _⟩ <;> simp [h]

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0RunningPeak

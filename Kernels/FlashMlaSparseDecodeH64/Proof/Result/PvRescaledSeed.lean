-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvInitialAccumulator
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.PvRescaleGain
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvRescalePublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputTmemWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescalePayload

@[expose] public section

/-! # The actual read of a later PV block's initial accumulator -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow PTX.AsyncCopy Protocol
open PvAccumulatorSource (Issue RescaleStore)
open MmaDataTrace (pvAccum)
open Wg1Mma (tmemO)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem rescale_value_at_cell {g t j block : Nat} {q : Wg0.D} {tile : Fin 4}
    (head : Fin 64) (half : Fin 2) (col : Fin 256) (prior : ℝ)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) g)
    (hb : 0 < block) (hqBlock : q.block = block) :
    let cell : TcMma.Cell :=
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
    let ref := canonicalPvReference P L X (ctaOf L g)
    RescaleStore P L X t j cell q tile →
    (∀ {s c : Nat} {rank : Fin 16},
      Frame.stateAt (Machine.code P L) X g s =
        some (some (.mma ⟨.pvMma (pvHalfIssue half 3), block - 1⟩)) →
      Issue L X g s (block - 1) (pvHalfIssue half 3) →
      TracksMma X (g, s) (g, c) → rank ∈ X.tcNotified (g, c) →
      TcMma.Result L Assumptions.all X (g, s) cell (.float .f32 prior)) →
    TcMma.StoreValue L X (t, j) cell
      (.float .f32 (prior * 2 ^ (ref (block - 1) head.val - ref block head.val))) := by
  dsimp only
  intro hStore hPrior
  obtain ⟨hCta, hT, hTile⟩ := PvInitialAccumulator.rescale_coordinates hpre hX hs hStore
  have hHead : Wg0.head L t = head.val := by
    have hh := head.isLt
    change head.val + 64 * (col.val / 128) = tidOf L t at hT
    change tidOf L t % 64 = head.val
    omega
  have hHalf : OutputTmemReadSource.tileHalf tile = half := by
    apply Fin.ext
    have hCol := Nat.mod_lt col.val (by decide : 0 < 128)
    change (tmemO + 128 * half.val + col.val % 128) / 64 = tile.val at hTile
    change tile.val / 2 = half.val
    simp only [tmemO, Nat.zero_add] at hTile
    omega
  have hLast : OutputTmemReadSource.lastIssue tile = pvHalfIssue half 3 :=
    congrArg (fun k => pvHalfIssue k 3) hHalf
  obtain ⟨ld, old, waitState, tag, reg, _, _, _, _, _, _, hCell, hWait, hWaitEvent,
    hWaitSite, hWaitBlock, hWords, hWriteValue⟩ :=
    Wg0.rescale_cell_payload hpre hX hs hStore.state hStore.site hStore.store hStore.covers
  have hMma : GemmRing.MmaIssuer P L X (ctaOf L t) g := hCta ▸ hmma
  obtain ⟨src, c, rank, hSrc, hIssue, hTrack, hNotify, _, hRead⟩ :=
    OutputTmemWords.rescale_word_from_prior hpre hX hs hMma hWait hWaitSite hWaitEvent reg
  rw [hLast, hWaitBlock, hqBlock] at hSrc hIssue
  have hVal := hPrior hSrc hIssue hTrack hNotify
  have hReadPrior : q.rescaleWords[reg.val]? = some (.float .f32 prior) := by
    rw [← hWords]
    apply hRead prior
    simpa only [OutputTmemReadSource.outputCell, ← hCell] using hVal
  have hOrd : Wg0VoteCount.ordinal q = q.block + 1 := by
    rw [Wg0VoteCount.ordinal, hStore.site]
    rfl
  have hGain := (pv_rescale_gain hpre hX hs ht hStore.store.choose_spec
    hStore.state hOrd (hqBlock.symm ▸ hb)).2.1
  rw [← hCta, hHead, hqBlock] at hGain
  exact hWriteValue prior _ hReadPrior hGain

/-- A later PV issue really starts at the previous output expressed in its new reference scale. -/
theorem pv_rescaled_seed {g i block : Nat}
    (head : Fin 64) (half : Fin 2) (col : Fin 256) (prior : ℝ)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) g)
    (hi : Issue L X g i block (pvHalfIssue half 0))
    (hd : Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma (pvHalfIssue half 0), block⟩)))
    (hb : 0 < block) :
    let cell : TcMma.Cell :=
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
    let ref := canonicalPvReference P L X (ctaOf L g)
    (∀ {s c : Nat} {seen : Fin 16},
      Frame.stateAt (Machine.code P L) X g s =
        some (some (.mma ⟨.pvMma (pvHalfIssue half 3), block - 1⟩)) →
      Issue L X g s (block - 1) (pvHalfIssue half 3) →
      TracksMma X (g, s) (g, c) → seen ∈ X.tcNotified (g, c) →
      TcMma.Result L Assumptions.all X (g, s) cell (.float .f32 prior)) →
    GemmAccumulator L X (g, i) cell (pvAccum block (pvHalfIssue half 0))
      (prior * 2 ^ (ref (block - 1) head.val - ref block head.val)) := by
  dsimp only
  intro hPrior
  have hAcc : pvAccum block (pvHalfIssue half 0) = true := by
    simp [pvAccum, hb.ne']
  rw [hAcc]
  obtain ⟨src, hRead, hKind⟩ := PvInitialAccumulator.from_first_issue hpre hX hs ht hi hd hb
    head col
  rcases hKind with ⟨s, _, rfl, hSrc, hIssue, hNoStore⟩ | ⟨t, j, q, tile, rfl, hStore, hBlock⟩
  · obtain ⟨a, out, e, he, hout, hSite, hBlock, _, hMatch⟩ :=
      PvRescalePublication.writer_publication hpre hX hs ht hi.choose_spec hd rfl head half col
    have hTaken : out.voteTaken = false := by
      cases hv : out.voteTaken
      · rfl
      · have hWants : Wg0.wantsRescale out = true := by
          change out.block = block at hBlock
          simp [Wg0.wantsRescale, hBlock, hb.ne', hv]
        obtain ⟨j, _, q, hQ, hStore⟩ := hMatch hWants
        exact (hNoStore ⟨_, j, q, _, hStore, hQ⟩).elim
    have hOrd : Wg0VoteCount.ordinal out = out.block + 1 := by
      rw [Wg0VoteCount.ordinal, hSite]
      rfl
    change out.block = block at hBlock
    have hEq := (pv_rescale_gain hpre hX hs ht he hout hOrd (hBlock.symm ▸ hb)).2.2 hTaken
    obtain ⟨hCta, hHead⟩ := PvRescalePublication.writer_geometry hpre (ctaOf L g) head col
    rw [hCta, hHead, hBlock] at hEq
    rw [hEq, sub_self, Real.rpow_zero, mul_one]
    have hSoftmax := Frame.lt_of_get hX he
    obtain ⟨_, _, _, _, p, _, q, event, _, hGet, hQ, hQBlock, hQSite, _, _⟩ :=
      Wg0ProbabilityRelease.store_before_publication hX (hs _ hSoftmax).machine ht
        he hout hSite 0 0
    obtain ⟨w, _, waitTag, parity, scope, c, tag, sp, rank, d, hWait, hCommit,
      _, hCommitState, _, _, hDBlock, _, hObs⟩ :=
      GemmRing.qk_commit_before_probability hpre hX (fun t ht' => (hs t ht').machine) ht
        hmma hQ hQSite hGet
    have hDBlock' : d.i = block := hDBlock.trans (hQBlock.trans hBlock)
    have hPriorLt : s < c := by
      by_contra! h
      have hh := Wg1Mma.block_order h hCommitState hSrc
      change d.i ≤ block - 1 at hh
      omega
    have hTrack : TracksMma X (g, s) (g, c) :=
      ⟨rfl, hPriorLt, .inl ⟨_, _, _, _, hIssue⟩, sp, tag, hCommit⟩
    exact .priorMma hRead (hPrior hSrc hIssue hTrack (hObs.waitObserves_tcNotify hWait).1)
  · exact .priorStore hRead
      (rescale_value_at_cell head half col prior hpre hX hs ht hmma hb hBlock hStore hPrior)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

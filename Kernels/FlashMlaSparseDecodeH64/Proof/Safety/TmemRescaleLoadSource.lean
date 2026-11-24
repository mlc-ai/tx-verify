-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RescaleTmemReadSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvInitialAccumulator
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.PvCompletedValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescaleGainTrace
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # A rescale load already has a completed value from the prior PV block at issue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Protocol Result OutputTmemReadSource

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {g i : Nat} {words : List Value} {tile : Fin 4} {d : Wg0.D} (reg : Fin 64)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleLoad tile) (hload : X.TLd (g, i) (64 * tile.val) words .s32x32b)
include hpre hX hs ht reg hd hsite hload

/-- At a rescale load, its preceding QK acquire certifies the preceding block's PV value. -/
theorem rescale_value_at_load :
    ∃ issuer src value, ctaOf L issuer = ctaOf L g ∧
      GemmRing.MmaIssuer P L X (ctaOf L g) issuer ∧
      Frame.stateAt (Machine.code P L) X issuer src =
        some (some (.mma ⟨.pvMma (lastIssue tile), d.block - 1⟩)) ∧
      PvAccumulatorSource.Issue L X issuer src (d.block - 1) (lastIssue tile) ∧
      X.MmaCell (issuer, src) (outputCell L g tile reg) ∧
      TcMma.DoneBefore L X (issuer, src) (g, i) ∧
      TcMma.Result L Assumptions.all X (issuer, src) (outputCell L g tile reg) value := by
  have he := hload.choose_spec
  have hIn : d.site.inRescale = true := by rw [hsite]; rfl
  have hi := (PTX.len_of_get he).le
  have hPos := Wg0RescaleGainTrace.rescale_block_pos hi hd hIn
  obtain ⟨issuer, hu⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
    (fun a ha => (hs a ha).machine)
  obtain ⟨w, wt, parity, c, ct, scope, sp, rank, cd, hwlt, hw, hc, hTarget, hCd,
    hCta, hBlock, hObs⟩ :=
    RescaleTmemReadSource.earlier_qk_in_rescale hpre hX hs ht hu hd hIn he
  obtain ⟨src, hSrcLt, hSrc, hIssue⟩ := PvInitialAccumulator.prior_block_issue_before
    hpre hX hs ht hc hCd (hBlock.symm ▸ hPos) (lastIssue tile)
  rw [hBlock] at hSrc hIssue
  have hBefore := done_before_of_observed hX hIssue hSrcLt hc hTarget hw hObs hCta hwlt hload
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  have hLane : tidOf L g < 128 := by
    have := (show Wg0.Inv P L g d from hInv).warpLt
    unfold warpOf at this
    omega
  have hWrite := output_cell_written hpre hLane hCta tile reg hIssue
  obtain ⟨v, hv⟩ := pv_completed_values hpre hX hs ht hIssue hSrc
    (hBefore.done hX.tcCommit) _ hWrite
  exact ⟨issuer, src, v, hCta, hu, hSrc, hIssue, hWrite, hBefore, hv⟩

/-- A rescale load already has a live source, even while its own load wait is pending. -/
theorem rescale_load_source (hWords : words.length = 64) :
    ∃ src value, TcMma.ReadSource L X .ld src (g, i) (outputCell L g tile reg) ∧
      TcMma.Wrote L Assumptions.all X src (outputCell L g tile reg) value := by
  let cell := outputCell L g tile reg
  obtain ⟨issuer, src, v, hCta, hu, hSrc, hIssue, hWrite, hDone, hValue⟩ :=
    rescale_value_at_load hpre hX hs ht reg hd hsite hload
  have hCell : TcMma.LoadCell L X (g, i) reg.val cell :=
    ⟨_, _, _, hload, hWords.symm ▸ reg.isLt, rfl⟩
  have hne : (issuer, src) ≠ (g, i) := by
    intro he
    obtain ⟨tag, hGet⟩ := hIssue
    rw [he] at hGet
    cases congrArg Event.kind (Option.some.inj (hGet.symm.trans hload.choose_spec))
  refine ⟨(issuer, src), v, ⟨hne, .inl hWrite, .inl (.inl hDone), ?_,
    tmem_load_source_live hpre hX hs ht hCell⟩, .inl hValue⟩
  rintro ⟨t, j⟩ hOther
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hload.choose_spec hd
  have hLane : tidOf L g < 128 := by
    have := (show Wg0.Inv P L g d from hInv).warpLt
    unfold warpOf at this
    omega
  have hEq := outputCell_eq hpre hLane tile reg
  have hCol : cell.column < 256 := by
    change (outputCell L g tile reg).column < 256
    rw [hEq]
    have := tile.isLt
    have := reg.isLt
    change 64 * tile.val + reg.val < 256
    omega
  obtain ⟨hOwner, hRole⟩ := PvAccumulatorSource.output_writer hpre hX hs ht hCol hOther
  have hCt : ctaOf L t = ctaOf L g := hOwner.symm.trans (congrArg TcMma.Cell.cta hEq)
  rcases hRole with ⟨q, k, hq, hqSite, hQIssue, hHalf⟩ | ⟨q, k, hStore⟩
  · have heq := hu t j q hCt hq (by rw [hqSite]; simp)
    subst t
    by_cases hLater : d.block ≤ q.i
    · exact .inr (.inr (.inl (RescaleTmemReadSource.rescale_read_before_later_pv
        hpre hX hs ht hCta hd hsite hload hQIssue hq hqSite hLater)))
    · have hColHalf : cell.column / 128 = tile.val / 2 := by
        change (outputCell L g tile reg).column / 128 = tile.val / 2
        rw [hEq]
        have := reg.isLt
        change (64 * tile.val + reg.val) / 128 = tile.val / 2
        omega
      have hSameHalf : k.val % 2 = (lastIssue tile).val % 2 := by
        rw [lastIssue_half, ← hColHalf, hHalf]
      have hJ := prior_pv_index hpre hX hs ht (show q.i ≤ d.block - 1 by omega)
        hQIssue hIssue hq hqSite hSrc hSameHalf
      rcases Nat.eq_or_lt_of_le hJ with rfl | hLt
      · exact .inl rfl
      · exact .inr (.inl (.inl (PvAccumulatorSource.pv_before hX hQIssue hIssue hLt hSameHalf)))
  · by_cases hLater : d.block ≤ q.block
    · exact .inr (.inr (.inl (RescaleTmemReadSource.rescale_read_before_later_store
        hpre hX hs ht hd hsite hload hLane hStore hLater)))
    · have hEarlier : q.block ≤ d.block - 1 := by omega
      exact .inr (.inl (PvAccumulatorSource.earlier_rescale hpre hX hs ht hIssue hSrc
        rfl hStore (hCt.trans hCta.symm) hEarlier))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

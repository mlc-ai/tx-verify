-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadbackSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.QkCompletedValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmScoreLoads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QkWriteOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemRelease
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The completed QK writer is available when a score load issues -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Protocol Result MmaDataTrace Wg1Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- At the load itself, the QK acquire supplies the last issue and its completed score value. -/
theorem score_value_at_load (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (_ht : Frame.Tracked (Machine.code P L) X)
    {g i : Nat} {d : Wg0.D} {arm part : Fin 2} {words : List Value} (reg : Fin 32)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .scoreLoad arm part)
    (hload : X.TLd (g, i) (Wg0.scoreLoadColumn part) words .s32x32b) :
    let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val
    ∃ issuer src value, ctaOf L issuer = ctaOf L g ∧
      GemmRing.MmaIssuer P L X (ctaOf L g) issuer ∧
      Frame.stateAt (Machine.code P L) X issuer src = some (some (.mma ⟨.qkMma 15, d.block⟩)) ∧
      X.MmaIssue (issuer, src) tmemP (qkOperands L issuer d.block 15)
        (qkAccum 15) [0, 0, 0, 0] ∧
      X.MmaCell (issuer, src) cell ∧ TcMma.DoneBefore L X (issuer, src) (g, i) ∧
      TcMma.Result L Assumptions.all X (issuer, src) cell value := by
  let cta := ctaOf L g
  have he := hload.choose_spec
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  have hInv : Wg0.Inv P L g d := hInv
  have hLaneLt : tidOf L g < 128 := by have := hInv.warpLt; unfold warpOf at *; omega
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre (cta := cta) rfl hInv.wg
  obtain ⟨w, q, tag, scope, hwi, hq, hQSite, hBlock, hw⟩ :=
    Wg0ScoreEventHistory.qk_wait_before_score_load hpre hX hs hd hsite (PTX.len_of_get he).le
  obtain ⟨issuer, hu⟩ := GemmRing.exists_issuer (cta := cta) hpre hX
    (fun a ha => (hs a ha).machine)
  have hq' : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) w =
      some (some (.wg0 q)) := by rwa [← hLane]
  have hw' : X.get (GemmRing.softmax L cta lane, w) =
      some ⟨tag, .wait (GemmRing.qk L cta (rawSlot q.block)) (q.block / 2 % 2) true true scope⟩ :=
    hLane ▸ hw
  have hload' : X.TLd (GemmRing.softmax L cta lane, i)
      (Wg0.scoreLoadColumn part) words .s32x32b := hLane ▸ hload
  obtain ⟨src, hSrc, hIssue, hBefore⟩ :=
    ScoreReadback.qk_issue_before_score hpre hX hs hu hq' hQSite hw' hwi hload' 15
  obtain ⟨_, _, _, _, _, _, _, _, hCta, _, _, _⟩ :=
    ScoreReadback.commit_of_qk_wait hpre hX hs hu hq' hQSite hw'
  rw [hBlock] at hSrc hIssue
  rw [← hLane] at hBefore
  have hWrite := ScoreReadback.issue_score_cell hpre hLaneLt hCta.symm hIssue part reg
  have hDone := hBefore.done hX.tcCommit
  obtain ⟨value, hVal⟩ := qk_completed_values hpre hX hs hIssue hSrc hDone _ hWrite
  exact ⟨issuer, src, value, hCta, hu, hSrc, hIssue, hWrite, hBefore, hVal⟩

/-- A pending score load already has a stable, value-bearing source for each of its cells. -/
theorem score_load_source (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {g i : Nat} {d : Wg0.D} {arm part : Fin 2} {words : List Value} (reg : Fin 32)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .scoreLoad arm part)
    (hload : X.TLd (g, i) (Wg0.scoreLoadColumn part) words .s32x32b) (hWords : words.length = 32) :
    let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val
    ∃ src value, TcMma.ReadSource L X .ld src (g, i) cell ∧
      TcMma.Wrote L Assumptions.all X src cell value := by
  let cta := ctaOf L g
  let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val
  obtain ⟨issuer, src, val, hCTA, hu, hSrc, hIssue, hWrite, hDone, hVal⟩ :=
    score_value_at_load hpre hX hs ht reg hd hsite hload
  have hCell : TcMma.LoadCell L X (g, i) reg.val cell :=
    ⟨_, _, _, hload, hWords.symm ▸ reg.isLt, rfl⟩
  have hne : (issuer, src) ≠ (g, i) := by
    intro he
    obtain ⟨tag, hl⟩ := hIssue
    rw [he] at hl
    cases congrArg Event.kind (Option.some.inj (hl.symm.trans hload.choose_spec))
  refine ⟨(issuer, src), val, ⟨hne, .inl hWrite, .inl (.inl hDone), ?_,
    tmem_load_source_live hpre hX hs ht hCell⟩, .inl hVal⟩
  intro other hOther
  have hGet := hload.choose_spec
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hGet hd
  have hInv : Wg0.Inv P L g d := hInv
  have hLaneLt : tidOf L g < 128 := by have := hInv.warpLt; unfold warpOf at *; omega
  have hCol : 400 ≤ cell.column := by
    unfold cell
    rw [scoreLoad_cell hpre hLaneLt]
    change 400 ≤ 400 + _
    omega
  obtain ⟨j, q, k, rfl, hq, hqSite, hQ⟩ :=
    ScoreReadback.score_issue_of_writer hpre hX hs hu (show cell.cta = cta by rfl) hCol hOther
  by_cases hLater : d.block < q.i
  · obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre (cta := cta) rfl hInv.wg
    have hl : X.TLd (GemmRing.softmax L cta lane, i)
        (Wg0.scoreLoadColumn part) words .s32x32b := by rwa [← hLane]
    have hst : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) i =
        some (some (.wg0 d)) := by rwa [← hLane]
    have hBefore := ScoreReadback.read_before_later_qk_at_score_load hpre hX hs ht hu hCTA
      hQ.choose_spec hq hqSite hLater hl hst hsite
    rw [← hLane] at hBefore
    exact .inr (.inr hBefore)
  · have hLe := QkWriteOrder.no_later_same_block_writer hIssue.choose_spec hSrc hq rfl hqSite
      (show q.i ≤ d.block by omega) (PTX.len_of_get hQ.choose_spec).le
    rcases Nat.eq_or_lt_of_le hLe with rfl | hlt
    · exact .inl rfl
    · exact .inr (.inl (ScoreReadback.earlier_qk_write hX hQ hIssue hlt))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

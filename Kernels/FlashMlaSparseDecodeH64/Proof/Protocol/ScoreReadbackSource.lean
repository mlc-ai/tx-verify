-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadbackOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreEventHistory
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QkWriteOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreTracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmScoreLoads
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

/-! # The last QK instruction supplies each score cell -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback

open PTX PTX.Flow GemmRing Wg1Mma MmaDataTrace

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A QK issue writes the represented score cell for this lane and part. -/
theorem issue_score_cell
    {g issuer i block : Nat} {k : Fin 16}
    (hpre : Pre P L mem0) (hg : tidOf L g < 128) (hc : ctaOf L g = ctaOf L issuer)
    (hi : X.MmaIssue (issuer, i) tmemP (qkOperands L issuer block k)
      (qkAccum k) [0, 0, 0, 0]) (part : Fin 2) (reg : Fin 32) :
    X.MmaCell (issuer, i) (tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val) := by
  let row : Fin 64 := ⟨tidOf L g % 64, Nat.mod_lt _ (by decide)⟩
  let col : Fin 128 := ⟨64 * (tidOf L g / 64) + 32 * part.val + reg.val, by
    have := part.isLt
    have := reg.isLt
    omega⟩
  rw [Result.scoreLoad_cell hpre hg part reg]
  change X.MmaCell (issuer, i)
    ⟨ctaOf L g, tidOf L g, tmemP + (32 * part.val + reg.val)⟩
  rw [hc]
  refine ⟨_, _, _, _, row.val, col.val, hi, ?_⟩
  rw [Result.qkWriteCell L issuer block k row col]
  simp only [Option.some.injEq, TcMma.Cell.mk.injEq, true_and]
  constructor
  · change tidOf L g % 64 + 64 * ((64 * (tidOf L g / 64) + 32 * part.val + reg.val) / 64) =
      tidOf L g
    have := part.isLt
    have := reg.isLt
    omega
  · change tmemP + (64 * (tidOf L g / 64) + 32 * part.val + reg.val) % 64 =
      tmemP + (32 * part.val + reg.val)
    have := part.isLt
    have := reg.isLt
    omega

private theorem writer_cta
    {g i block : Nat} {k : Fin 16} {cell : TcMma.Cell}
    (hi : X.MmaIssue (g, i) tmemP (qkOperands L g block k) (qkAccum k) [0, 0, 0, 0])
    (hw : TcMma.TmemWrite L X (g, i) cell) : cell.cta = ctaOf L g := by
  obtain ⟨_, he⟩ := hi
  rcases hw with hw | hw | hw | hw
  · obtain ⟨d, s, _, _, _, _, ⟨_, he'⟩, hp⟩ := hw
    have h := congrArg Event.kind (Option.some.inj (he'.symm.trans he))
    obtain ⟨_, rfl, _, _⟩ := TcKind.mma.inj (Kind.tc.inj h)
    exact (TcMma.resultCell_cta (TcMma.writeCell_resultCell hp)).elim id id
  · obtain ⟨_, _, _, _, ⟨_, he'⟩, _, _⟩ := hw
    cases congrArg Event.kind (Option.some.inj (he.symm.trans he'))
  · obtain ⟨_, _, _, _, ⟨_, he'⟩, _, _, _, _⟩ := hw
    cases congrArg Event.kind (Option.some.inj (he.symm.trans he'))
  · obtain ⟨_, ⟨_, he'⟩, _⟩ := hw
    cases congrArg Event.kind (Option.some.inj (he.symm.trans he'))

/-- A competing score write is an actual QK issue of the score CTA's unique issuer. -/
theorem score_issue_of_writer {cta issuer : Nat} {e : EvId} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer) (hCta : cell.cta = cta)
    (hCol : 400 ≤ cell.column) (hw : TcMma.TmemWrite L X e cell) :
    ∃ j d k, e = (issuer, j) ∧
      Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma d)) ∧
      d.site = .qkMma k ∧
      X.MmaIssue (issuer, j) tmemP (qkOperands L issuer d.i k) (qkAccum k) [0, 0, 0, 0] := by
  obtain ⟨g, j⟩ := e
  obtain ⟨d, k, hr, hs', hi⟩ := Wg0ScoreSources.actual_score_write hpre hX hs hCol hw
  have hg := hmma g j d ((writer_cta hi hw).symm.trans hCta) hr (by rw [hs']; simp)
  subst g
  exact ⟨j, d, k, rfl, hr, hs', hi⟩

/-- At an actual mask-read state, choose the final QK issue as the read source of any
loaded score register. The source writes the cell and has finished; every other writer
is earlier or ordered after the load. The separate allocation lifetime premise is explicit. -/
theorem final_qk_score_source_at
    {cta issuer j : Nat} {lane : Fin 128} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (softmax L cta lane) j = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) (hlen : j ≤ (X.tr (softmax L cta lane)).length)
    (part : Fin 2) (reg : Fin 32) :
    let g := softmax L cta lane
    let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val
    ∃ src ld words, ld + (4 - part.val) = j ∧ ld + 3 ≤ j ∧
      Frame.stateAt (Machine.code P L) X issuer src = some (some (.mma ⟨.qkMma 15, d.block⟩)) ∧
      TcMma.LoadCell L X (g, ld) reg.val cell ∧
      X.TLd (g, ld) (Wg0.scoreLoadColumn part) words .s32x32b ∧
      X.MmaIssue (issuer, src) tmemP (qkOperands L issuer d.block 15) (qkAccum 15) [0, 0, 0, 0] ∧
      X.MmaCell (issuer, src) cell ∧
      (TcMma.SourceLive L X (issuer, src) (g, ld) cell →
        TcMma.ReadSource L X .ld (issuer, src) (g, ld) cell) := by
  dsimp only
  let g := softmax L cta lane
  let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val
  have hgcta : ctaOf L g = cta := by
    have := lane.isLt
    simp only [g, softmax, ctaOf, hpre.block]
    omega
  have hg : tidOf L g < 128 := by
    have hl := lane.isLt
    rw [tidOf_eq hpre]
    have hh : g % 384 = lane.val := by
      simp only [g, softmax, hpre.block]
      omega
    omega
  obtain ⟨w, q, entry, sw, tag, ltag, scope, rfl, hq, hqSite, hbq, hw, hentry, heSite, _,
    hsw, hsSite, hbs, hwait⟩ := Wg0ScoreEventHistory.waits_of_mask hpre hX hs hd hsite hlen
  have hlen' : w + 1 + 5 ≤ (X.tr g).length := hlen
  obtain ⟨lo, hi, _, _, hlo, hhi, _⟩ :=
    Wg0.maskRead_score_history hpre hX hs hentry heSite hd hlen'
  let ld := w + 2 + part.val
  obtain ⟨words, hload, hWords⟩ : ∃ words,
      X.TLd (g, ld) (Wg0.scoreLoadColumn part) words .s32x32b ∧ words.length = 32 := by
    fin_cases part
    · exact ⟨lo, hlo.choose_spec.2.2.2⟩
    · exact ⟨hi, hhi.choose_spec.2.2.2⟩
  have hw' : X.get (g, w) = some
      ⟨tag, .wait (qk L cta (rawSlot q.block)) (q.block / 2 % 2) true true scope⟩ := by
    rw [← hbq, hgcta] at hw
    exact hw
  have hwd : w < ld := by dsimp [ld]; omega
  obtain ⟨src, hSrcState, hSrc, hDone⟩ :=
    qk_issue_before_score hpre hX hs hmma hq hqSite hw' hwd hload 15
  rw [hbq] at hSrcState hSrc
  obtain ⟨_, _, _, _, _, _, _, _, hctai, _, _, _⟩ :=
    commit_of_qk_wait hpre hX hs hmma hq hqSite hw'
  have hWrite := issue_score_cell hpre hg (hgcta.trans hctai.symm) hSrc part reg
  have hGap : ld + 3 ≤ w + 6 := by
    have := part.isLt
    dsimp [ld]
    omega
  have hLoadCell : TcMma.LoadCell L X (g, ld) reg.val cell :=
    ⟨_, _, _, hload, by rw [hWords]; exact reg.isLt, rfl⟩
  have hIndex : ld + (4 - part.val) = w + 6 := by
    have := part.isLt
    dsimp [ld]
    omega
  refine ⟨src, ld, words, hIndex, hGap, hSrcState, hLoadCell, hload, hSrc, hWrite, ?_⟩
  intro hLive
  have hne : (issuer, src) ≠ (g, ld) := by
    intro hEq
    obtain ⟨_, hget⟩ := hSrc
    rw [hEq] at hget
    cases congrArg Event.kind (Option.some.inj (hget.symm.trans hload.choose_spec))
  refine ⟨hne, .inl hWrite, .inl (.inl hDone), ?_, hLive⟩
  intro other hwo
  have hcol : 400 ≤ cell.column := by
    unfold cell
    rw [Result.scoreLoad_cell hpre hg]
    change 400 ≤ 400 + (32 * part.val + reg.val)
    omega
  have hCellCta : cell.cta = cta := by
    unfold cell
    rw [Result.scoreLoad_cell hpre hg]
    exact hgcta
  obtain ⟨oi, o, k, rfl, hrole, hoSite, ho⟩ :=
    score_issue_of_writer hpre hX hs hmma hCellCta hcol hwo
  have hother := ho.choose_spec
  by_cases hgt : d.block < o.i
  · have hwaitld : ld < w + 4 := by
      have := part.isLt
      dsimp [ld]
      omega
    exact .inr (.inr (read_before_later_qk hpre hX hs hmma hctai hother hrole hoSite
      (hbs.symm ▸ hgt) hwait hsw hsSite hwaitld))
  · have horder := QkWriteOrder.no_later_same_block_writer hSrc.choose_spec hSrcState hrole
      rfl hoSite (show o.i ≤ d.block by omega) (PTX.len_of_get hother).le
    rcases Nat.eq_or_lt_of_le horder with rfl | hlt
    · exact .inl rfl
    · exact .inr (.inl (earlier_qk_write hX ho hSrc hlt))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback

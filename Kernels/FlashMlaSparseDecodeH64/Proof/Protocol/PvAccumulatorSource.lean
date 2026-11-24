-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingObjects
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmSums
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputWaitGeneration
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingStageQkHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilityLaterWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescaleHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Lemmas.Protocol.UnitHandoff
import Lemmas.Tcgen05.TcDataCell
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # Adjacent PV results within one Tensor Memory output half -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvAccumulatorSource

open PTX PTX.Flow Wg1Mma MmaDataTrace AsyncCopy
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result (pvHalfIssue pvWriteCell)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The exact operands of a PV issue in the actual trace. -/
abbrev Issue (L : Launch) (X : Execution) (g i block : Nat) (k : Fin 8) : Prop :=
  X.MmaIssue (g, i) (pvDest k) (pvOperands L g block k) (pvAccum block k) [0, 0, 0, 0]

/-- A competing output-cell store belongs to a softmax rescale stage. -/
structure RescaleStore (P : Params) (L : Launch) (X : Execution) (g i : Nat)
    (cell : TcMma.Cell) (d : Wg0.D) (k : Fin 4) : Prop where
  state : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))
  site : d.site = .rescaleStore k
  store : X.TSt (g, i) (64 * k.val) (Wg0.rescaleStoreValues d) .s32x32b
  covers : TcMma.StoreCell L X (g, i) cell

private theorem pv_cell_columns {g block row col : Nat} {k : Fin 8} {cell : TcMma.Cell}
    (hw : TcMma.writeCell (pvOperands L g block k) (pvDest k) [0, 0, 0, 0]
      row col = some cell) : cell.cta = ctaOf L g ∧ cell.column / 128 = k.val % 2 := by
  have hr := TcMma.writeCell_resultCell hw
  have hdim : row < 64 ∧ col < 256 := by
    unfold TcMma.resultCell at hr
    dsimp only at hr
    split at hr
    · rename_i h
      exact ⟨h.2.2.1, h.2.2.2.1⟩
    · cases hr
  rw [pvResultCell L g block k ⟨row, hdim.1⟩ ⟨col, hdim.2⟩] at hr
  cases hr
  refine ⟨rfl, ?_⟩
  have hcol := Nat.mod_lt col (by decide : 0 < 128)
  change (pvDest k + col % 128) / 128 = k.val % 2
  simp only [pvDest, tmemO, Nat.zero_add]
  omega

private theorem qk_cell_columns {g block row col : Nat} {k : Fin 16} {cell : TcMma.Cell}
    (hw : TcMma.writeCell (qkOperands L g block k) tmemP [0, 0, 0, 0]
      row col = some cell) : 400 ≤ cell.column := by
  have hr := TcMma.writeCell_resultCell hw
  have hdim : row < 64 ∧ col < 128 := by
    unfold TcMma.resultCell at hr
    dsimp only at hr
    split at hr
    · rename_i h
      exact ⟨h.2.2.1, h.2.2.2.1⟩
    · cases hr
  rw [qkResultCell L g block k ⟨row, hdim.1⟩ ⟨col, hdim.2⟩] at hr
  cases hr
  change 400 ≤ 400 + col % 64
  omega

/-- A followed ordinary Tensor Memory write supplies its rescale state. -/
theorem followed_output_store {g i : Nat} {cell : TcMma.Cell} {addr : Nat}
    {words : List Value} {sh : TcShape}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hFollow : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (hw : X.TSt (g, i) addr words sh) (hCell : TcMma.StoreCell L X (g, i) cell) :
    ∃ d k, RescaleStore P L X g i cell d k := by
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine hFollow he (by simp)
  have hfields := Wg0ScoreSources.writer_fields hpre hg hf (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  rcases hfields with ⟨q, k, rfl, hsite, hk⟩ | ⟨_, _, _, _, hk⟩ |
    ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
  · obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
    exact ⟨q, k, hd, hsite, ⟨tag, he⟩, hCell⟩
  all_goals cases hk

/-- Actual output writers are PV issues or stores to a rescale slice. -/
theorem actual_output_writer {g i : Nat} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hcol : cell.column < 256)
    (hw : TcMma.TmemWrite L X (g, i) cell) :
    cell.cta = ctaOf L g ∧
    ((∃ (d : Wg1Mma.D) (k : Fin 8), Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧
      d.site = .pvMma k ∧ Issue L X g i d.i k ∧ cell.column / 128 = k.val % 2) ∨
    ∃ (k : Fin 4) (words : List Value), X.TSt (g, i) (64 * k.val) words .s32x32b ∧
      TcMma.StoreCell L X (g, i) cell ∧ words.length = 64 ∧
      cell.lane = tidOf L g ∧ cell.column / 64 = k.val) := by
  have fields {e : Event} (he : X.get (g, i) = some e) (hn : ∀ f, e.kind ≠ .ub f)
      (hFollow : Frame.stateAt (Machine.code P L) X g i ≠ some none)
      (hw : (∃ dst sp acc mask, e.kind = .tc (.mma dst sp acc mask)) ∨
        (∃ sp, e.kind = .tc (.cp sp)) ∨ (∃ dst words sh, e.kind = .tc (.st dst words sh)) ∨
        ∃ sp, e.kind = .tc (.shift sp)) :
      ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
        Wg0ScoreSources.WriterFields L g d e := by
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_at_followed hX (hs g hg).machine hFollow he hn
    exact ⟨d, hd, Wg0ScoreSources.writer_fields hpre hg hf hw⟩
  have nonstore_followed {e : Event} (he : X.get (g, i) = some e)
      (hWrite : Wg0ScoreSources.WritesTensorMemory e.kind)
      (hNoStore : ∀ dst vals sh, e.kind ≠ .tc (.st dst vals sh)) :
      Frame.stateAt (Machine.code P L) X g i ≠ some none := by
    intro hDismiss
    obtain ⟨tile, words, hKind, _⟩ :=
      Wg0ScoreSources.dismissed_writer_store hpre hX hs he hDismiss hWrite
    exact hNoStore _ _ _ hKind
  rcases hw with hw | hw | hw | hw
  · obtain ⟨dst, spec, accum, mask, row, col, ⟨tag, he⟩, hc⟩ := hw
    obtain ⟨d, hd, hfields⟩ := fields he (by simp)
      (nonstore_followed he trivial (by intros; simp)) (.inl ⟨_, _, _, _, rfl⟩)
    rcases hfields with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ |
      ⟨q, k, _, _, hk⟩ | ⟨q, k, rfl, hsite, hk⟩
    · cases hk
    · cases hk
    · obtain ⟨rfl, rfl, _, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hk)
      have := qk_cell_columns hc
      omega
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hk)
      obtain ⟨hcta, hhalf⟩ := pv_cell_columns hc
      exact ⟨hcta, .inl ⟨q, k, hd, hsite, ⟨tag, he⟩, hhalf⟩⟩
  · obtain ⟨dst, words, shape, r, ⟨tag, he⟩, hr, hcell⟩ := hw
    have hStore : ∃ k : Fin 4, dst = 64 * k.val ∧ shape = .s32x32b ∧
        words.length = 64 ∧ wgOf L g = 0 := by
      have hg := Frame.lt_of_get hX he
      by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
      · obtain ⟨k, _, hk, hLen⟩ :=
          Wg0ScoreSources.dismissed_writer_store hpre hX hs he hDismiss trivial
        obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
        have hWg : wgOf L g = 0 := by
          by_contra hn
          exact MachineTracking.tracked_nonsoftmax_wg hpre hX hs hn i hDismiss
        exact ⟨k, rfl, rfl, hLen, hWg⟩
      · obtain ⟨d, hd, hfields⟩ :=
          fields he (by simp) hDismiss (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
        rcases hfields with ⟨q, k, rfl, _, hk⟩ | ⟨_, _, _, _, hk⟩ |
          ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
        · obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
          exact ⟨k, rfl, rfl, by simp [Wg0.rescaleStoreValues],
            RingRoleGeometry.of_trace hX hg (hs g hg).machine hd⟩
        all_goals cases hk
    obtain ⟨k, rfl, rfl, hLength, hWg⟩ := hStore
    have hLane : g % 384 < 128 := by
      unfold wgOf at hWg
      rw [tidOf_eq hpre] at hWg
      omega
    have hk := k.isLt
    have haddr : 64 * k.val < 2 ^ 16 := by omega
    rw [hLength] at hr
    have hStoreCell : TcMma.StoreCell L X (g, i) cell :=
      ⟨_, _, _, r, ⟨tag, he⟩, hLength.symm ▸ hr, hcell⟩
    refine ⟨?_, .inr ⟨k, words, ⟨tag, he⟩, hStoreCell, hLength, ?_, ?_⟩⟩
    · rw [hcell, tcDataCell_s32x32b]
      rfl
    · rw [hcell, tcDataCell_s32x32b, tidOf_eq hpre]
      simp only [tcDataCell32, laneBase, PTX.laneOf, hpre.block]
      omega
    · rw [hcell, tcDataCell_s32x32b]
      simp only [tcDataCell32, Nat.mod_eq_of_lt haddr]
      omega
  · obtain ⟨spec, cta, index, lane, ⟨_, he⟩, _, _, _, hcell⟩ := hw
    obtain ⟨_, _, hfields⟩ := fields he (by simp)
      (nonstore_followed he trivial (by intros; simp)) (.inr (.inl ⟨_, rfl⟩))
    rcases hfields with ⟨_, _, _, _, hk⟩ | ⟨_, k, _, _, hk⟩ |
      ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩
    · cases hk
    · have hspec := TcKind.cp.inj (Kind.tc.inj hk)
      subst spec
      rw [hcell] at hcol
      have hk' := k.isLt
      have hbase : 256 + 8 * k.val < 2 ^ 16 := by omega
      change (256 + 8 * k.val) % 2 ^ 16 + index % 32 / 4 < 256 at hcol
      rw [Nat.mod_eq_of_lt hbase] at hcol
      omega
    all_goals cases hk
  · obtain ⟨spec, ⟨_, he⟩, _⟩ := hw
    obtain ⟨_, _, hfields⟩ := fields he (by simp)
      (nonstore_followed he trivial (by intros; simp)) (.inr (.inr (.inr ⟨spec, rfl⟩)))
    rcases hfields with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ |
      ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk

/-- All writers of an output cell are actual PV issues or actual softmax rescale stores. -/
theorem output_writer {g i : Nat} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hcol : cell.column < 256)
    (hw : TcMma.TmemWrite L X (g, i) cell) :
    cell.cta = ctaOf L g ∧
    ((∃ (d : Wg1Mma.D) (k : Fin 8), Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧
      d.site = .pvMma k ∧ Issue L X g i d.i k ∧ cell.column / 128 = k.val % 2) ∨
    ∃ (d : Wg0.D) (k : Fin 4), RescaleStore P L X g i cell d k) := by
  have hActual := actual_output_writer hpre hX hs hcol hw
  refine ⟨hActual.1, ?_⟩
  rcases hActual.2 with hm | ⟨k, words, hStore, hCell, _, _, _⟩
  · exact .inl hm
  · exact .inr (followed_output_store hpre hX hs
      (ht g i (Frame.lt_of_get hX hStore.choose_spec)) hStore hCell)

/-- PV issues from the same lane and half-tile follow their issue order. -/
theorem pv_before {g i j b b' : Nat} {k k' : Fin 8}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : Issue L X g i b k) (hj : Issue L X g j b' k') (hlt : i < j)
    (hhalf : k.val % 2 = k'.val % 2) : TcMma.Before L X (g, i) (g, j) := by
  apply TcMma.Before.of_mma_po hi hj (Frame.lt_of_get hX hi.choose_spec) rfl hlt
  exact ⟨congrArg (fun n => tmemO + 128 * n) hhalf, rfl, rfl, rfl, rfl⟩

section
variable {g i t j : Nat} {d : Wg1Mma.D} {k : Fin 8} {r : Fin 4} {q : Wg0.D} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

/-- A rescale write from this or an earlier block completes before the PV issue. -/
theorem actual_earlier_rescale (hi : Issue L X g i d.i k)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) (hsite : d.site = .pvMma k)
    (hstore : RescaleStore P L X t j cell q r) (hcta : ctaOf L t = ctaOf L g)
    (hblock : q.block ≤ d.i) :
    TcMma.WriteBefore L X (t, j) (g, i) := by
  have ht' := Frame.lt_of_get hX hstore.store.choose_spec
  have hrole : wgOf L t = 0 := RingRoleGeometry.of_trace hX ht' (hs t ht').machine hstore.state
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre hcta hrole
  let slot := rawSlot d.i
  let m := GemmRing.score L (ctaOf L g) slot
  let trace := (hs t ht').machine.produces (hX.thr t ht')
  obtain ⟨a, tag, ha, haCount, hbase⟩ :=
    PvProbabilitySource.actual_publication_before_pv hpre hX hs hi.choose_spec hd hsite lane
  rw [← hLane] at ha haCount hbase
  change arrivals m ((X.tr t).take a) = d.i / 2 at haCount
  have hjCount := (Wg0GemmTrace.composed_rescale_counts hpre trace hstore.state hstore.site slot).1
  rw [hcta] at hjCount
  change arrivals m ((X.tr t).take j) = (q.block + (1 - d.i % 2)) / 2 at hjCount
  have haj : j ≤ a := PTX.MbarRing.arrival_index_ge ha (by
    simp [arrivesOn, sourceArrive, m, slot])
    haCount (by rw [hjCount]; omega)
  have hja : j < a := by
    by_contra! h
    have he : j = a := by omega
    have hk := congrArg Event.kind (Option.some.inj (hstore.store.choose_spec.symm.trans
      (he ▸ ha)))
    cases hk
  obtain ⟨waitTag, hwait⟩ := Wg0RescaleHistory.wait_next hpre hX hs hstore.state
    hstore.site hstore.store (lt_of_le_of_lt (by omega) (PTX.len_of_get ha))
  have hwaitA : j + 1 < a := by
    by_contra! h
    have he : j + 1 = a := by omega
    rw [he] at hwait
    cases congrArg Event.kind (Option.some.inj (hwait.symm.trans ha))
  have hwaitBase : baseCausality L X (t, j + 1) (t, a) :=
    TcMma.baseCausality_of_tc_po hwait rfl hwaitA (PTX.len_of_get ha)
  exact TcMma.WriteBefore.of_waitSt hstore.store hwait rfl (by omega)
    (.inl (hwaitBase.trans hbase))

theorem earlier_rescale (_ht : Frame.Tracked (Machine.code P L) X) (hi : Issue L X g i d.i k)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) (hsite : d.site = .pvMma k)
    (hstore : RescaleStore P L X t j cell q r) (hcta : ctaOf L t = ctaOf L g)
    (hblock : q.block ≤ d.i) :
    TcMma.WriteBefore L X (t, j) (g, i) :=
  actual_earlier_rescale hpre hX hs hi hd hsite hstore hcta hblock

/-- A later rescale store observes the earlier PV via its block's QK commit. -/
theorem actual_later_rescale (hi : Issue L X g i d.i k)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) (hsite : d.site = .pvMma k)
    (hstore : RescaleStore P L X t j cell q r) (hcta : ctaOf L t = ctaOf L g)
    (hblock : d.i < q.block) :
    TcMma.DoneBefore L X (g, i) (t, j) := by
  have he := hstore.store.choose_spec
  have hh := Frame.lt_of_get hX he
  have hWg := RingRoleGeometry.of_trace hX hh (hs t hh).machine hstore.state
  have hCount := (Wg0GemmTrace.composed_rescale_counts hpre
    ((hs t hh).machine.produces (hX.thr t hh)) hstore.state hstore.site (rawSlot q.block)).2
  exact (PvProbabilitySource.prior_pv_read_finished_of_count (isB := false) (index := 0)
    hpre hX hs hi hd hsite hblock he hWg hcta.symm hCount.ge).2.1

theorem later_rescale (_ht : Frame.Tracked (Machine.code P L) X) (hi : Issue L X g i d.i k)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d))) (hsite : d.site = .pvMma k)
    (hstore : RescaleStore P L X t j cell q r) (hcta : ctaOf L t = ctaOf L g)
    (hblock : d.i < q.block) :
    TcMma.DoneBefore L X (g, i) (t, j) :=
  actual_later_rescale hpre hX hs hi hd hsite hstore hcta hblock
end

/-- A followed rescale store writes an FP32 word at every covered cell. -/
theorem rescale_store_f32 {t j : Nat} {q : Wg0.D} {k : Fin 4} {cell : TcMma.Cell}
    (hStore : RescaleStore P L X t j cell q k) :
    ∃ x : ℝ, TcMma.StoreValue L X (t, j) cell (.float .f32 x) := by
  obtain ⟨addr, words, shape, reg, hw, hReg, hCell⟩ := hStore.covers
  have hk := congrArg Event.kind (Option.some.inj
    (hw.choose_spec.symm.trans hStore.store.choose_spec))
  obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
  have hGet : (Wg0.rescaleStoreValues q)[reg]? = some (Wg0.rescaleValue q reg) := by
    rw [List.getElem?_eq_getElem hReg]
    simp [Wg0.rescaleStoreValues]
  exact ⟨_, _, _, _, reg, hStore.store, hGet, hCell⟩

/-- Each competing store either has a followed state or follows completion of the read. -/
def StoreHistory (P : Params) (L : Launch) (X : Execution) (reader : EvId)
    (cell : TcMma.Cell) : Prop :=
  ∀ {t j}, TcMma.StoreCell L X (t, j) cell →
    (∃ d k, RescaleStore P L X t j cell d k) ∨ TcMma.DoneBefore L X reader (t, j)

theorem store_history_of_tracking {reader : EvId} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    StoreHistory P L X reader cell := by
  intro t j hStore
  obtain ⟨addr, words, shape, reg, hGet, hReg, hCell⟩ := hStore
  exact .inl (followed_output_store hpre hX hs
    (ht t j (Frame.lt_of_get hX hGet.choose_spec)) hGet ⟨_, _, _, reg, hGet, hReg, hCell⟩)

/-- A consumer lane's followed prefix determines its own rescale stores. -/
theorem store_history_at_cut {g cut : Nat} {d : Wg0.D} {reader : EvId} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g cut = some (some (.wg0 d)))
    (hCta : cell.cta = ctaOf L g) (hLane : cell.lane = tidOf L g)
    (hCol : cell.column < 256)
    (hLate : ∀ {j e}, cut ≤ j → X.get (g, j) = some e → TcMma.DoneBefore L X reader (g, j)) :
    StoreHistory P L X reader cell := by
  intro t j hStore
  have hPhysical := hStore
  obtain ⟨_, _, _, _, hw, _, _⟩ := hPhysical
  have hGet := hw.choose_spec
  obtain ⟨hc, hClass⟩ := actual_output_writer hpre hX hs hCol (.inr (.inl hStore))
  rcases hClass with ⟨p, k, hp, hk, hi, _⟩ | ⟨k, words, ht, _, _, hTid, _⟩
  · cases congrArg Event.kind (Option.some.inj (hi.choose_spec.symm.trans hGet))
  have hOwner : t = g := by
    have hSameCta := hc.symm.trans hCta
    have hSameLane := hTid.symm.trans hLane
    change t / L.block = g / L.block at hSameCta
    rw [tidOf_eq hpre, tidOf_eq hpre] at hSameLane
    rw [hpre.block] at hSameCta
    omega
  subst t
  by_cases hb : cut ≤ j
  · exact .inr (hLate hb hGet)
  · obtain ⟨q, hq⟩ := FollowedPrefix.state_at hState (by omega : j ≤ cut)
    exact .inl (followed_output_store hpre hX hs (by rw [hq]; simp) ht hStore)

/-- Any actual release of a PV cell's allocation follows completion of its consumer. -/
theorem actual_source_live {g i : Nat} {d : Wg1Mma.D} {k : Fin 8}
    {source : EvId} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hi : Issue L X g i d.i k)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma k) (hcta : cell.cta = ctaOf L g) :
    TcMma.SourceLive L X source (g, i) cell := by
  intro c r hr hcover release hrelease
  obtain ⟨hown, tag, group, base, n, hget⟩ := ScoreLifetime.release_source hX hr hrelease
  obtain ⟨_, _, _, howner, _, _, _⟩ := hcover
  obtain ⟨h, j⟩ := release
  have hcta' : ctaOf L h = ctaOf L g := hown.trans (howner.symm.trans hcta)
  obtain ⟨issuer, hmma⟩ := GemmRing.exists_issuer (cta := ctaOf L h) hpre hX
    (fun n hn => (hs n hn).machine)
  have hIssuer := hmma g i d hcta'.symm hd (by rw [hsite]; simp)
  subst issuer
  have hHistory := MachineTracking.actual_dealloc_pv_history hpre hX hs hget
  obtain ⟨_, w, _, _, _, hBefore⟩ :=
    StageAfterPv.actual_operand_completed (isB := false) (index := 0)
      hpre hX hs hmma hcta'.symm (.inl ⟨_, _, _, _, hi⟩) hd (.inr ⟨k, hsite⟩)
      hget hHistory
  exact .inl (TcMma.CompletedBefore.of_mma hi hBefore)

section
variable {g i block : Nat} {k m n : Fin 8} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

private theorem previous_of_adjacent_with_orders (hprev : Issue L X g i block k)
    (hmid : Issue L X g (i + 1) block m) (hnext : Issue L X g (i + 2) block n)
    (hstate : Frame.stateAt (Machine.code P L) X g (i + 2) = some (some (.mma ⟨.pvMma n, block⟩)))
    (hhalf : k.val % 2 = n.val % 2) (hmhalf : m.val % 2 ≠ k.val % 2) (head : Fin 64) (col : Fin 256)
    (hstores : ∀ t j,
      TcMma.StoreCell L X (t, j)
        ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest k + col.val % 128⟩ →
      TcMma.WriteBefore L X (t, j) (g, i) ∨ TcMma.ReadBefore L X .acc (g, i + 2) (t, j))
    (hlive : TcMma.SourceLive L X (g, i) (g, i + 2)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest k + col.val % 128⟩) :
    TcMma.ReadSource L X .acc (g, i) (g, i + 2)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest k + col.val % 128⟩ := by
  let cell : TcMma.Cell := ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest k + col.val % 128⟩
  have hkHalf := Nat.mod_lt k.val (by decide : 0 < 2)
  have hcolMod := Nat.mod_lt col.val (by decide : 0 < 128)
  have hcol : cell.column < 256 := by
    change pvDest k + col.val % 128 < 256
    simp only [pvDest, tmemO, Nat.zero_add]
    omega
  have hcolHalf : cell.column / 128 = k.val % 2 := by
    change (pvDest k + col.val % 128) / 128 = k.val % 2
    simp only [pvDest, tmemO, Nat.zero_add]
    omega
  obtain ⟨issuer, his⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
    (fun t h => (hs t h).machine)
  have hi := his g (i + 2) _ rfl hstate (by simp)
  subst issuer
  have hwrite : X.MmaCell (g, i) cell :=
    ⟨_, _, _, _, head.val, col.val, hprev, pvWriteCell L g block k head col⟩
  refine ⟨fun h => by have hi := congrArg Prod.snd h; omega, .inl hwrite,
    .inl (pv_before hX hprev hnext (by omega) hhalf), ?_, hlive⟩
  rintro ⟨t, j⟩ hother
  obtain ⟨hcta, hrole⟩ := actual_output_writer hpre hX hs hcol hother
  rcases hrole with ⟨d, p, hd, hsite, hp, hpHalf⟩ | ⟨r, words, hSt, hCell, _, _, _⟩
  · have hissuer := his t j d hcta.symm hd (by rw [hsite]; simp)
    subst t
    have hpSame : k.val % 2 = p.val % 2 := hcolHalf.symm.trans hpHalf
    rcases Nat.lt_trichotomy j i with hlt | rfl | hlt
    · exact .inr (.inl (.inl (pv_before hX hp hprev hlt hpSame.symm)))
    · exact .inl rfl
    · by_cases hj : j = i + 1
      · subst j
        have h := congrArg Event.kind (Option.some.inj
          (hp.choose_spec.symm.trans hmid.choose_spec))
        have hdest := (TcKind.mma.inj (Kind.tc.inj h)).1
        change tmemO + 128 * (p.val % 2) = tmemO + 128 * (m.val % 2) at hdest
        exact (hmhalf (by omega)).elim
      · refine .inr (.inr ?_)
        rcases Nat.eq_or_lt_of_le (show i + 2 ≤ j by omega) with rfl | hlt
        · exact .inl rfl
        · obtain hdone | hpipe := pv_before hX hnext hp hlt (hhalf.symm.trans hpSame)
          · exact .inr (.inl hdone)
          · exact .inr (.inr hpipe)
  · exact .inr (hstores t j hCell)

/-- The previous PV issue of the half supplies every cell of the next accumulating issue. -/
theorem actual_previous_of_adjacent (hprev : Issue L X g i block k)
    (hmid : Issue L X g (i + 1) block m) (hnext : Issue L X g (i + 2) block n)
    (hPrevState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩)))
    (hNextState : Frame.stateAt (Machine.code P L) X g (i + 2) =
      some (some (.mma ⟨.pvMma n, block⟩))) (hhalf : k.val % 2 = n.val % 2)
    (hmhalf : m.val % 2 ≠ k.val % 2) (head : Fin 64) (col : Fin 256)
    (hHistory : StoreHistory P L X (g, i + 2)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest k + col.val % 128⟩) :
    TcMma.ReadSource L X .acc (g, i) (g, i + 2)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest k + col.val % 128⟩ := by
  refine previous_of_adjacent_with_orders hpre hX hs hprev hmid hnext hNextState hhalf hmhalf
    head col ?_ (actual_source_live hpre hX hs hnext hNextState rfl rfl)
  intro t j hCell
  rcases hHistory hCell with ⟨d, r, hstore⟩ | hLate
  swap
  · exact .inr (.inr (.inl hLate))
  have hcta : ctaOf L t = ctaOf L g := by
    obtain ⟨_, _, _, _, _, _, hcell⟩ := hstore.covers
    exact (congrArg TcMma.Cell.cta hcell).symm
  by_cases hb : d.block ≤ block
  · exact .inl (actual_earlier_rescale hpre hX hs hprev hPrevState rfl hstore hcta hb)
  · exact .inr (.inr (.inl (actual_later_rescale hpre hX hs hnext hNextState rfl hstore hcta
      (Nat.lt_of_not_ge hb))))

theorem previous_of_adjacent (ht : Frame.Tracked (Machine.code P L) X)
    (hprev : Issue L X g i block k) (hmid : Issue L X g (i + 1) block m)
    (hnext : Issue L X g (i + 2) block n)
    (hPrevState : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩)))
    (hNextState : Frame.stateAt (Machine.code P L) X g (i + 2) =
      some (some (.mma ⟨.pvMma n, block⟩))) (hhalf : k.val % 2 = n.val % 2)
    (hmhalf : m.val % 2 ≠ k.val % 2) (head : Fin 64) (col : Fin 256) :
    TcMma.ReadSource L X .acc (g, i) (g, i + 2)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), pvDest k + col.val % 128⟩ :=
  actual_previous_of_adjacent hpre hX hs hprev hmid hnext hPrevState hNextState hhalf hmhalf
    head col (store_history_of_tracking hpre hX hs ht)
end

/-- An actual PV commit identifies the eight issues and every same-half accumulator source. -/
theorem of_commit {g commit : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, commit) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g commit = some (some (.mma d)))
    (hsite : d.site = .pvCommit) :
    ∃ visit : Fin 8 → Nat,
      (∀ k, visit k + (8 - k.val) = commit ∧
        Frame.stateAt (Machine.code P L) X g (visit k) =
          some (some (.mma ⟨.pvMma k, d.i⟩)) ∧ Issue L X g (visit k) d.i k) ∧
      ∀ (i : Nat) (hi : i + 1 < 4) (half : Fin 2) (head : Fin 64) (col : Fin 256),
        TcMma.ReadSource L X .acc (g, visit (pvHalfIssue half ⟨i, by omega⟩))
          (g, visit (pvHalfIssue half ⟨i + 1, hi⟩))
          ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩ := by
  choose visit hvisit using fun k => PvIssueHistory.pv_issue_of_commit hpre hX hs he hd hsite k
  refine ⟨visit, hvisit, ?_⟩
  intro i hi half head col
  let prev := pvHalfIssue half ⟨i, by omega⟩
  let next := pvHalfIssue half ⟨i + 1, hi⟩
  have hHalf := half.isLt
  let mid : Fin 8 := ⟨prev.val + 1, by change 2 * i + half.val + 1 < 8; omega⟩
  change TcMma.ReadSource L X .acc (g, visit prev) (g, visit next) _
  obtain ⟨hPrevIdx, hpState, hp⟩ := hvisit prev
  obtain ⟨hMidIdx, _, hm⟩ := hvisit mid
  obtain ⟨hNextIdx, hnState, hn⟩ := hvisit next
  have hMid : visit mid = visit prev + 1 := by
    change visit mid + (8 - (2 * i + half.val + 1)) = commit at hMidIdx
    change visit prev + (8 - (2 * i + half.val)) = commit at hPrevIdx
    omega
  have hNext : visit next = visit prev + 2 := by
    change visit next + (8 - (2 * (i + 1) + half.val)) = commit at hNextIdx
    change visit prev + (8 - (2 * i + half.val)) = commit at hPrevIdx
    omega
  rw [hMid] at hm
  rw [hNext] at hn hnState ⊢
  have hpHalf : prev.val % 2 = half.val := by
    change (2 * i + half.val) % 2 = half.val
    omega
  have hnHalf : next.val % 2 = half.val := by
    change (2 * (i + 1) + half.val) % 2 = half.val
    omega
  have hmHalf : mid.val % 2 ≠ prev.val % 2 := by
    change (2 * i + half.val + 1) % 2 ≠ (2 * i + half.val) % 2
    omega
  simpa only [pvDest, hpHalf] using previous_of_adjacent hpre hX hs ht hp hm hn hpState hnState
    (hpHalf.trans hnHalf.symm) hmHalf head col

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvAccumulatorSource

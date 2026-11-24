-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaCompletionShape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsOperands
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantOperandWriter
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantGenerationOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.PvProbabilityConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Tcgen05.TcMmaACell

public section

/-! # Visible byte sources for an issued QK or PV instruction -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow AsyncCopy MmaSources MmaDataTrace Protocol Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

private theorem kv_operand_source {g i dest index : Nat} {op : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {d : Wg1Mma.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) dest op acc mask)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : (∃ k, d.site = .qkMma k) ∨ ∃ k, d.site = .pvMma k)
    (slot : Fin 64) (feature : Fin 512) (b : Fin 2)
    (hFoot : X.MmaFootprint (g, i) true index (kvOperandLoc L (ctaOf L g) d.i slot feature b)) :
    let l := kvOperandLoc L (ctaOf L g) d.i slot feature b
    ∃ src : ByteSource X, src.loc = l ∧ ∀ w a bs, X.MemWrites w a bs → a.Covers l →
      w = src.ref ∨ ByteCausality L X l w src.ref ∨
        ByteCausality L X l (.async (g, i) (.mmaRead true index)) w := by
  dsimp only
  let cta := ctaOf L g
  let l := kvOperandLoc L cta d.i slot feature b
  let sound := fun h hh => (hs h hh).machine
  have hOp : X.TcAsync (g, i) := .inl ⟨_, _, _, _, hi⟩
  have hReady : Wg1MmaGemmTrace.completed .dequant d.site = true := by
    rcases hSite with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
  have hNe : d.site ≠ .elect := by
    rcases hSite with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := cta) hpre hX sound
  have hId := hIssuer g i d rfl hd hNe
  subst issuer
  obtain ⟨j, curr, fp, data, hCurr, hBlock, ⟨r, s, hCurrent, hRow, hStep⟩, hWrite,
    hCover, _, _⟩ :=
    dequant_operand_source hpre hX hs hIssuer rfl hi.choose_spec hd hReady slot feature b
  let writer := GemmRing.producer L cta (dequantLane slot feature)
  refine ⟨⟨l, .thread (writer, j), fp, data, .inl hWrite, hCover⟩, rfl, ?_⟩
  intro other a bs hw ha
  rcases Wg2.raw_read_competing_kinds hX hw ha (show l.space = .shared from rfl) with
    ⟨⟨w, t⟩, rfl, hw⟩ | ⟨src, x, y, k, rfl⟩
  · obtain hw | ⟨_, hrmw⟩ := hw
    swap
    · exact (GlobalWrites.no_rmw hX hrmw).elim
    rcases kv_ordinary_writer hpre hX hs ht hw ha with
      ⟨hThread, q, r', s', hState, hStore, hRow', hStep', hSlot⟩ |
      ⟨_, hCta, q, tile, chunk, hState, hStage⟩
    · change w = writer at hThread
      subst w
      rcases lt_trichotomy q.block d.i with hEarly | hEqual | hLate
      · have hg := Frame.lt_of_get hX hw.choose_spec
        exact .inr (.inl (GemmRing.dequant_generation_before hpre hX (sound _ hg) hState hCurr
          ⟨r', s', hStore⟩ ⟨r, s, hCurrent⟩ hw hWrite ha hCover
          (hSlot.trans (congrArg (· % 2) hBlock.symm)) (hBlock.symm ▸ hEarly)))
      · obtain rfl : r' = r := Fin.ext (hRow'.trans hRow.symm)
        obtain rfl : s' = s := Fin.ext (hStep'.trans hStep.symm)
        have hEq := Wg2StoreHistory.store_index_unique hState hCurr
          (PTX.len_of_get hw.choose_spec).le (PTX.len_of_get hWrite.choose_spec).le
          hStore hCurrent (hEqual.trans hBlock.symm)
        change t = j at hEq
        exact .inl (by rw [hEq])
      · obtain ⟨_, wait, hLt, hFinish, hBase⟩ := DequantAfterPv.earlier_operand_completed
          (isB := true) (index := index) hpre hX sound hIssuer rfl hOp hd hSite hLate hSlot.symm
          hw.choose_spec hState ⟨r', s', hStore⟩
        exact .inr (.inr
          (completed_mma_source_before_store hi hFoot hFinish rfl hLt hBase rfl hw ha))
    · obtain ⟨stageIssuer, hStageIssuer⟩ :=
        GemmRing.exists_issuer (cta := ctaOf L w) hpre hX sound
      obtain ⟨_, wait, hLt, hFinish, hBase⟩ := StageAfterPv.operand_completed
        (isB := true) (index := index) hpre hX hs ht hStageIssuer hCta.symm hOp hd hSite
        hw.choose_spec hState hStage
      exact .inr (.inr
        (completed_mma_source_before_store hi hFoot hFinish rfl hLt hBase rfl hw ha))
  · exact .inr (.inl (kv_tensor_writer_earlier hpre hX hs hCurr hCurrent hWrite hCover hw ha))

/-- The reads of every issued QK and PV instruction have covering byte sources. -/
theorem mma_operand_sources (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    OperandByteSourcesT L X := by
  let sound := fun h hh => (hs h hh).machine
  refine ⟨?_, ?_⟩
  · rintro ⟨g, i⟩ ⟨h, j⟩ ⟨_, _, _, _, hi⟩ ⟨_, _, _, _, hj⟩ hWarp
    obtain ⟨_, hSpec⟩ := MmaAccessWindow.mma_spec hpre hX hs ht hi
    obtain ⟨_, hSpec'⟩ := MmaAccessWindow.mma_spec hpre hX hs ht hj
    obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX sound
    have hCta : ctaOf L h = ctaOf L g := hWarp.1.2.2.symm
    have hg : g = issuer := by
      rcases hSpec with ⟨block, k, _, _, _, hState⟩ | ⟨block, k, _, _, _, hState⟩ <;>
        exact hIssuer g i _ rfl hState (by simp)
    have hh : h = issuer := by
      rcases hSpec' with ⟨block, k, _, _, _, hState⟩ | ⟨block, k, _, _, _, hState⟩ <;>
        exact hIssuer h j _ hCta hState (by simp)
    exact hg.trans hh.symm
  · intro i dest sp acc mask hi _
    refine ⟨(Safety.mma_issue_shape hpre hX hs ht hi).2.1, ?_⟩
    intro isB index l hf
    obtain ⟨g, i⟩ := i
    rcases hf with ⟨_, _, _, _, hIssue, hLoc⟩ | ⟨cp, _, _, hCopy, _, _, _, _⟩
    · obtain ⟨d, hd, hSite, ⟨rfl, slot, feature, b, rfl⟩ | ⟨rfl, _⟩⟩ :=
        Safety.AsyncSharedConflicts.operand_mma_geometry hpre hX hs ht hIssue hLoc
      · exact kv_operand_source hpre hX hs ht hi hd hSite slot feature b
          (.inl ⟨_, _, _, _, hIssue, hLoc⟩)
      · obtain ⟨rfl, ⟨block, k, rfl, rfl, rfl, _⟩ | ⟨block, issue, rfl, rfl, rfl, hState⟩⟩ :=
          MmaAccessWindow.mma_spec hpre hX hs ht hIssue
        · change (qkOperands L g block k).byteLoc .a index = some l at hLoc
          rw [TcMma.byteLoc_a_tmem (s := qkOperands L g block k) rfl index] at hLoc
          cases hLoc
        · change (pvOperands L g block issue).byteLoc .a index = some l at hLoc
          have hn := TcMma.OperandSpec.byteLoc_index_lt (s := pvOperands L g block issue)
            (op := .a) hLoc
          norm_num [pvOperands, Wg1Mma.pvDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
            TcMma.Kind.k, TcMma.Kind.width] at hn
          obtain ⟨row, k, b, rfl⟩ := MmaAccessWindow.operand_slot (rows := 128) hn
          rw [pvProbabilityByte L g block issue row k b] at hLoc
          obtain rfl := (Option.some.inj hLoc).symm
          obtain ⟨src, hl, _, hOrder⟩ :=
            Safety.PvProbabilityConflicts.operand_source hpre hX hs ht hIssue hState rfl row k b
          refine ⟨src, hl, fun w a bs hw hc => ?_⟩
          rcases hOrder w a bs hw hc with ⟨e, f, rfl, hf, hBase⟩ | hEq | hLater
          · exact .inr (.inl (hf.symm ▸ .direct (modelCausality.of_base L hBase)))
          · exact .inl hEq
          · exact .inr (.inr hLater)
    · have hKind := congrArg Event.kind (Option.some.inj (hi.choose_spec.symm.trans
        hCopy.choose_spec))
      cases hKind

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

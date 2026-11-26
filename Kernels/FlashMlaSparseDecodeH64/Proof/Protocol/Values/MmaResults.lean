-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.AccSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.SourceDone
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Result.Gemm
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.RescaleStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists
import Lemmas.Tcgen05.AccumulateStored
import Lemmas.Tcgen05.ValuesByTcOrder
import Lemmas.Tcgen05.TcFence
import Lemmas.Order.OrderBaseCausality
import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

/-! # Every completed MMA has its result, by induction on the tcgen05 order

A completed MMA read its operands, so its ideal arithmetic gives a single-precision number at every
cell it writes when its operand elements decode to numbers (`MmaElements`) and, when it accumulates,
its old value does. The old value is the result of an earlier done MMA, or a store's word.
`tmem_values` proves both claims together, by induction on the tcgen05 order (`TcStep` paths,
well founded: `Frame.values_by_tcStep`): a store's word is a number when the words its lane loaded
before are (`RescaleStep`, `Iface/RescaleStep.lean`), and each of those is the word of its read
source, a done MMA (`ld_src_kind`) or a store, both ordered before the load, so before the MMA. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

/-- **The operand elements of a completed MMA are numbers**: every contraction element of the A row
(the datapath row of the output row) and the B column of a result cell decodes (`valFloat` of the
rebuilt bytes). -/
def MmaElemAt (X : Execution) (i : EvId) : Prop :=
  ∀ d s acc mask ops row col cell, X.MmaIssue i d s acc mask → X.async.mmaDone i = true →
    X.async.mmaOperands i = some ops → TcMma.writeCell s d mask row col = some cell →
    (∀ k < 16, ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
      (TcMma.operandRow s.descriptor row col) k = .ok x) ∧
    (∀ k < 16, ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok y)

/-- **The operand elements of every completed MMA are numbers.** -/
def MmaElements (X : Execution) : Prop := ∀ i, MmaElemAt X i

/-- **The operand elements of the QK MMAs** (the MMAs into column 400) are numbers. -/
def QkElements (X : Execution) : Prop :=
  ∀ g i pc s acc mask, X.get (g, i) = some ⟨pc, .tc (.mma 400 s acc mask)⟩ → MmaElemAt X (g, i)

theorem MmaElements.qk {X : Execution} (h : MmaElements X) : QkElements X :=
  fun g i _ _ _ _ _ => h (g, i)

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The MMA descriptors of the two instruction words are `kind::f16` bf16 with an f32 D and no
operand negation. -/
theorem desc_bf16 {i : Nat} (hi : i = TmemRow.qkIdesc ∨ i = TmemRow.pvIdesc)
    {d : TcMma.Descriptor} (h : TcMma.decode .one true .f16 i = some d) :
    d.kind = .f16 .bf16 .f32 ∧ d.negateA = false ∧ d.negateB = false := by
  rcases hi with rfl | rfl
  · have h' : TcMma.decode .one true .f16 69207184 = some d := h
    simp only [TcMma.decode, TcMma.decodeKind] at h'
    split at h'
    · simp_all
    · simp_all
      obtain ⟨-, rfl⟩ := h'
      exact ⟨rfl, rfl, rfl⟩
  · have h' : TcMma.decode .one true .f16 71369872 = some d := h
    simp only [TcMma.decode, TcMma.decodeKind] at h'
    split at h'
    · simp_all
    · simp_all
      obtain ⟨-, rfl⟩ := h'
      exact ⟨rfl, rfl, rfl⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hT : TmemRows P L X)
  (hO : MmaOne L X)
include hp hX hT hO

/-- **The source MMA of an accumulator read is of the same lane and earlier**: ordered before the
read, so it is not a later event of the lane (`tcStep_acyclic`). -/
theorem acc_mma_prev (hG : SyncGuarded L kernel X) {i src : EvId} {cell : TcMma.Cell}
    (hr : X.MmaReadCell i cell) (hs : TcMma.ReadSource L X .acc src i cell)
    (hm : X.MmaCell src cell) : src.1 = i.1 ∧ src.2 < i.2 := by
  have hw := acc_write hX hT hr
  obtain ⟨d0, s0, a0, m0, row0, col0, ⟨pcx, hxg⟩, -⟩ := id hm
  obtain ⟨d, s, mask, row, col, ⟨pci, hig⟩, -⟩ := id hr
  obtain ⟨hon, hct, -⟩ := mma_class hp hX hT hxg hs.2.1
  obtain ⟨hon', hct', -⟩ := mma_class hp hX hT hig hw
  have hthr : src.1 = i.1 := mma_same hO hxg hig hon hon' (hct.symm.trans hct')
  refine ⟨hthr, ?_⟩
  rcases Nat.lt_trichotomy src.2 i.2 with h | h | h
  · exact h
  · exact absurd (Prod.ext hthr h) hs.1
  · have hlen : src.2 < (X.tr src.1).length := (List.getElem?_eq_some_iff.mp hxg).1
    exact (TcMma.tcStep_acyclic hX hG _ (hs.2.2.1.tcStep.tail (.inl (.single (.inl
      (po_of_not_access (e := i) (f := src) hthr.symm h hlen (by rw [hxg]; rfl))))))).elim

end

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
  (hG : SyncGuarded L kernel X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (hR : MbarRows P L X) (hI : InitRows L X)
  (hB : Bar0Rows L X) (hnu : ¬ HasUb X) (hN : DequantInputs L X) (hBr : BarRows P L X)
include hp hX hFw hT hO hPS hG ht hmd hR hI hB hN hBr

/-- **The words of an event**: every cell of a done MMA has a single-precision result, and every
word a store writes is a number. -/
def TmClaim (L : Launch) (X : Execution) (w : EvId) : Prop :=
  (∀ d s acc mask row col cell, X.MmaIssue w d s acc mask → X.async.mmaDone w = true →
      TcMma.writeCell s d mask row col = some cell →
      ∃ r, TcMma.Result L Assumptions.all X w cell (.float .f32 r)) ∧
    (∀ cell old, TcMma.StoreValue L X w cell old → ∃ r : ℝ, OkF old r)

/-- **One step of the induction on the tcgen05 order**: the words of the event `w` are numbers when
those of the events with a `TcStep` path to it are (`ih`), the operand elements of `w` decode when
it is an MMA (`hEw`), and a store's word is a number when the words its lane loaded before are
(`hSw`, `RescaleStepAt`). The old value of an accumulating MMA is the result of an earlier done MMA
or a store's word, both before `w`. -/
theorem tm_step {w : EvId}
    (ih : ∀ j e', X.get j = some e' → Relation.TransGen (TcMma.TcStep L X) j w → TmClaim L X j)
    (hEw : MmaElemAt X w) (hSw : RescaleStepAt L X w) : TmClaim L X w := by

  refine ⟨?_, ?_⟩
  · obtain ⟨g, k⟩ := w
    intro d s acc mask row col cell hi hd hpos
    have hc : X.MmaCell (g, k) cell := ⟨_, _, _, _, _, _, hi, hpos⟩
    obtain ⟨ops, hops⟩ : ∃ ops, X.async.mmaOperands (g, k) = some ops := by
      have hst := hX.tma.2.1.2 _ hd
      cases h : X.async.mmaOperands (g, k) with
      | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
      | some ops => exact ⟨ops, rfl⟩
    obtain ⟨hv, hla, hlb⟩ := hX.mma_observation_shape hi hops
    obtain ⟨pc, he⟩ := id hi
    obtain ⟨-, -, -, aT, idc, hcol, hmo⟩ := mma_class hp hX hT he (.inl hc)
    obtain ⟨hk, hna, hnb⟩ : s.descriptor.kind = .f16 .bf16 .f32 ∧ s.descriptor.negateA = false ∧
        s.descriptor.negateB = false := by
      obtain ⟨-, hdec, -⟩ := hmo
      refine desc_bf16 ?_ hdec
      rcases hcol with ⟨h1, -⟩ | ⟨h1, -⟩
      exacts [.inl h1, .inr h1]
    obtain ⟨hrow, hcl⟩ := TcMma.resultCell_rowcol (TcMma.writeCell_resultCell hpos)
    obtain ⟨hAe, hBe⟩ := hEw d s acc mask ops row col cell hi hd hops hpos
    choose! x hx using hAe
    choose! y hy using hBe
    have heval : ∀ {old : Option Value} {prev : ℝ},
        Assumption.idealMmaAccumulator .f32 acc old = .ok prev →
        ∃ r, TcMma.eval Assumptions.all s.descriptor acc ops.a ops.b old row col =
          .ok (.float .f32 r) := fun hprev =>
      ⟨_, Result.bf16Mma_sum hk hv hna hnb (by rw [hla]; simp [TcMma.Operand.bytes,
        TcMma.Operand.rows, TcMma.Operand.extent]) (by rw [hlb]; simp [TcMma.Operand.bytes,
        TcMma.Operand.rows, TcMma.Operand.extent]) hrow hcl hx hy hprev⟩
    cases acc
    · obtain ⟨r, hr⟩ := heval (old := none) (prev := 0) rfl
      exact ⟨r, .overwrite hi hpos hops hr⟩
    have hrd : X.MmaReadCell (g, k) cell :=
      ⟨d, s, mask, row, col, hi, TcMma.writeCell_resultCell hpos⟩
    obtain ⟨src, hsrc⟩ := acc_source hp hX hFw hT hO hPS hG ht hmd hrd
    have hdep : Relation.TransGen (TcMma.TcStep L X) src (g, k) := hsrc.2.2.1.tcStep
    rcases hsrc.2.1 with hm | ⟨a, vals, sh, j, hst, hj, hceq⟩ | hcp | ⟨sp, ⟨pc', he'⟩, -⟩
    · have hds := acc_mma_done hp hX hT hO hG hd hrd hsrc hm
      obtain ⟨dK, sK, aK, mK, rowK, colK, hiK, hposK⟩ := id hm
      obtain ⟨pcK, heK⟩ := id hiK
      obtain ⟨r', hr'⟩ := (ih src _ heK hdep).1 dK sK aK mK rowK colK cell hiK hds hposK
      obtain ⟨r, hr⟩ := heval (old := some (.float .f32 r')) (prev := r') rfl
      exact ⟨r, .accumulate hi hpos hops hr' hsrc hr⟩
    · have hsv : TcMma.StoreValue L X src cell vals[j] :=
        ⟨a, vals, sh, j, hst, List.getElem?_eq_getElem hj, hceq⟩
      obtain ⟨pcS, heS⟩ := id hst
      obtain ⟨r', hr'⟩ := (ih src _ heS hdep).2 cell vals[j] hsv
      obtain ⟨r, hr⟩ := heval (old := some vals[j]) (prev := r') hr'.2
      exact ⟨r, .accumulateStored hi hpos hops hsv hsrc hr⟩
    · exact (acc_no_cp hp hX hT hrd hcp).elim
    · exact absurd rfl (no_shift_of_code hX code_noShift he' sp)
  · intro cell old hsv
    obtain ⟨e', a, vals, sh, hld, hg', hlt, himp⟩ := hSw cell old hsv
    obtain ⟨address, valsS, shapeS, jS, hstS, -, -⟩ := id hsv
    obtain ⟨pcS, hgetS⟩ := id hstS
    refine himp fun v hv => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have hlc : TcMma.LoadCell L X e' j (tcDataCell L e'.1 sh a j) := ⟨a, vals, sh, hld, hj, rfl⟩
    obtain ⟨src, hs⟩ := ld_source hp hX hFw hR hI hB hN hBr hPS hG ht hlc
      (ld_write hp hX hFw hR hI hB hN hld hj rfl)
    have hpo : po X e' w := po_of_not_access hg' hlt (len_of_get hgetS)
      (by rw [hgetS]; rfl)
    have hdep : Relation.TransGen (TcMma.TcStep L X) src w :=
      hs.2.2.1.tcStep.tail (.inl (.single (.inl hpo)))
    have hword : ∀ {value : Value} {r : ℝ}, OkF value r → TcMma.Wrote L Assumptions.all X src
        (tcDataCell L e'.1 sh a j) value → ∃ r', OkF vals[j] r' := by
      intro value r hok hw
      obtain ⟨word, hwd, hcont⟩ := TcMma.load_word hX.tcRead.1 hld hlc hs hw
      have hwj : vals[j] = word := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hwd)
      rcases hcont with ⟨-, rfl⟩ | ⟨h2, -⟩
      · exact ⟨r, hwj ▸ hok⟩
      · exact absurd hok.1.1 (by omega)
    rcases ld_src_kind hp hX hFw hld hj rfl hs with ⟨hm, hds⟩ | hstc
    · obtain ⟨dK, sK, aK, mK, rowK, colK, hiK, hposK⟩ := id hm
      obtain ⟨pcK, heK⟩ := id hiK
      obtain ⟨r', hr'⟩ := (ih src _ heK hdep).1 dK sK aK mK rowK colK _ hiK hds hposK
      exact hword (okF_float r') (.inl hr')
    · obtain ⟨a', vals', sh', j', hst', hjl, hceq⟩ := id hstc
      have hsv' : TcMma.StoreValue L X src (tcDataCell L e'.1 sh a j) vals'[j'] :=
        ⟨a', vals', sh', j', hst', List.getElem?_eq_getElem hjl, hceq⟩
      obtain ⟨pcT, heT⟩ := id hst'
      obtain ⟨r', hr'⟩ := (ih src _ heT hdep).2 _ _ hsv'
      exact hword hr' (.inr (.inl hsv'))

/-- **Every Tensor Memory word of the MMA lane is a number**, by induction on the tcgen05 order,
given the operand elements and the rescale step at every event. -/
theorem tmem_values (hE : MmaElements X) (hS : RescaleStep L X) :
    ∀ w e, X.get w = some e → TmClaim L X w :=
  Frame.values_by_tcStep hX hG _ fun w _ _ ih => tm_step hp hX hFw hT hO hPS hG ht hmd hR hI
    hB hN hBr ih (hE w) (hS w)

/-- **`TcMma.CompletedValues`**: the unmasked result of a completed MMA is defined. -/
theorem completed_values (hE : MmaElements X) (hS : RescaleStep L X) {i : EvId} {d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} (_hi : X.MmaIssue i d s acc mask) :
    TcMma.CompletedValues L Assumptions.all X i := by
  intro hd cell ⟨d', s', acc', mask', row, col, hi', hpos⟩
  obtain ⟨pc, he⟩ := id hi'
  obtain ⟨r, h⟩ := (tmem_values hp hX hFw hT hO hPS hG ht hmd hR hI hB hN hBr hE hS i _
    he).1 d' s' acc' mask' row col cell hi' hd hpos
  exact ⟨_, h⟩

end

end TmRace
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.ASource
import Lemmas.Tcgen05.TcMmaSource
import Lemmas.Tcgen05.TcMmaIdealEval
import Lemmas.Tcgen05.TcFence
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # The word of a read source exists once the completed MMAs have their results

A read source `source` of a load or an accumulator read is a Tensor Memory write ordered before
the read (`WriteBefore`). The word it left (`TcMma.Wrote`) exists when

* it is an MMA that is done: `TcMma.CompletedValues` of that MMA (the hypothesis `hCV`);
* it is a store: the register the store wrote to the cell (`StoreValue` is the store's own list);
* it is a copy that is done: `CpDefined` (`cp_defined`);
* the kernel fires no shift (`no_shift_of_code`).

`wrote_of_done` is that case split. An ordered source is done: by the observed commit
(`DoneBefore.done`), or, for an accumulator read, by the D to D pipeline of the lane
(`CompletionClosed`: the source is an earlier MMA of the same accumulator and the same cells,
`acc_source_done`). A load's source is never in a pipelined pair: the pairs start at an MMA. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Two readings of one event as `tcgen05` instructions are the same instruction. -/
theorem get_tc_inj {e : EvId} {pc pc' : Nat} {k k' : TcKind}
    (h : X.get e = some ⟨pc, .tc k⟩) (h' : X.get e = some ⟨pc', .tc k'⟩) : k = k' := by
  rw [h] at h'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq] at h'
  exact h'.2

/-- **The case split**: a Tensor Memory write has a word when a done MMA or copy is completed. -/
theorem wrote_of_done (hX : Consistent L kernel Assumptions.all m X)
    (hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      TcMma.CompletedValues L Assumptions.all X i)
    (hD : CpDefined X) {src : EvId} {cell : TcMma.Cell} (hw : TcMma.TmemWrite L X src cell)
    (hd : (X.MmaCell src cell ∨ TcMma.CpCell X src cell) → X.async.mmaDone src = true) :
    ∃ value, TcMma.Wrote L Assumptions.all X src cell value := by
  rcases hw with hm | ⟨a, vals, sh, j, hst, hj, rfl⟩ | hc | ⟨sp, ⟨pc, he⟩, -⟩
  · obtain ⟨d, s, acc, mask, row, col, hi, hc⟩ := id hm
    obtain ⟨v, hv⟩ := hCV src d s acc mask hi (hd (.inl hm)) cell hm
    exact ⟨v, .inl hv⟩
  · exact ⟨vals[j], .inr (.inl ⟨a, vals, sh, j, hst, List.getElem?_eq_getElem hj, rfl⟩)⟩
  · obtain ⟨c, cta, index, lane, hi, -⟩ := id hc
    obtain ⟨v, hv⟩ := hD src c cell hi (hd (.inr hc)) hc
    exact ⟨v, .inr (.inr (.inl hv))⟩
  · exact absurd rfl (no_shift_of_code hX code_noShift he sp)

/-- A write of the issuing kind is not of another kind: an MMA or a copy is no store. -/
private theorem write_not_st {src : EvId} {cell : TcMma.Cell} {a : Nat} {vals : List Value}
    {sh : TcShape} (hst : X.TSt src a vals sh)
    (hmc : X.MmaCell src cell ∨ TcMma.CpCell X src cell) : False := by
  obtain ⟨pc, h⟩ := hst
  rcases hmc with ⟨d, s, acc, mask, row, col, ⟨pc', h'⟩, -⟩ | ⟨c, cta, index, lane, ⟨pc', h'⟩, -⟩
  · cases get_tc_inj h h'
  · cases get_tc_inj h h'

/-- **A load's source is done** when it is an MMA or a copy: its order before the load is an
observed commit. -/
theorem ld_wrote (hX : Consistent L kernel Assumptions.all m X)
    (hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      TcMma.CompletedValues L Assumptions.all X i)
    (hD : CpDefined X) {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (hld : X.TLd e a vals sh) {src : EvId} {cell : TcMma.Cell}
    (hs : TcMma.ReadSource L X .ld src e cell) :
    ∃ value, TcMma.Wrote L Assumptions.all X src cell value := by
  refine wrote_of_done hX hCV hD hs.2.1 fun hmc => ?_
  obtain ⟨pcl, hl⟩ := hld
  rcases hs.2.2.1 with (hdn | hpl) | ⟨⟨a', vals', sh', hst⟩, -⟩ | ⟨-, -, c, d, s, acc, mask, -, -,
      ⟨pc, hy⟩, -⟩
  · exact hdn.done hX.tcCommit
  · obtain ⟨-, -, d, s, acc, mask, d', s', acc', mask', -, ⟨pc, hy⟩, -⟩ := hpl
    cases get_tc_inj hl hy
  · exact (write_not_st hst hmc).elim
  · cases get_tc_inj hl hy

/-- **The column of a cell an MMA writes**, and its descriptor row: zero output masks, and the
operand words of the QK MMA (columns `[400, 464)`) or of the PV MMA (columns below 256). -/
theorem mma_class (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) {x : EvId} {pc d : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : TcMma.Cell}
    (he : X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩) (hw : TcMma.TmemWrite L X x cell) :
    MmaOn L x.1 pc ∧ cell.cta = x.1 / L.block ∧ mask = [0, 0, 0, 0] ∧
      ∃ aT idc, ((idc = TmemRow.qkIdesc ∧ 400 ≤ cell.column ∧
      cell.column < 464) ∨ (idc = TmemRow.pvIdesc ∧ cell.column < 256)) ∧
      TmemRow.MmaOps L x.1 s aT idc := by
  obtain ⟨hcta, hc⟩ := writer_cases hp hX hT hw
  rcases hc with ⟨k, ⟨pc', s', hk, he', hon, hops⟩, h1, h2⟩ |
    ⟨b, ⟨pc', s', acc', he', hon, hops⟩, hb, hb2, h1, h2⟩ | ⟨k, ⟨pc', c, hk, he', -⟩, -, -⟩ |
    ⟨⟨pc', a, vals, he', -⟩, -, -⟩
  · rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨rfl, -, rfl, -, rfl⟩ := he'
    exact ⟨hon, hcta, rfl, _, _, .inl ⟨rfl, h1, h2⟩, hops⟩
  · rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨rfl, -, rfl, -, rfl⟩ := he'
    exact ⟨hon, hcta, rfl, _, _, .inr ⟨rfl, by omega⟩, hops⟩
  · cases get_tc_inj he he'
  · cases get_tc_inj he he'

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hT : TmemRows P L X)
include hp hX hT

/-- **No copy writes the cell an MMA accumulates**: the copies write columns `[256, 392)`. -/
theorem acc_no_cp {i src : EvId} {cell : TcMma.Cell} (hr : X.MmaReadCell i cell)
    (hcp : TcMma.CpCell X src cell) : False := by
  have hw := acc_write hX hT hr
  obtain ⟨d, s, mask, row, col, ⟨pc, he⟩, hc⟩ := hr
  obtain ⟨-, -, -, aT, idc, hcol, -⟩ := mma_class hp hX hT he hw
  obtain ⟨-, hq⟩ := writer_cases hp hX hT (.inr (.inr (.inl hcp)))
  obtain ⟨c, cta, index, lane, ⟨pcc, hcg⟩, -⟩ := id hcp
  rcases hq with ⟨k, ⟨pc', s', hk, he', -⟩, -⟩ | ⟨b, ⟨pc', s', acc', he', -⟩, -⟩ |
    ⟨k, ⟨pc', c', hk, he', -⟩, h1, h2⟩ | ⟨⟨pc', a, vals, he', -⟩, -, -⟩
  · cases get_tc_inj hcg he'
  · cases get_tc_inj hcg he'
  · omega
  · cases get_tc_inj hcg he'

/-- **An accumulator read's source MMA is done**: by the observed commit, or by the D to D
pipeline: an earlier MMA of the lane with the same accumulator and the same cells, whose
completion the done reader forces (`CompletionClosed`). -/
theorem acc_mma_done (hO : MmaOne L X) (hG : SyncGuarded L kernel X)
    {i : EvId} {cell : TcMma.Cell} (hdi : X.async.mmaDone i = true)
    (hr : X.MmaReadCell i cell) {src : EvId} (hs : TcMma.ReadSource L X .acc src i cell)
    (hm : X.MmaCell src cell) : X.async.mmaDone src = true := by
  rcases hs.2.2.1 with (hdn | hpl) | ⟨⟨a', vals', sh', hst⟩, -⟩ | ⟨-, -, c, d, s, acc, mask,
      ⟨pcc, hcc⟩, -, -, -⟩
  · exact hdn.done hX.tcCommit
  · have hw := acc_write hX hT hr
    obtain ⟨-, -, d, s, a, mask, d', s', a', mask', ⟨pcx, hxg⟩, ⟨pci, hig⟩, hsa⟩ := id hpl
    obtain ⟨hon, hct, hm1, aT, idc, hcol, hops⟩ := mma_class hp hX hT hxg hs.2.1
    obtain ⟨hon', hct', hm2, aT', idc', hcol', hops'⟩ := mma_class hp hX hT hig hw
    have hid : idc = idc' ∧ (idc = TmemRow.qkIdesc ∨ idc = TmemRow.pvIdesc) := by
      rcases hcol with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> rcases hcol' with ⟨h4, h5, h6⟩ | ⟨h4, h5⟩
      · exact ⟨h1.trans h4.symm, .inl h1⟩
      · omega
      · omega
      · exact ⟨h1.trans h4.symm, .inr h1⟩
    obtain ⟨rfl, hi⟩ := hid
    have hthr : src.1 = i.1 := mma_same hO hxg hig hon hon' (hct.symm.trans hct')
    have hg : src.1 < L.threads := Frame.lt_of_get hX hxg
    obtain ⟨hl, hh⟩ := ops_cta hp hg hi hops
    obtain ⟨hl', hh'⟩ := ops_cta hp (hthr ▸ hg) hi hops'
    obtain ⟨-, hd1, -⟩ := hops
    obtain ⟨-, hd2, -⟩ := hops'
    have hdd : s.descriptor = s'.descriptor := Option.some.inj (hd1.symm.trans hd2)
    have hlo : s.lowCta = s'.lowCta := by rw [hl, hl', hthr]
    have hhi : s.highCta = s'.highCta := by rw [hh, hh', hthr]
    obtain ⟨hdd', hm', hn', hlo', hhi'⟩ := hsa
    subst hdd' hm1 hm2
    have hlt : src.2 < i.2 := by
      rcases Nat.lt_trichotomy src.2 i.2 with h | h | h
      · exact h
      · exact absurd (Prod.ext hthr h) hs.1
      · exact (TcMma.writeBefore_asymm hX hG hs.2.2.1 (.inl (TcMma.Before.of_mma_po ⟨_, hig⟩
          ⟨_, hxg⟩ (hthr ▸ hg) hthr.symm h ⟨rfl, hm'.symm, hn'.symm, hlo'.symm, hhi'.symm⟩))).elim
    obtain ⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, hc0⟩ := hm
    rw [hxg] at h0
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h0
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h0
    exact hX.mmaCompletion src i ⟨hthr, hlt, hpl, _, _, _, _, _, _, _, _, ⟨_, hxg⟩, ⟨_, hig⟩,
      fun r c => TcMma.writeCell_congr hdd hlo hhi _ _ r c, row, col, cell, hc0⟩ hdi
  · exact (write_not_st hst (.inl hm)).elim
  · obtain ⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, -⟩ := hm
    cases get_tc_inj h0 hcc

/-- **An accumulator read's source is done** (an MMA or a copy): by `acc_mma_done`; no copy
writes an accumulator cell. -/
theorem acc_wrote (hO : MmaOne L X) (hG : SyncGuarded L kernel X)
    (hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      TcMma.CompletedValues L Assumptions.all X i)
    (hD : CpDefined X) {i : EvId} {cell : TcMma.Cell} (hdi : X.async.mmaDone i = true)
    (hr : X.MmaReadCell i cell) {src : EvId} (hs : TcMma.ReadSource L X .acc src i cell) :
    ∃ value, TcMma.Wrote L Assumptions.all X src cell value := by
  refine wrote_of_done hX hCV hD hs.2.1 fun hmc => ?_
  rcases hmc with hm | hcp
  · exact acc_mma_done hp hX hT hO hG hdi hr hs hm
  · exact (acc_no_cp hp hX hT hr hcp).elim

end

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

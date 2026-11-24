-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxEpi

@[expose] public section

/-!
# The read sources of the Tensor Memory reads (`ProtocolRest.tcSource`)

`tcSource_of`: on every consistent execution no required Tensor Memory read lacks a source
(`¬ TcMma.SourceUnsafe`, the three clauses of `TcMma.sourceSafe_iff`), given `SourceRest`: the
sources of the registers of the softmax region's loads (`ldS`, `ldO`) and of the A reads of the
PV MMAs. The other cases are proved here:

* the registers of the epilogue's load (`Lk.tcld_event`: a load is at `ldS`, `ldO` or the
  epilogue's `ld`): the last PV MMA (`Rs.oSourceAll_of`) with its `f32` result
  (`ldSource_result`);
* the accumulator reads of a completed MMA (`acc_source`): QK step `j + 1` reads step `j`
  (`QkChain.prev`), PV step `j + 1` reads step `j` (`PvNext`), PV step 0 of an iteration `i ≥ 2`
  the source `ElemPrem.oBase` names (an MMA, or a store with its stored value); an MMA source is
  completed (`done_prev`) and has an `f32` result (`ResultF32`). QK step 0 and PV step 0 of
  iteration 1 do not accumulate, so they read no accumulator.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qx
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Result cells -/

/-- A position a write maps to a cell has that cell as its result cell. -/
theorem resultCell_of_writeCell {s : OperandSpec} {b : Nat} {m : List Nat} {r c : Nat}
    {cell : Cell} (h : writeCell s b m r c = some cell) : resultCell s b r c = some cell := by
  unfold writeCell at h
  by_cases hm : OutputMaskValid s.descriptor.group m
  · simp only [hm, not_true_eq_false, ↓reduceIte] at h
    cases hr : resultCell s b r c with
    | none => rw [hr] at h; simp at h
    | some c0 =>
      rw [hr] at h
      simp only [bind, Option.bind] at h
      cases hw : m[(r / (s.descriptor.m / s.descriptor.group.size) * 128 + c0.lane) / 32]? with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h
        split at h
        · simp at h
        · simp at h
          exact congrArg some h.2
  · simp [hm] at h

/-- A result cell is of a row and a column of the shape. -/
theorem resultCell_bounds {s : OperandSpec} {b r c : Nat} {cell : Cell}
    (h : resultCell s b r c = some cell) : r < s.descriptor.m ∧ c < s.descriptor.n := by
  simp only [resultCell] at h
  split at h
  · rename_i hc
    exact ⟨hc.2.2.1, hc.2.2.2.1⟩
  · cases h

/-- With the write of a position known, its result cell is its written cell. -/
theorem writeCell_of_resultCell {s : OperandSpec} {b : Nat} {m : List Nat} {r c : Nat}
    {cell c0 : Cell} (hw : writeCell s b m r c = some c0) (hr : resultCell s b r c = some cell) :
    writeCell s b m r c = some cell := by
  rw [hw, ← Option.some.inj ((resultCell_of_writeCell hw).symm.trans hr)]

/-! ### The premises -/

/-- **The sources without a proof**: every register of a load of the softmax region (`ldS`,
`ldO`) and every A cell of a completed MMA has a read source with a value. -/
structure SourceRest (Q : Params) (L : Launch) (X : Execution) : Prop where
  ldSm : ∀ {g k pc a j : Nat} {vals : List Value} {sh : TcShape} {d : Sm.D} {cell : Cell},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    St Q L X g k = some (some (.d (.sm d))) → LoadCell L X (g, k) j cell →
    ∃ source value, ReadSource L X .ld source (g, k) cell ∧
      Wrote L Assumptions.all X source cell value
  a : ∀ i cell, X.async.mmaDone i = true → X.MmaACell i cell →
    ∃ source value, ReadSource L X .a source i cell ∧ Wrote L Assumptions.all X source cell value

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hw : MmaWords Q L X) (hch : QkChain Q L X)
  (hnext : PvNext Q L X) (E : ElemPrem Q L X) (hres : ResultF32 L X)
include hpre hX hf hw hch hnext E hres

/-- **The accumulator read of a completed MMA has a source with a value.** -/
theorem acc_source : ∀ i cell, X.async.mmaDone i = true → X.MmaReadCell i cell →
    ∃ source value, ReadSource L X .acc source i cell ∧
      Wrote L Assumptions.all X source cell value := by
  rintro ⟨g, k⟩ cell hd ⟨dst, sp, mask, row, col, ⟨pc, he⟩, hrc⟩
  have hg : g < L.threads := event_thread_lt hX he
  obtain ⟨hr, hc⟩ := resultCell_bounds hrc
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d, P, j, hσ, hI, hs, hq, hdst, hacc, hmask⟩ | ⟨d, P, j, hσ, hI, hs, hq, hdst, hacc, hmask⟩
  · -- a QK MMA
    rw [hq.desc] at hr hc
    have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
    have hwc : writeCell sp dst mask row col = some cell := by
      have h0 := qk_writeCell (i := d.i) hq.desc hq.low (by omega : d.tm + 384 ≤ 512) hr hc
      rw [← hdst, ← hmask] at h0
      exact writeCell_of_resultCell h0 hrc
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero => simp at hacc
    | succ j =>
      obtain ⟨k', hk', hσ', ⟨pc', dst', sp', acc', mask', he'⟩, hrs⟩ := hch.prev hj hσ hs
      rcases mma_event_cases hpre hX hf hg he' with
        ⟨d', P', j', hσ'', -, hs', hq', hdst', -, hmask'⟩ | ⟨d', P', j', hσ'', -, hs', -⟩
      · have hdd : d' = { d with site := .qk ⟨j, by omega⟩ } := by
          have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
          simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
          exact this.1
        rw [hdd] at hdst' hq'
        have hdst2 : dst' = dst := by rw [hdst', hdst]
        have hmask2 : mask' = mask := by rw [hmask', hmask]
        subst hdst2 hmask2
        have hD : sp'.descriptor = sp.descriptor := by rw [hq'.desc, hq.desc]
        have hL : sp'.lowCta = sp.lowCta := by rw [hq'.low, hq.low]
        have hH : sp'.highCta = sp.highCta := by rw [hq'.high, hq.high]
        have hd' := done_prev hX hg hk' he he' hD hL hH hwc hd
        have hwc' : writeCell sp' dst' mask' row col = some cell := by
          rw [writeCell_congr hD hL hH]; exact hwc
        obtain ⟨v, hv⟩ := hres k' hg he' hd' hwc'
        exact ⟨_, _, hrs cell ⟨_, _, _, _, _, _, ⟨pc, he⟩, hwc⟩, .inl hv⟩
      · exfalso
        have hdd : d' = { d with site := .qk ⟨j, by omega⟩ } := by
          have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
          simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
          exact this.1
        rw [hdd] at hs'
        simp at hs'
  · -- a PV MMA
    rw [hq.desc] at hr hc
    have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
    have hcell : cell = oCell (g / L.block) d.tm row col := by
      have h0 := pv_writeCell hq.desc hq.low (by omega : d.tm + 384 ≤ 512) hr hc
      rw [← hdst, ← hmask] at h0
      exact Option.some.inj (hrc.symm.trans (resultCell_of_writeCell h0))
    have hwc : writeCell sp dst mask row col = some cell := by
      rw [hcell, hdst, hmask]
      exact pv_writeCell hq.desc hq.low (by omega) hr hc
    obtain ⟨h1, -, -⟩ := hI.pv (by simp [Mma.PvSite, hs])
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero =>
      by_cases hi1 : d.i = 1
      · simp [hi1] at hacc
      · obtain ⟨src, hrs, hsrc⟩ := E.oBase hg ⟨_, he⟩ hσ hs (by omega) hd
          (fun k' _ {_ _ _ _ _} he1 hd1 {_ _ _} hw1 => hres k' hg he1 hd1 hw1) hr hc
        rw [← hcell] at hrs hsrc
        rcases hsrc with ⟨k', d', P', hk', rfl, hσ', ⟨pc', dst', sp', acc', mask', he'⟩, hs7,
          hi', htm⟩ | ⟨old, v, hst, -⟩
        · rcases mma_event_cases hpre hX hf hg he' with
            ⟨d'', P'', j', hσ'', -, hs', -⟩ | ⟨d'', P'', j', hσ'', -, hs', hq', hdst', -, hmask'⟩
          · exfalso
            have hdd : d'' = d' := by
              have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
              simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
              exact this.1
            subst hdd
            rw [hs7] at hs'
            simp at hs'
          · have hdd : d'' = d' := by
              have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
              simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
              exact this.1
            subst hdd
            have hdst2 : dst' = dst := by rw [hdst', hdst, htm]
            have hmask2 : mask' = mask := by rw [hmask', hmask]
            subst hdst2 hmask2
            have hD : sp'.descriptor = sp.descriptor := by rw [hq'.desc, hq.desc]
            have hL : sp'.lowCta = sp.lowCta := by rw [hq'.low, hq.low]
            have hH : sp'.highCta = sp.highCta := by rw [hq'.high, hq.high]
            have hd' := done_prev hX hg hk' he he' hD hL hH hwc hd
            have hwc' : writeCell sp' dst' mask' row col = some cell := by
              rw [writeCell_congr hD hL hH]; exact hwc
            obtain ⟨u, hu⟩ := hres k' hg he' hd' hwc'
            exact ⟨_, _, hrs, .inl hu⟩
        · exact ⟨_, _, hrs, .inr (.inl hst)⟩
    | succ j =>
      obtain ⟨k', hk', hσ', ⟨pc', dst', sp', acc', mask', he'⟩, hrs⟩ := hnext hj hσ hs
      rcases mma_event_cases hpre hX hf hg he' with
        ⟨d', P', j', hσ'', -, hs', -⟩ | ⟨d', P', j', hσ'', -, hs', hq', hdst', -, hmask'⟩
      · exfalso
        have hdd : d' = { d with site := .pv ⟨j, by omega⟩ } := by
          have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
          simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
          exact this.1
        rw [hdd] at hs'
        simp at hs'
      · have hdd : d' = { d with site := .pv ⟨j, by omega⟩ } := by
          have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
          simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
          exact this.1
        rw [hdd] at hdst' hq'
        have hdst2 : dst' = dst := by rw [hdst', hdst]
        have hmask2 : mask' = mask := by rw [hmask', hmask]
        subst hdst2 hmask2
        have hD : sp'.descriptor = sp.descriptor := by rw [hq'.desc, hq.desc]
        have hL : sp'.lowCta = sp.lowCta := by rw [hq'.low, hq.low]
        have hH : sp'.highCta = sp.highCta := by rw [hq'.high, hq.high]
        have hd' := done_prev hX hg hk' he he' hD hL hH hwc hd
        have hwc' : writeCell sp' dst' mask' row col = some cell := by
          rw [writeCell_congr hD hL hH]; exact hwc
        obtain ⟨v, hv⟩ := hres k' hg he' hd' hwc'
        exact ⟨_, _, hrs cell ⟨_, _, _, _, _, _, ⟨pc, he⟩, hwc⟩, .inl hv⟩

/-- **`ProtocolRest.tcSource`**: no required Tensor Memory read lacks a source, given the sources
of the softmax region's loads and of the A reads (`SourceRest`). -/
theorem tcSource_of (hso : Rs.OSourceAll Q L X) (R : SourceRest Q L X) :
    ¬ SourceUnsafe L Assumptions.all X := by
  intro hu
  apply hu
  rw [sourceSafe_iff]
  refine ⟨?_, acc_source hpre hX hf hw hch hnext E hres, R.a⟩
  rintro ⟨g, k⟩ j cell ⟨a, vals, sh, ⟨pc, he⟩, hj, rfl⟩
  have hg : g < L.threads := event_thread_lt hX he
  rcases (Interface.Lk.tcld_event hpre hX hf hg he).2.2 with ⟨d, hσ, -⟩ | ⟨d, hσ, hs, ha⟩
  · exact R.ldSm hg he hσ ⟨a, vals, sh, ⟨pc, he⟩, hj, rfl⟩
  · have hsh := (Interface.Lk.tcld_event hpre hX hf hg he).1
    subst ha hsh
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    have hI : Epi.Inv d := hinv.2.1
    have hsk : d.sk = false := hI.pre (.inr (.inl hs))
    obtain ⟨⟨mg, mk⟩, pcm, dst, sp, acc, mask, dm, P, hml, -, hem, -, -, -, -, hsrc⟩ :=
      hso hg hσ hsk hσ hs rfl he
    obtain ⟨x, hx⟩ := ldSource_result hX hres hml hem he (hsrc j (by
      have := (Interface.Lk.tcld_event hpre hX hf hg he).2.1; omega))
    exact ⟨_, _, hsrc j (by have := (Interface.Lk.tcld_event hpre hX hf hg he).2.1; omega),
      .inl hx⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Qx

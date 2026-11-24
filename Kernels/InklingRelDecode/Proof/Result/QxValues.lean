-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.PrChain
public import Lemmas.Tcgen05.MmaCompletionFrame

@[expose] public section

/-!
# Every completed MMA has derived values, from the operand elements (`ProtocolRest.values`)

`values_of`: on every consistent execution (prefixes included), every unmasked result cell of a
completed MMA has a derived value (`TcMma.CompletedValues`), given `ElemPrem`: the operand
elements every completed MMA reads are reals, and the accumulator source of step 0 of a PV block
after the first is the previous block's last PV MMA or a store with an `f32` word.

The proof is a strong induction on the MMA's event index (`result_of`). An MMA event is a QK or a
PV step of the MMA warp (`mma_event_cases`). It evaluates (`MmaBf16.eval_all`) once its 16 A
elements of the row, its 16 B elements of the column and its old accumulator have values. The old
accumulator of QK step `j + 1` is QK step `j` (`QkChain.prev`), of PV step `j + 1` PV step `j`
(`Pr.oAccNext_of`), of PV step 0 of block `b ≥ 1` the premise `ElemPrem.oBase`. In each case the
source is an earlier MMA event of the thread with the same write footprint, so it is completed
(`Consistent.mmaCompletion`, DEP-TC-COMPLETION-CLOSURE: `done_prev`) and, by the induction, has a
value at the cell.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qx
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The write footprint -/

/-- A cell a result position maps to is a cell of a row and column of the shape. -/
theorem writeCell_bounds {s : OperandSpec} {base : Nat} {mask : List Nat} {row col : Nat}
    {cell : Cell} (h : writeCell s base mask row col = some cell) :
    row < s.descriptor.m ∧ col < s.descriptor.n := by
  unfold writeCell resultCell at h
  by_contra hc
  simp only [not_and_or, not_lt] at hc
  by_cases hm : OutputMaskValid s.descriptor.group mask
  · simp only [hm, not_true_eq_false, ↓reduceIte] at h
    split at h
    · rename_i hcond
      obtain ⟨-, -, h1, h2, -⟩ := hcond
      rcases hc with h3 | h3 <;> omega
    · simp at h
  · simp [hm] at h

/-- The write footprint depends on the operand spec only through its descriptor and its CTAs. -/
theorem writeCell_congr {s s' : OperandSpec} (hd : s.descriptor = s'.descriptor)
    (hl : s.lowCta = s'.lowCta) (hh : s.highCta = s'.highCta) (base : Nat) (mask : List Nat)
    (row col : Nat) : writeCell s base mask row col = writeCell s' base mask row col := by
  unfold writeCell resultCell
  rw [hd, hl, hh]

/-- **An earlier MMA of the thread with the same write footprint is completed** when a later one
is (DEP-TC-COMPLETION-CLOSURE). -/
theorem done_prev (hX : Consistent L kernel Assumptions.all mem0 X) {g k k' pc pc' dst : Nat}
    {sp sp' : OperandSpec} {acc acc' : Bool} {mask : List Nat} (hg : g < L.threads)
    (hk : k' < k) (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    (he' : X.get (g, k') = some ⟨pc', .tc (.mma dst sp' acc' mask)⟩)
    (hd : sp'.descriptor = sp.descriptor) (hl : sp'.lowCta = sp.lowCta)
    (hh : sp'.highCta = sp.highCta) {row col : Nat} {cell : Cell}
    (hw : writeCell sp dst mask row col = some cell)
    (hdone : X.async.mmaDone (g, k) = true) : X.async.mmaDone (g, k') = true := by
  refine hX.mmaCompletion (g, k') (g, k) (completionPrecedes_iff.mpr ⟨rfl, hk, ?_, ?_, ?_⟩) hdone
  · exact ⟨⟨hg, hg, rfl⟩, rfl⟩
  · exact ⟨dst, sp', acc', mask, dst, sp, acc, mask, ⟨pc', he'⟩, ⟨pc, he⟩,
      ⟨rfl, by rw [hd], by rw [hd], hl, hh⟩⟩
  · refine ⟨dst, sp', acc', mask, dst, sp, acc, mask, ⟨pc', he'⟩, ⟨pc, he⟩,
      fun r c => writeCell_congr hd hl hh dst mask r c, row, col, cell, ?_⟩
    rw [writeCell_congr hd hl hh]
    exact hw

/-- A completed MMA has recorded its operands. -/
theorem ops_of_done (hX : Consistent L kernel Assumptions.all mem0 X) {m : EvId}
    (hd : X.async.mmaDone m = true) : ∃ ops, X.async.mmaOperands m = some ops := by
  have hst := hX.tma.2.1.2 m hd
  cases h : X.async.mmaOperands m with
  | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
  | some ops => exact ⟨ops, rfl⟩

/-! ### The premises -/

/-- **Every result cell of a completed MMA of thread `g` before its `k`-th event has an `f32`
value** (the induction hypothesis of `result_of`, for the thread of the MMA at `(g, k)`). -/
def ResultBelow (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∀ k' < k, ∀ {pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat},
    X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    X.async.mmaDone (g, k') = true → ∀ {r c : Nat} {cell : Cell},
    writeCell sp dst mask r c = some cell →
    ∃ x, Result L Assumptions.all X (g, k') cell (.float .f32 x)

/-- **The operand elements and the base accumulators of the completed MMAs.**
* `qkA`, `pvA`: every A element (row `r < 64`, index `kk < 16`) of a completed QK or PV MMA is a
  real: the bf16 query tile (QK; the padding rows and the rows of tokens at or beyond `q_len` are
  the zeros of the masked query loads) or the bf16 probabilities the softmax stored in Tensor
  Memory (PV).
* `b`: every B element (column `n < 128`) of a completed MMA is a real (the K or V tile the copies
  wrote).
* `oBase`: the accumulator of PV step 0 of an iteration `i ≥ 2` has a read source that is the last
  PV MMA of iteration `i - 1` or a store whose word reads as an `f32` number, given that the
  earlier MMAs of the thread have `f32` results (`ResultBelow`: the store's word is `alpha` times
  a word an earlier MMA left). -/
structure ElemPrem (Q : Params) (L : Launch) (X : Execution) : Prop where
  qkA : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {r kk : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk j →
    X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → r < 64 → kk < 16 →
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk = .ok x
  pvA : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {r kk : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv j →
    X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → r < 64 → kk < 16 →
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk = .ok x
  b : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {n kk : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) →
    (d.site = .qk j ∨ d.site = .pv j) →
    X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → n < 128 → kk < 16 →
    ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b n kk = .ok y
  oBase : ∀ {g k : Nat} {d : Mma.D} {P : Loader.Pro}, g < L.threads →
    (∃ e, X.get (g, k) = some e) →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv 0 → 2 ≤ d.i →
    X.async.mmaDone (g, k) = true → ResultBelow L X g k → ∀ {r n : Nat}, r < 64 → n < 128 →
    ∃ src, ReadSource L X .acc src (g, k) (oCell (g / L.block) d.tm r n) ∧
      ((∃ (k' : Nat) (d' : Mma.D) (P' : Loader.Pro), k' < k ∧ src = (g, k') ∧
          St Q L X g k' = some (some (.w (.mma d' P'))) ∧
          (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
          d'.site = .pv 7 ∧ d'.i + 1 = d.i ∧ d'.tm = d.tm) ∨
        ∃ old x, StoreValue L X src (oCell (g / L.block) d.tm r n) old ∧
          valFloat .f32 old = .ok x)

/-- The accumulator source of PV step `j + 1` is PV step `j` (the `next` field of `OAcc`,
`Pr.oAccNext_of`). -/
def PvNext (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k j : Nat} {d : Mma.D} {P : Loader.Pro} (hj : j + 1 < 8),
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .pv ⟨j + 1, hj⟩ →
    ∃ k', k' < k ∧ St Q L X g k' =
        some (some (.w (.mma { d with site := .pv ⟨j, by omega⟩ } P))) ∧
      (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      ∀ cell, X.MmaCell (g, k) cell → ReadSource L X .acc (g, k') (g, k) cell

/-! ### The induction -/

/-- The 16 elements of a row as a function. -/
theorem elems_fun {f : Nat → Exec ℝ} (h : ∀ kk < 16, ∃ x, f kk = .ok x) :
    ∃ x : Nat → ℝ, ∀ kk < 16, f kk = .ok (x kk) := by
  classical
  refine ⟨fun kk => if hk : kk < 16 then Classical.choose (h kk hk) else 0, fun kk hk => ?_⟩
  simp only [hk, ↓reduceDIte]
  exact Classical.choose_spec (h kk hk)

/-- The accumulator value `valFloat` reads. -/
theorem acc_some (old : Value) :
    Assumption.idealMmaAccumulator .f32 true (some old) = valFloat .f32 old := rfl

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hw : MmaWords Q L X) (hch : QkChain Q L X)
  (hnext : PvNext Q L X) (E : ElemPrem Q L X)
include hpre hX hf hw hch hnext E

/-- **Every result cell of a completed MMA has an `f32` value.** -/
theorem result_of : ∀ (k : Nat) {g pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat}, g < L.threads → X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    X.async.mmaDone (g, k) = true → ∀ {r c : Nat} {cell : Cell},
    writeCell sp dst mask r c = some cell →
    ∃ x, Result L Assumptions.all X (g, k) cell (.float .f32 x) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g pc dst sp acc mask hg he hd r c cell hwc
  obtain ⟨ops, hops⟩ := ops_of_done hX hd
  obtain ⟨hr, hc⟩ := writeCell_bounds hwc
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d, P, j, hσ, hI, hs, hq, hdst, hacc, hmask⟩ | ⟨d, P, j, hσ, hI, hs, hq, hdst, hacc, hmask⟩
  · -- a QK MMA
    rw [hq.desc] at hr hc
    obtain ⟨x, hx⟩ := elems_fun fun kk hk => E.qkA hg he hσ hs hd hops hr hk
    obtain ⟨y, hy⟩ := elems_fun fun kk hk => E.b hg he hσ (.inl hs) hd hops hc hk
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero =>
      have hacc' : acc = false := by simpa using hacc
      subst hacc'
      exact ⟨_, .overwrite ⟨pc, he⟩ hwc hops (qk_eval hX he hq.desc hops hr hc hx hy
        (old := none) (prev := 0) rfl)⟩
    | succ j =>
      have hacc' : acc = true := by simpa using hacc
      subst hacc'
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
        have hwc' : writeCell sp' dst' mask' r c = some cell := by
          rw [writeCell_congr hD hL hH]; exact hwc
        obtain ⟨v, hv⟩ := ih k' hk' hg he' hd' hwc'
        exact ⟨_, .accumulate ⟨pc, he⟩ hwc hops hv
          (hrs cell ⟨_, _, _, _, _, _, ⟨pc, he⟩, hwc⟩)
          (qk_eval hX he hq.desc hops hr hc hx hy (idealMmaAccumulator_f32 v))⟩
      · exfalso
        have hdd : d' = { d with site := .qk ⟨j, by omega⟩ } := by
          have := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
          simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
          exact this.1
        rw [hdd] at hs'
        simp at hs'
  · -- a PV MMA
    rw [hq.desc] at hr hc
    obtain ⟨x, hx⟩ := elems_fun fun kk hk => E.pvA hg he hσ hs hd hops hr hk
    obtain ⟨y, hy⟩ := elems_fun fun kk hk => E.b hg he hσ (.inr hs) hd hops hc hk
    obtain ⟨h1, -, -⟩ := hI.pv (by simp [Mma.PvSite, hs])
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero =>
      by_cases hi1 : d.i = 1
      · have hacc' : acc = false := by simpa [hi1] using hacc
        subst hacc'
        exact ⟨_, .overwrite ⟨pc, he⟩ hwc hops (pv_eval hX he hq.desc hops hr hc hx hy
          (old := none) (prev := 0) rfl)⟩
      · have hacc' : acc = true := by simpa [hi1] using hacc
        subst hacc'
        have hT : d.tm = 0 := hw.tm (m := (g, k)) ⟨P, hσ⟩
        have hcell : cell = oCell (g / L.block) d.tm r c := by
          rw [hdst, hmask, pv_writeCell hq.desc hq.low (by omega) hr hc] at hwc
          exact (Option.some.inj hwc).symm
        subst hcell
        obtain ⟨src, hrs, hsrc⟩ := E.oBase hg ⟨_, he⟩ hσ hs (by omega) hd
          (fun k' hk' {_ _ _ _ _} he1 hd1 {_ _ _} hw1 => ih k' hk' hg he1 hd1 hw1) hr hc
        rcases hsrc with ⟨k', d', P', hk', rfl, hσ', ⟨pc', dst', sp', acc', mask', he'⟩, hs7,
          hi', htm⟩ | ⟨old, v, hst, hv⟩
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
            have hwc' : writeCell sp' dst' mask' r c = some (oCell (g / L.block) d.tm r c) := by
              rw [writeCell_congr hD hL hH]; exact hwc
            obtain ⟨u, hu⟩ := ih k' hk' hg he' hd' hwc'
            exact ⟨_, .accumulate ⟨pc, he⟩ hwc hops hu hrs
              (pv_eval hX he hq.desc hops hr hc hx hy (idealMmaAccumulator_f32 u))⟩
        · exact ⟨_, .accumulateStored ⟨pc, he⟩ hwc hops hst hrs
            (pv_eval hX he hq.desc hops hr hc hx hy (by rw [acc_some]; exact hv))⟩
    | succ j =>
      have hacc' : acc = true := by simpa using hacc
      subst hacc'
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
        have hwc' : writeCell sp' dst' mask' r c = some cell := by
          rw [writeCell_congr hD hL hH]; exact hwc
        obtain ⟨v, hv⟩ := ih k' hk' hg he' hd' hwc'
        exact ⟨_, .accumulate ⟨pc, he⟩ hwc hops hv
          (hrs cell ⟨_, _, _, _, _, _, ⟨pc, he⟩, hwc⟩)
          (pv_eval hX he hq.desc hops hr hc hx hy (idealMmaAccumulator_f32 v))⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Qx

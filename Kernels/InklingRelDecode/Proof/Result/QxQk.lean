-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxEpi

@[expose] public section

/-!
# The QK MMAs have `f32` results, from the query and key elements alone (`ResultQk`)

`result_of` proves that every completed MMA has `f32` results from all the operand elements
(`ElemPrem`), among them the probabilities the softmax region stores (`ElemPrem.pvA`), which are
numbers only where the S words the region reads are `f32` numbers, the QK MMAs' results. So the
QK MMAs come first: `resultQk_of` is the QK case of `result_of`, a strong induction on the MMA's
event index, from the A elements of the QK MMAs (the query tile) and the B elements (the key tile)
only. The old accumulator of QK step `j + 1` is QK step `j` (`QkChain.prev`), an earlier QK MMA.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qx
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every result cell of a completed QK MMA has an `f32` value. -/
def ResultQk (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ (k : Nat) {g pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
    {P : Loader.Pro} {j : Fin 8}, g < L.threads →
    X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk j →
    X.async.mmaDone (g, k) = true → ∀ {r c : Nat} {cell : Cell},
    writeCell sp dst mask r c = some cell →
    ∃ x, Result L Assumptions.all X (g, k) cell (.float .f32 x)

theorem resultQk_of_f32 (h : ResultF32 L X) : ResultQk Q L X :=
  fun k _ _ _ _ _ _ _ _ _ hg he _ _ hd _ _ _ hwc => h k hg he hd hwc

/-- **Every result cell of a completed QK MMA has an `f32` value**, from the query and key
elements. -/
theorem resultQk_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hch : QkChain Q L X)
    (qkA : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
      {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {r kk : Nat}, g < L.threads →
      X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
      St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk j →
      X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → r < 64 → kk < 16 →
      ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a r kk = .ok x)
    (qkB : ∀ {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {d : Mma.D}
      {P : Loader.Pro} {j : Fin 8} {ops : AsyncCopy.MmaOperands} {n kk : Nat}, g < L.threads →
      X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
      St Q L X g k = some (some (.w (.mma d P))) → d.site = .qk j →
      X.async.mmaDone (g, k) = true → X.async.mmaOperands (g, k) = some ops → n < 128 →
      kk < 16 → ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b n kk = .ok y) :
    ResultQk Q L X := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g pc dst sp acc mask d0 P0 j0 hg he hσ0 hs0 hd r c cell hwc
  obtain ⟨ops, hops⟩ := ops_of_done hX hd
  obtain ⟨hr, hc⟩ := writeCell_bounds hwc
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d, P, j, hσ, hI, hs, hq, hdst, hacc, hmask⟩ | ⟨d, P, j, hσ, hI, hs, hq, hdst, hacc, hmask⟩
  · rw [hq.desc] at hr hc
    obtain ⟨x, hx⟩ := elems_fun fun kk hk => qkA hg he hσ hs hd hops hr hk
    obtain ⟨y, hy⟩ := elems_fun fun kk hk => qkB hg he hσ hs hd hops hc hk
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
        obtain ⟨v, hv⟩ := ih k' hk' hg he' hσ' rfl hd' hwc'
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
  · exfalso
    have hdd : d = d0 := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ0))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    rw [hs] at hs0
    cases hs0

end
end PTX.Kernels.InklingRelDecode.Proof.Qx

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.ResultFacts
public import Kernels.Fp16Gemm8192.Proof.TcInstrFacts
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.Order
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Values
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Last
public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstrPrev
public import Kernels.Fp16Gemm8192.Proof.Safety.OperandValues
public import Kernels.Fp16Gemm8192.Proof.Result.Values
public import Kernels.Fp16Gemm8192.Proof.GuardFacts

@[expose] public section

/-! # The values of `ResultGoal`

This file sits at the top of the proof tree, outside the layer order (as `TcLoadFacts.lean` does):
it supplies the value half of `ResultGoal` (`output_values_of`) with the sources of the output's
values, all from the thread facts (`threadFacts`): the staging bytes the TMA stores read
(`OutputRing.staging_value`, over the region layer's staging accessors and the CLC responses'
agreement), the MMA the Tensor Memory loads read (`TmemRing.load_last`), the accumulators' sources
(`Safety.mmaAccSources`) and the MMAs' operand elements (`operand_values`: the copy of each
operand element, `InputRing.pair_copy`, copies its matrix element, `Safety.copy_value`). With the
write structure (`result_goal_of`), `ResultGoal` holds (`result_goal`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The MMAs' operand elements** (`OperandValues`). -/
theorem operand_values (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    OperandValues P L X := by
  have ht := threadFacts hpre hX
  have hacc := Region.inputAccessors hpre hX ht
  intro g km pc dst sp acc mask m s jj ops he hσ hs hops isB row kk hrow hkk
  obtain ⟨copy, o, x, y, hobs, ⟨mm, s', jj', lw, bw, jw, pcw, alw, hσ', hs', hget, hσw, hlsite,
    hslot, hjw, hcta, hcnt, hx, hy⟩, hz⟩ :=
    InputRing.pair_copy hpre hX ht hacc ⟨pc, he⟩ isB (m := row * 16 + kk) (by omega)
  rw [hσ] at hσ'
  simp only [Option.some.injEq, Sum.inr.injEq, Prologue.Role.mma.injEq] at hσ'
  subst hσ'
  rw [hs] at hs'
  simp only [Mma.Site.mma.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  obtain ⟨gw, kw⟩ := copy
  simp only at hget hσw hcta hcnt
  refine ⟨gw, kw, pcw, alw, o.spec, lw, bw, jw, hget, hσw, hlsite, by omega, hslot, hjw, hcnt, ?_⟩
  -- the two bytes of the element
  have hb : ∀ z, z < 2 → (if isB then ops.b else ops.a)[2 * (row * 16 + kk) + z]? =
      some (some ((Value.float .f16 ((if isB then P.b else P.a) ((o.spec.origin 1).toNat + y)
        ((o.spec.origin 0).toNat + x))).byteAt z)) := by
    intro z hz'
    obtain ⟨l, hbl, hwl, ⟨v, hv⟩, hvis, hord⟩ := hz z hz'
    obtain ⟨observed, hr, hgetb⟩ := hX.tma.2.1.mma_read_exists ⟨pc, he⟩ hops hbl
    obtain ⟨addr, hTI⟩ := (hX.tensor (gw, kw) o hobs).1
    rw [hgetb, mma_read_of_tensor_write hX hr hobs hTI hwl hv hvis hord,
      Safety.copy_value hpre hX ht hobs hget hσw hlsite hz' hv]
    congr 4
    cases isB
    · simp only [Bool.false_eq_true, ↓reduceIte] at hjw ⊢
      simp only [show jw.val < 2 by omega, ↓reduceIte]
    · simp only [↓reduceIte] at hjw ⊢
      simp only [show ¬ jw.val < 2 by omega, ↓reduceIte]
  refine idealMmaElement_of_bytes ?_
  have hl := Safety.take_two (hb 0 (by decide)) (hb 1 (by decide))
  simp only [Nat.add_zero] at hl
  rw [hl, hx, hy, show (row * 16 + kk) % 16 = kk by omega, show (row * 16 + kk) / 16 % 128 =
    row % 128
    by omega]
  simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]

/-- **The output values** (`OutputValues`) of a consistent execution. -/
theorem output_values_of (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    OutputValues P L X := by
  have ht := threadFacts hpre hX
  have hub : ∀ g j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩ :=
    fun g j pc f h => no_ub hpre hX ⟨(g, j), pc, f, h⟩
  have hag := ClcRing.allResponsesAgree hpre hX ht (Region.responseWriters hpre hX ht)
  have hins := Classical.not_not.mp (no_instructionUnsafe hpre hX)
  exact Result.output_values hpre hX ht hub
    (fun h k pc a sp c s x y z o v he hσ hs hx hy hz ho hv =>
      OutputRing.staging_value hpre hX ht hag
        (Region.stagingAccessors hpre hX ht) hub he hσ hs hx hy hz ho hv)
    (fun _ _ _ _ _ _ hld hj => TmemRing.load_last hpre hX ht hins (tmem_live hpre hX) hld hj)
    (Safety.mmaAccSources hpre hX ht (mmaReleased hpre hX)) (operand_values hpre hX) hag
    (TmemRing.tmemWords hX ht) (sync_guarded hpre hX) (load_words hpre hX)

/-- **`ResultGoal`**: a complete execution leaves the specified output. -/
theorem result_goal (hpre : Pre P L mem0) : ResultGoal kernel Prod L mem0 (Post P mem0) :=
  result_goal_of hpre fun _ hX _ => output_values_of hpre hX

end

end PTX.Kernels.Fp16Gemm8192.Proof

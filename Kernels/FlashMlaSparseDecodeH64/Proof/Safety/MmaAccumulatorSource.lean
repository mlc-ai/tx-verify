-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MmaShapes
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.PvCompletedValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.QkCompletedValue

@[expose] public section

/-! # Accumulating MMA instructions have a source for each completed C read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow MmaDataTrace Protocol Result
open Wg1Mma (pvDest tmemO)

private theorem source_of_seed {L : Launch} {X : Execution} {e : EvId} {cell : TcMma.Cell}
    {value : ℝ} (h : GemmAccumulator L X e cell true value) :
    ∃ source value, TcMma.ReadSource L X .acc source e cell ∧
      TcMma.Wrote L Assumptions.all X source cell value := by
  cases h with
  | priorMma hread hval => exact ⟨_, _, hread, .inl hval⟩
  | priorStore hread hval => exact ⟨_, _, hread, .inr (.inl hval)⟩

/-- A represented result cell lies inside the logical matrix dimensions. -/
theorem result_indices {s : TcMma.OperandSpec} {base row col : Nat} {cell : TcMma.Cell}
    (h : TcMma.resultCell s base row col = some cell) :
    row < s.descriptor.m ∧ col < s.descriptor.n := by
  unfold TcMma.resultCell at h
  dsimp only at h
  split at h
  · rename_i hguard
    exact ⟨hguard.2.2.1, hguard.2.2.2.1⟩
  · cases h

/-- Every completed QK or PV accumulator read has an actual prior write and its value. -/
theorem mma_acc_source {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {e : EvId} {cell : TcMma.Cell} (hDone : X.async.mmaDone e = true)
    (hread : X.MmaReadCell e cell) :
    ∃ source value, TcMma.ReadSource L X .acc source e cell ∧
      TcMma.Wrote L Assumptions.all X source cell value := by
  obtain ⟨g, i⟩ := e
  obtain ⟨d, s, mask, row, col, hi, hresult⟩ := hread
  rcases MmaAccessWindow.mma_spec hpre hX hs ht hi with ⟨rfl,
    ⟨block, issue, rfl, rfl, hAcc, hState⟩ | ⟨block, issue, rfl, rfl, hAcc, hState⟩⟩
  · have hBounds := result_indices hresult
    let head : Fin 64 := ⟨row, hBounds.1⟩
    let channel : Fin 128 := ⟨col, hBounds.2⟩
    rw [qkResultCell L g block issue head channel] at hresult
    cases hresult
    have hi' : X.MmaIssue (g, i) _ _ (qkAccum issue) _ := hAcc ▸ hi
    obtain ⟨_, hseed⟩ :=
      (qk_completed_cell issue head channel hpre hX hs hi' hState hDone).1
    exact source_of_seed (hAcc.symm ▸ hseed)
  · have hBounds := result_indices hresult
    let head : Fin 64 := ⟨row, hBounds.1⟩
    let channel : Fin 256 := ⟨col, hBounds.2⟩
    let half : Fin 2 := ⟨issue.val % 2, Nat.mod_lt _ (by decide)⟩
    let part : Fin 4 := ⟨issue.val / 2, by have := issue.isLt; omega⟩
    have hk : pvHalfIssue half part = issue := Fin.ext (by dsimp [half, part, pvHalfIssue]; omega)
    have hDest : pvDest issue = tmemO + 128 * half.val := rfl
    rw [pvResultCell L g block issue head channel, hDest] at hresult
    cases hresult
    obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
      (fun a ha => (hs a ha).machine)
    have hThis := hIssuer g i _ rfl hState (by simp)
    subst issuer
    have hi' : PvAccumulatorSource.Issue L X g i block issue := by
      change X.MmaIssue (g, i) _ _ (pvAccum block issue) _
      exact hAcc ▸ hi
    obtain ⟨_, hseed⟩ := (pv_completed_cell half part head channel hpre hX hs ht hIssuer
      (hk.symm ▸ hi') (hk.symm ▸ hState) hDone).1
    rw [hk, ← hAcc] at hseed
    exact source_of_seed hseed

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

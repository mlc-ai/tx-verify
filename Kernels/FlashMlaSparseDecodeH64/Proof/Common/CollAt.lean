-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollKey
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs
public import Lemmas.Kernel.Progress.WarpCollPair
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time

@[expose] public section

/-! # The warp collectives of the thread machine

A thread state at a warp collective (`CollAt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

/-- A thread state at a warp collective. -/
def CollAt (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Prop :=
  ∃ ins, kernel.code[(thread P L g).pc σ]? = some ins ∧ CollIns ins

/-- **The static part of a state's collective**: the instruction's at its pc. -/
def collS (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) : Sched.CollShape :=
  pcShape ((thread P L g).pc σ)

/-- **The static part of a state at a shuffle with immediate operands** is its instruction's. -/
theorem shapeAt_shfl {P : Params} {L : Launch} {g : Nat} {σ : (thread P L g).D} {md : ShflMode}
    {b c : Nat} {ins : Instr} (hi : kernel.code[(thread P L g).pc σ]? = some ins)
    (ho : opShape ins.op = some (.shfl md b c)) :
    Sched.ShapeAt ⟨thread P L, time P L⟩ (collS P L) g σ := by
  have hS : collS P L g σ = .shfl md b c := by simp [collS, pcShape, hi, ho]
  refine ⟨by rw [hS]; trivial, fun t ins' hAt hinv hi' => ?_⟩
  have hii : ins' = ins := by
    have : kernel.code[(thread P L g).pc σ]? = some ins' := hi'
    rw [hi] at this
    exact (Option.some.inj this).symm
  subst hii
  refine ⟨?_, ?_⟩
  · cases hop : ins'.op <;> rw [hop] at ho <;> simp only [opShape, reduceCtorEq] at ho
    rfl
  · rw [hS]
    exact Sched.warpOp_tmpl ho

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

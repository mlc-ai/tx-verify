-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Warp
public import Kernels.TmlFa4Fwd.Proof.Top.JR
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # The invariant of a followed MMA state -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {n : Cls → Nat}

theorem jr_mma_ref {d : (frag p L g .mma).D} (h : JR p L g (.inr ⟨.mma, d⟩, n)) :
    Prologue.warpIndex L g = 12 ∧ Mma.Ref p L g (.inr ⟨.mma, d⟩, n) := by
  rw [JR_eq] at h; unfold RefAll at h
  split_ifs at h with h1 h2 <;> first
    | exact ⟨h2, h⟩
    | simp [SmWarp.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at h

end
end PTX.Kernels.TmlFa4Fwd.Proof

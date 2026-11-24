-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Top.JR
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # The invariant of a followed loader state -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {n : Cls → Nat}

theorem jr_loader {b : Bool} {d : (frag p L g (.loader b)).D}
    (h : JR p L g (.inr ⟨.loader b, d⟩, n)) :
    (Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) ∧
      LdWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.loader b, d⟩, n) := by
  rw [JR_eq] at h; unfold RefAll at h
  split_ifs at h with h1 h2 h3 h4 <;> first
    | exact ⟨h4, h⟩
    | simp [SmWarp.Ref, Epilogue.Ref, Mma.Ref, CorrWarp.Ref] at h

end
end PTX.Kernels.TmlFa4Fwd.Proof

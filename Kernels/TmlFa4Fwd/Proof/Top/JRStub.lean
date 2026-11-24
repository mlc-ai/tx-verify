-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Top.JR
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # The lane of a followed state, by role: no stub, and warp 12 for the MMA role -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat} {n : Cls → Nat}

theorem jr_stub {r : Startup.Entry} {d : (frag p L g (.stub r)).D}
    (h : JR p L g (.inr ⟨.stub r, d⟩, n)) : False := by
  rw [JR_eq] at h; unfold RefAll at h
  split_ifs at h <;> simp [SmWarp.Ref, Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at h

/-- A state of the MMA warp is a lane of warp 12. -/
theorem jr_mma {d : (frag p L g .mma).D} (hJ : JR p L g (.inr ⟨.mma, d⟩, n)) :
    Prologue.warpIndex L g = 12 := by
  rw [JR_eq] at hJ; unfold RefAll at hJ
  split_ifs at hJ with h1 h2 <;> first
    | exact h2
    | simp [SmWarp.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref] at hJ

end
end PTX.Kernels.TmlFa4Fwd.Proof

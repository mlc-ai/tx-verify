-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand

@[expose] public section

/-! # A scheduler that returned from its first pass picked no tile -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {g : Nat}

theorem noPicked_of_exit {d : Epilogue.D} {ns nv : Nat} (hF : Epilogue.Fits p L g d ns nv)
    (hs : d.site = .exit false) : ¬ ∃ R bal, Epilogue.Picked p L g R bal := by
  rintro ⟨R, bal, hP⟩
  rcases Mma.eband hF (by rw [hs]; simp) with ⟨-, -, hk⟩ | ⟨hp2, -⟩
  · exact (hk R bal hP).2.2 false hs
  · rw [hs] at hp2; simp [Mma.ePass] at hp2

end PTX.Kernels.TmlFa4Fwd.Proof

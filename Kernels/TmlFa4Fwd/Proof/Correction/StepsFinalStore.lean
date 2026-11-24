-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Correction.StepsFinalStore0
import Kernels.TmlFa4Fwd.Proof.Correction.StepsFinalStore1

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_fst (hp : Pre p L m) (hg : g < L.threads) (d : D)
    (hs : ∃ st j h, d.site = .fst st j h) :
    (code p L g).StepAt d := by
  obtain ⟨st, j, h, hs⟩ := hs
  fin_cases st <;> fin_cases h
  · exact stepAt_fst00 hp hg d ⟨j, hs⟩
  · exact stepAt_fst01 hp hg d ⟨j, hs⟩
  · exact stepAt_fst10 hp hg d ⟨j, hs⟩
  · exact stepAt_fst11 hp hg d ⟨j, hs⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction

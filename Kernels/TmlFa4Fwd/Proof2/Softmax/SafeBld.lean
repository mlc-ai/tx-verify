-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Safe

@[expose] public section

/-! # The bias loads without undefined behaviour

Every element of every bias load (`ld.shared.v4.b32`) reads a 16-aligned shared address: the
table's `bAddr0` or `bAddr` word (`lo_bAddr0`, `lo_bAddr`) plus an offset of 0 or 16384. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem safe_bld (hp : Pre p L m) (b : Bool) (c : Fin 16) (k : Fin 4) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.bld b c, v, k, acc⟩ := by
  cases b <;> fin_cases c <;> safe_lds

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Data.Machine
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The rescale factor's reads

How the rules of the rescale rounds read a factor that is the pattern of one (`read_one`,
`pairRead_one`), for the step files of the rescale rounds. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

/-- The code's pack of the pattern of one with itself reads as a pair of ones. -/
theorem pairRead_join_one : pairRead (joinValue (.bits 32 (BitVec.ofNat 64 1065353216))
    (.bits 32 (BitVec.ofNat 64 1065353216))) = some (.ok (((1 : ℝ) : EReal), ((1 : ℝ) : EReal))) :=
  pairRead_one

/-- The rules' evaluation at a factor that is the pattern of one. -/
scoped macro_rules
  | `(tactic| rule_simp) => `(tactic| simp only [sOf, read_one, pairRead_one, pairRead_join_one,
      joinValue_float, pairRead_float, bindRead_some_ok, mulEReal_coe, mul_one, erealValue_coe,
      Option.map_some, Option.bind_some])

end PTX.Kernels.TmlFa4Fwd.Proof.Correction

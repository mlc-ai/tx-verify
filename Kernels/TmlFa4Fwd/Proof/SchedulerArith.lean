-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A lane represents a request if it belongs to the batch and has a successor lane carrying its
right endpoint. Lane 31 is reserved for the sentinel at the end of each group. -/
abbrev laneHasRequest (lane batch : Nat) : Prop := lane < batch ∧ lane < 31

/-- Clearing the low byte of a 32-bit value rounds it down to a multiple of 256. -/
theorem lowByteMask {x : Nat} (hx : x < 2 ^ 32) :
    x &&& 4294967040 = x / 256 * 256 := by
  have hDiv : (x &&& 4294967040) / 256 = x / 256 := by
    rw [show 256 = 2 ^ 8 from rfl, Nat.and_div_two_pow]
    change x / 256 &&& (2 ^ 24 - 1) = x / 256
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  have hMod : (x &&& 4294967040) % 256 = 0 := by
    rw [show 256 = 2 ^ 8 from rfl, Nat.and_mod_two_pow]
    simp
  omega

structure CeilSite where
  pc : Nat
  lengthReg : Nat
  quotientReg : Nat
  remainderPred : Nat
  countReg : Nat

set_option maxRecDepth 2000 in

theorem firstScanSource (stage : Fin 5) (lane : Nat) :
    shflSource .up lane (2 ^ stage.val) 0 =
      if 2 ^ stage.val ≤ lane then (lane - 2 ^ stage.val, true) else (lane, false) := by
  have hWidth : 2 ^ stage.val < 32 :=
    Nat.pow_lt_pow_right (by decide) stage.isLt
  simp [shflSource, Nat.mod_eq_of_lt hWidth]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Kinds
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl

@[expose] public section

/-! # Checks of the first round's generated exponent pieces

The kind tables link the output of each piece to the input of the next. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The condition of the run -/

theorem expo1_facts0_eq (V : Nat → Value) :
    Gen.expo1_facts0 V = factsFrom ((Gen.expo1_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The role readings of a run's items are the packs' (`packE`). -/
macro "fns_ok" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.expo1_items0, Gen.expo1_items1, Gen.expo1_items2,
    Gen.expo1_items3, Gen.expo1_items4, Gen.expo1_items5, Gen.expo1_items6, Gen.expo1_items7,
    Gen.expo1_items8, Gen.expo1_items9, Gen.expo1_items10, Gen.expo1_items11, Gen.expo1_items12,
    Gen.expo1_items13, and_true, true_and]
  repeat' first | exact Gen.packE_spec | exact Gen.widenE_spec | constructor))

theorem band_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

/-- Assign one value kind to the listed registers. -/
def expo1KindsAt (kind : Kd) (regs : List Nat) : List (Nat × Kd) :=
  regs.map fun r => (r, kind)

/-- Register kinds at the first exponent run's cuts, checked by `expo1_kok`. -/
@[irreducible] def eL1 : List (Nat × Kd) :=
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (elemRegs.drop 20) ++
  expo1KindsAt (.s .ni) (List.range' 3687 18) ++
  expo1KindsAt (.pr .pw) [8026] ++
  expo1KindsAt (.pr .fl) [8024] ++
  expo1KindsAt (.pr .ni) [8045]

@[irreducible] def eL2 : List (Nat × Kd) :=
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (elemRegs.drop 42) ++
  expo1KindsAt (.s .ni) (List.range' 3687 40) ++
  expo1KindsAt (.pr .pw) [8026] ++
  expo1KindsAt (.pr .fl) [8024] ++
  expo1KindsAt (.pr .ni) [8066]

@[irreducible] def eL3 : List (Nat × Kd) :=
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (elemRegs.drop 62) ++
  expo1KindsAt (.s .ni) (List.range' 3687 62) ++
  expo1KindsAt (.pr .pw) [8026] ++
  expo1KindsAt (.pr .fl) [8024]

@[irreducible] def eL4 : List (Nat × Kd) :=
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (elemRegs.drop 84) ++
  expo1KindsAt (.s .ni) (List.range' 3687 82) ++
  expo1KindsAt (.pr .pw) [8026] ++
  expo1KindsAt (.pr .fl) [8024] ++
  expo1KindsAt (.pr .ni) [8109]

@[irreducible] def eL5 : List (Nat × Kd) :=
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (elemRegs.drop 106) ++
  expo1KindsAt (.s .ni) (List.range' 3687 104) ++
  expo1KindsAt (.pr .pw) [8026] ++
  expo1KindsAt (.pr .fl) [8024] ++
  expo1KindsAt (.pr .ni) [8130]

@[irreducible] def eL6 : List (Nat × Kd) :=
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) [3618, 3619] ++
  expo1KindsAt (.s .ni) (List.range' 3687 126) ++
  expo1KindsAt (.pr .pw) [8026] ++
  expo1KindsAt (.pr .fl) [8024]

@[irreducible] def eL7 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 29) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (List.range' 3716 99)

@[irreducible] def eL8 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 37) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (List.range' 3724 91) ++
  expo1KindsAt (.pr .w4) (List.range' 8154 8)

@[irreducible] def eL9 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 64) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (List.range' 3751 64) ++
  expo1KindsAt (.s .w4) [3833, 3834] ++
  expo1KindsAt (.pr .w4) (List.range' 8154 9)

@[irreducible] def eL10 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 77) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (List.range' 3764 51) ++
  expo1KindsAt (.pr .w4) (List.range' 8154 16)

@[irreducible] def eL11 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 96) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (List.range' 3783 32) ++
  expo1KindsAt (.s .w4) [3855] ++
  expo1KindsAt (.pr .w4) (List.range' 8154 20)

@[irreducible] def eL12 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 117) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .ni) (List.range' 3804 11) ++
  expo1KindsAt (.pr .w4) (List.range' 8154 24)

@[irreducible] def eL13 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 128) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.pr .w4) (List.range' 8154 31)

@[irreducible] def eL14 : List (Nat × Kd) :=
  expo1KindsAt (.s .nn) (List.range' 1231 128) ++
  expo1KindsAt (.s .fl) [1230] ++
  expo1KindsAt (.s .w4) (List.range' 3879 16) ++
  expo1KindsAt (.pr .w4) (List.range' 8162 24)

/-- The checks of the pieces of the exponent stretch, one evaluation. -/
theorem expo1_kok (V : Nat → Value) :
    (kOk (kOf expo1K) Gen.expo1_items0 &&
      kNext expo1K Gen.expo1_items0 ((Gen.expo1_facts1 V).map Prod.fst) eL1 &&
      kOk (kOf eL1) Gen.expo1_items1 &&
      kNext eL1 Gen.expo1_items1 ((Gen.expo1_facts2 V).map Prod.fst) eL2 &&
      kOk (kOf eL2) Gen.expo1_items2 &&
      kNext eL2 Gen.expo1_items2 ((Gen.expo1_facts3 V).map Prod.fst) eL3 &&
      kOk (kOf eL3) Gen.expo1_items3 &&
      kNext eL3 Gen.expo1_items3 ((Gen.expo1_facts4 V).map Prod.fst) eL4 &&
      kOk (kOf eL4) Gen.expo1_items4 &&
      kNext eL4 Gen.expo1_items4 ((Gen.expo1_facts5 V).map Prod.fst) eL5 &&
      kOk (kOf eL5) Gen.expo1_items5 &&
      kNext eL5 Gen.expo1_items5 ((Gen.expo1_facts6 V).map Prod.fst) eL6 &&
      kOk (kOf eL6) Gen.expo1_items6 &&
      kNext eL6 Gen.expo1_items6 ((Gen.expo1_facts7 V).map Prod.fst) eL7 &&
      kOk (kOf eL7) Gen.expo1_items7 &&
      kNext eL7 Gen.expo1_items7 ((Gen.expo1_facts8 V).map Prod.fst) eL8 &&
      kOk (kOf eL8) Gen.expo1_items8 &&
      kNext eL8 Gen.expo1_items8 ((Gen.expo1_facts9 V).map Prod.fst) eL9 &&
      kOk (kOf eL9) Gen.expo1_items9 &&
      kNext eL9 Gen.expo1_items9 ((Gen.expo1_facts10 V).map Prod.fst) eL10 &&
      kOk (kOf eL10) Gen.expo1_items10 &&
      kNext eL10 Gen.expo1_items10 ((Gen.expo1_facts11 V).map Prod.fst) eL11 &&
      kOk (kOf eL11) Gen.expo1_items11 &&
      kNext eL11 Gen.expo1_items11 ((Gen.expo1_facts12 V).map Prod.fst) eL12 &&
      kOk (kOf eL12) Gen.expo1_items12 &&
      kNext eL12 Gen.expo1_items12 ((Gen.expo1_facts13 V).map Prod.fst) eL13 &&
      kOk (kOf eL13) Gen.expo1_items13 &&
      kNext eL13 Gen.expo1_items13 ((Gen.expo1_facts14 V).map Prod.fst) eL14) = true := by
  unfold expo1K
  kernel_rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

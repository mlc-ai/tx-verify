-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoB0
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoBA
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoBB
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoBT
public import Kernels.TmlFa4Fwd.Proof.Softmax.SwExpB

@[expose] public section

/-! # The bias round's exponents: the value functions

The values the bias round's exponent stretch computes, for the data table of its P part
(`Data.lean`) and the stretch's proofs: the software `exp2` instances' matches (`mB<pc>`), the
values after each instance (`nextB<k>`, the lane readings `laneY` written over the run's end
values), the start values of the software path's runs (`vB<k>`), and the values after the tail's
unpack at pc 6380 (`nextTA`, `nextTB`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000

/-- The software `exp2` instance at pc 6059. -/
def mB6059 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6059).get (by rfl)

theorem hmB6059 : cuteExp2.matchAt kernel 6059 = some mB6059 := (Option.some_get _).symm

theorem mB6059_regs :
    (mB6059.regOf CuteSlot.y0, mB6059.regOf CuteSlot.y1, mB6059.regOf CuteSlot.x0,
      mB6059.regOf CuteSlot.x1) = (4668, 4671, 1407, 1408) := by decide +kernel

/-- The software `exp2` instance at pc 6091. -/
def mB6091 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6091).get (by rfl)

theorem hmB6091 : cuteExp2.matchAt kernel 6091 = some mB6091 := (Option.some_get _).symm

theorem mB6091_regs :
    (mB6091.regOf CuteSlot.y0, mB6091.regOf CuteSlot.y1, mB6091.regOf CuteSlot.x0,
      mB6091.regOf CuteSlot.x1) = (4674, 4677, 1409, 1410) := by decide +kernel

/-- The software `exp2` instance at pc 6131. -/
def mB6131 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6131).get (by rfl)

theorem hmB6131 : cuteExp2.matchAt kernel 6131 = some mB6131 := (Option.some_get _).symm

theorem mB6131_regs :
    (mB6131.regOf CuteSlot.y0, mB6131.regOf CuteSlot.y1, mB6131.regOf CuteSlot.x0,
      mB6131.regOf CuteSlot.x1) = (4680, 4683, 1423, 1424) := by decide +kernel

/-- The software `exp2` instance at pc 6153. -/
def mB6153 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6153).get (by rfl)

theorem hmB6153 : cuteExp2.matchAt kernel 6153 = some mB6153 := (Option.some_get _).symm

theorem mB6153_regs :
    (mB6153.regOf CuteSlot.y0, mB6153.regOf CuteSlot.y1, mB6153.regOf CuteSlot.x0,
      mB6153.regOf CuteSlot.x1) = (4686, 4689, 1425, 1426) := by decide +kernel

/-- The software `exp2` instance at pc 6193. -/
def mB6193 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6193).get (by rfl)

theorem hmB6193 : cuteExp2.matchAt kernel 6193 = some mB6193 := (Option.some_get _).symm

theorem mB6193_regs :
    (mB6193.regOf CuteSlot.y0, mB6193.regOf CuteSlot.y1, mB6193.regOf CuteSlot.x0,
      mB6193.regOf CuteSlot.x1) = (4692, 4695, 1439, 1440) := by decide +kernel

/-- The software `exp2` instance at pc 6215. -/
def mB6215 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6215).get (by rfl)

theorem hmB6215 : cuteExp2.matchAt kernel 6215 = some mB6215 := (Option.some_get _).symm

theorem mB6215_regs :
    (mB6215.regOf CuteSlot.y0, mB6215.regOf CuteSlot.y1, mB6215.regOf CuteSlot.x0,
      mB6215.regOf CuteSlot.x1) = (4698, 4701, 1441, 1442) := by decide +kernel

/-- The software `exp2` instance at pc 6255. -/
def mB6255 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6255).get (by rfl)

theorem hmB6255 : cuteExp2.matchAt kernel 6255 = some mB6255 := (Option.some_get _).symm

theorem mB6255_regs :
    (mB6255.regOf CuteSlot.y0, mB6255.regOf CuteSlot.y1, mB6255.regOf CuteSlot.x0,
      mB6255.regOf CuteSlot.x1) = (4704, 4707, 1455, 1456) := by decide +kernel

/-- The software `exp2` instance at pc 6277. -/
def mB6277 : SegMatch CuteSlot := (cuteExp2.matchAt kernel 6277).get (by rfl)

theorem hmB6277 : cuteExp2.matchAt kernel 6277 = some mB6277 := (Option.some_get _).symm

theorem mB6277_regs :
    (mB6277.regOf CuteSlot.y0, mB6277.regOf CuteSlot.y1, mB6277.regOf CuteSlot.x0,
      mB6277.regOf CuteSlot.x1) = (4710, 7252, 1457, 1458) := by decide +kernel

/-- The start values of run 0. -/
abbrev vB0 (W : Nat → Value) : Nat → Value := W

/-- The values after the instance at pc 6059. -/
def nextB0 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB0_facts3 U)) (segValsY mB6059 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB0_facts3 U) 1407))
    (laneY (lookupD (Gen.expoBB0_facts3 U) 1408)) ++ [])

def vB1 (W : Nat → Value) : Nat → Value := nextB0 (vB0 W)

/-- The values after the instance at pc 6091. -/
def nextB1 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB1_facts1 U)) (segValsY mB6091 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB1_facts1 U) 1409))
    (laneY (lookupD (Gen.expoBB1_facts1 U) 1410)) ++ [])

def vB2 (W : Nat → Value) : Nat → Value := nextB1 (vB1 W)

/-- The values after the instance at pc 6131. -/
def nextB2 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB2_facts1 U)) (segValsY mB6131 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB2_facts1 U) 1423))
    (laneY (lookupD (Gen.expoBB2_facts1 U) 1424)) ++ [])

def vB3 (W : Nat → Value) : Nat → Value := nextB2 (vB2 W)

/-- The values after the instance at pc 6153. -/
def nextB3 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB3_facts1 U)) (segValsY mB6153 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB3_facts1 U) 1425))
    (laneY (lookupD (Gen.expoBB3_facts1 U) 1426)) ++ [])

def vB4 (W : Nat → Value) : Nat → Value := nextB3 (vB3 W)

/-- The values after the instance at pc 6193. -/
def nextB4 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB4_facts1 U)) (segValsY mB6193 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB4_facts1 U) 1439))
    (laneY (lookupD (Gen.expoBB4_facts1 U) 1440)) ++ [])

def vB5 (W : Nat → Value) : Nat → Value := nextB4 (vB4 W)

/-- The values after the instance at pc 6215. -/
def nextB5 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB5_facts1 U)) (segValsY mB6215 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB5_facts1 U) 1441))
    (laneY (lookupD (Gen.expoBB5_facts1 U) 1442)) ++ [])

def vB6 (W : Nat → Value) : Nat → Value := nextB5 (vB5 W)

/-- The values after the instance at pc 6255. -/
def nextB6 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB6_facts1 U)) (segValsY mB6255 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB6_facts1 U) 1455))
    (laneY (lookupD (Gen.expoBB6_facts1 U) 1456)) ++ [])

def vB7 (W : Nat → Value) : Nat → Value := nextB6 (vB6 W)

/-- The values after the instance at pc 6277. -/
def nextB7 (U : Nat → Value) : Nat → Value :=
  valueEx (lookupD (Gen.expoBB7_facts1 U)) (segValsY mB6277 CuteSlot.y0 CuteSlot.y1
    (laneY (lookupD (Gen.expoBB7_facts1 U) 1457))
    (laneY (lookupD (Gen.expoBB7_facts1 U) 1458)) ++ [])

def vB8 (W : Nat → Value) : Nat → Value := nextB7 (vB7 W)

/-- The values after the unpack at pc 6380 (path A). -/
abbrev nextTA (U : Nat → Value) : Nat → Value :=
  Function.update (lookupD (Gen.expoBTA0_facts3 U)) 4905
    (splitValue 64 (lookupD (Gen.expoBTA0_facts3 U) 9556)).1

/-- The values after the unpack at pc 6380 (path B). -/
abbrev nextTB (U : Nat → Value) : Nat → Value :=
  Function.update (lookupD (Gen.expoBTB0_facts3 U)) 4905
    (splitValue 64 (lookupD (Gen.expoBTB0_facts3 U) 9556)).1

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

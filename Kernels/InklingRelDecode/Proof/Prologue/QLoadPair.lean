-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Gen.StepPrologue
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow

def qDst (i : Fin 64) : Nat := if i.val = 0 then 198 else 199 + i.val

def qMove (i : Fin 64) : Instr :=
  ⟨none, .move ⟨.scalar, .int .u 16, [some (qDst i)], [.reg 199]⟩⟩

def qLoad (i : Fin 64) : Instr :=
  ⟨some (81 + i.val / 16, false), .mem
    { kind := .load, space := some .global, sem := .weak, elem := .int .b 16,
      addr := ⟨.reg (2077 + i.val) 64, 0⟩, dsts := [some (qDst i)] }⟩

/-- Each query load is preceded by a local move into its destination. -/
theorem qLoadPair {L : Launch} {g : Nat} (i : Fin 64) :
    PcLocal kernel Assumptions.all L g (387 + 2 * i.val) (qMove i) ∧
      kernel.code[388 + 2 * i.val]? = some (qLoad i) := by
  fin_cases i
  · exact ⟨Flow.step_387, Flow.code_388⟩
  · exact ⟨Flow.step_389, Flow.code_390⟩
  · exact ⟨Flow.step_391, Flow.code_392⟩
  · exact ⟨Flow.step_393, Flow.code_394⟩
  · exact ⟨Flow.step_395, Flow.code_396⟩
  · exact ⟨Flow.step_397, Flow.code_398⟩
  · exact ⟨Flow.step_399, Flow.code_400⟩
  · exact ⟨Flow.step_401, Flow.code_402⟩
  · exact ⟨Flow.step_403, Flow.code_404⟩
  · exact ⟨Flow.step_405, Flow.code_406⟩
  · exact ⟨Flow.step_407, Flow.code_408⟩
  · exact ⟨Flow.step_409, Flow.code_410⟩
  · exact ⟨Flow.step_411, Flow.code_412⟩
  · exact ⟨Flow.step_413, Flow.code_414⟩
  · exact ⟨Flow.step_415, Flow.code_416⟩
  · exact ⟨Flow.step_417, Flow.code_418⟩
  · exact ⟨Flow.step_419, Flow.code_420⟩
  · exact ⟨Flow.step_421, Flow.code_422⟩
  · exact ⟨Flow.step_423, Flow.code_424⟩
  · exact ⟨Flow.step_425, Flow.code_426⟩
  · exact ⟨Flow.step_427, Flow.code_428⟩
  · exact ⟨Flow.step_429, Flow.code_430⟩
  · exact ⟨Flow.step_431, Flow.code_432⟩
  · exact ⟨Flow.step_433, Flow.code_434⟩
  · exact ⟨Flow.step_435, Flow.code_436⟩
  · exact ⟨Flow.step_437, Flow.code_438⟩
  · exact ⟨Flow.step_439, Flow.code_440⟩
  · exact ⟨Flow.step_441, Flow.code_442⟩
  · exact ⟨Flow.step_443, Flow.code_444⟩
  · exact ⟨Flow.step_445, Flow.code_446⟩
  · exact ⟨Flow.step_447, Flow.code_448⟩
  · exact ⟨Flow.step_449, Flow.code_450⟩
  · exact ⟨Flow.step_451, Flow.code_452⟩
  · exact ⟨Flow.step_453, Flow.code_454⟩
  · exact ⟨Flow.step_455, Flow.code_456⟩
  · exact ⟨Flow.step_457, Flow.code_458⟩
  · exact ⟨Flow.step_459, Flow.code_460⟩
  · exact ⟨Flow.step_461, Flow.code_462⟩
  · exact ⟨Flow.step_463, Flow.code_464⟩
  · exact ⟨Flow.step_465, Flow.code_466⟩
  · exact ⟨Flow.step_467, Flow.code_468⟩
  · exact ⟨Flow.step_469, Flow.code_470⟩
  · exact ⟨Flow.step_471, Flow.code_472⟩
  · exact ⟨Flow.step_473, Flow.code_474⟩
  · exact ⟨Flow.step_475, Flow.code_476⟩
  · exact ⟨Flow.step_477, Flow.code_478⟩
  · exact ⟨Flow.step_479, Flow.code_480⟩
  · exact ⟨Flow.step_481, Flow.code_482⟩
  · exact ⟨Flow.step_483, Flow.code_484⟩
  · exact ⟨Flow.step_485, Flow.code_486⟩
  · exact ⟨Flow.step_487, Flow.code_488⟩
  · exact ⟨Flow.step_489, Flow.code_490⟩
  · exact ⟨Flow.step_491, Flow.code_492⟩
  · exact ⟨Flow.step_493, Flow.code_494⟩
  · exact ⟨Flow.step_495, Flow.code_496⟩
  · exact ⟨Flow.step_497, Flow.code_498⟩
  · exact ⟨Flow.step_499, Flow.code_500⟩
  · exact ⟨Flow.step_501, Flow.code_502⟩
  · exact ⟨Flow.step_503, Flow.code_504⟩
  · exact ⟨Flow.step_505, Flow.code_506⟩
  · exact ⟨Flow.step_507, Flow.code_508⟩
  · exact ⟨Flow.step_509, Flow.code_510⟩
  · exact ⟨Flow.step_511, Flow.code_512⟩
  · exact ⟨Flow.step_513, Flow.code_514⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue

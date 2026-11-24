-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaRead

@[expose] public section

/-! CLC arbitration and the CLC response stages change no Tensor Memory result, source, or read
rule. This frame is proved through the result derivation, including accumulation. -/
namespace PTX.TcMma
noncomputable section
variable {L : Launch} {A : List Assumption} {X : Execution}

 theorem Result.with_clc {i : EvId} {cell : Cell} {value : Value}
    (h : Result L A X i cell value) (state : Clc.State) (C : EvId → Clc.Effects) :
    Result L A {X with clcState := state, clc := C} i cell value := by
  induction h with
  | overwrite hi hp hr hv => exact .overwrite hi hp hr hv
  | accumulate hi hp hr _ hs hv ih => exact .accumulate hi hp hr ih hs hv
  | accumulateStored hi hp hr hs ho hv => exact .accumulateStored hi hp hr hs ho hv

 theorem result_clc (state : Clc.State) (C : EvId → Clc.Effects) {i : EvId} {cell : Cell}
    {value : Value} :
    Result L A {X with clcState := state, clc := C} i cell value ↔ Result L A X i cell value :=
  ⟨fun h => h.with_clc X.clcState X.clc,fun h => h.with_clc state C⟩

 theorem shiftValue_clc (state : Clc.State) (C : EvId → Clc.Effects) {sh : EvId} {cell : Cell}
    {value : Value} :
    ShiftValue L A {X with clcState := state, clc := C} sh cell value ↔
      ShiftValue L A X sh cell value := by
  simp only [ShiftValue, result_clc, ShiftSource]
  rfl

 theorem wrote_clc (state : Clc.State) (C : EvId → Clc.Effects) {source : EvId} {cell : Cell}
    {value : Value} :
    Wrote L A {X with clcState := state, clc := C} source cell value ↔
      Wrote L A X source cell value := by
  simp only [Wrote, result_clc, shiftValue_clc]
  rfl

 theorem readSource_clc (state : Clc.State) (C : EvId → Clc.Effects)
    {k : TmemRead} {source e : EvId} {cell : Cell} :
    ReadSource L {X with clcState := state, clc := C} k source e cell ↔
      ReadSource L X k source e cell := by
  simp only [ReadSource]
  rfl

 theorem loadReadOk_clc (state : Clc.State) (C : EvId → Clc.Effects) :
    LoadReadOk L A {X with clcState := state, clc := C} ↔ LoadReadOk L A X := by
  simp only [LoadReadOk, readSource_clc, wrote_clc]
  rfl

 theorem aReadOk_clc (state : Clc.State) (C : EvId → Clc.Effects) :
    AReadOk L A {X with clcState := state, clc := C} ↔ AReadOk L A X := by
  simp only [AReadOk, readSource_clc, wrote_clc]
  rfl

 theorem readOk_clc (state : Clc.State) (C : EvId → Clc.Effects) :
    ReadOk L A {X with clcState := state, clc := C} ↔ ReadOk L A X := by
  simp only [ReadOk, loadReadOk_clc, aReadOk_clc]

end
end PTX.TcMma

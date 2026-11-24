-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access
public import Core.Tc.TcMmaRead

@[expose] public section

section
/-! Rebuilding an opaque CLC response from all sixteen of its actual bytes
preserves both its request identity and its cancellation result. These facts
are purely local value reconstruction, independent of memory visibility. -/
namespace PTX
noncomputable section

theorem rebuild_clc (r : ClcResponse) :
    rebuild 3 ((Value.clc r).toBytes.map some) = .ok (.clc r) := by
  have he : (Value.clc r).toBytes.map some =
      some (Value.clc r,0) ::
        (List.range 15).map (fun k => some ((Value.clc r).byteAt (k+1))) := by
    simp [Value.toBytes,Value.bytes,List.range_succ_eq_map,Value.byteAt]
  rw [he]
  simp only [rebuild]
  rw [ite_eq_left ⟨by simp [Value.bytes],he.symm⟩]
  rfl

theorem rebuild_clc_of_bytes {r : ClcResponse} {bs : List (Option Byte)}
    (hbs : bs = (Value.clc r).toBytes.map some) : rebuild 3 bs = .ok (.clc r) := by
  rw [hbs]
  exact rebuild_clc r

end
end PTX
end

section
/-! CLC replica-effect recording changes no Tensor Memory result, source, or read rule.
This frame is proved through the result derivation, including accumulation. -/
namespace PTX.TcMma
noncomputable section
variable {L : Launch} {A : List Assumption} {X : Execution}

 theorem Result.with_clcEffects {i : EvId} {cell : Cell} {value : Value}
    (h : Result L A X i cell value) (effects : EvId → Clc.Effects) :
    Result L A {X with clc := effects} i cell value := by
  induction h with
  | overwrite hi hp hr hv => exact .overwrite hi hp hr hv
  | accumulate hi hp hr _ hs hv ih => exact .accumulate hi hp hr ih hs hv
  | accumulateStored hi hp hr hs ho hv => exact .accumulateStored hi hp hr hs ho hv

 theorem result_clcEffects (effects : EvId → Clc.Effects) {i : EvId} {cell : Cell}
    {value : Value} :
    Result L A {X with clc := effects} i cell value ↔ Result L A X i cell value :=
  ⟨fun h => h.with_clcEffects X.clc,fun h => h.with_clcEffects effects⟩

 theorem shiftValue_clcEffects (effects : EvId → Clc.Effects)
    {sh : EvId} {cell : Cell} {value : Value} :
    ShiftValue L A {X with clc := effects} sh cell value ↔
      ShiftValue L A X sh cell value := by
  simp only [ShiftValue, result_clcEffects, ShiftSource]
  rfl

 theorem wrote_clcEffects (effects : EvId → Clc.Effects)
    {source : EvId} {cell : Cell} {value : Value} :
    Wrote L A {X with clc := effects} source cell value ↔
      Wrote L A X source cell value := by
  simp only [Wrote, result_clcEffects, shiftValue_clcEffects]
  rfl

 theorem readSource_clcEffects (effects : EvId → Clc.Effects)
    {k : TmemRead} {source e : EvId} {cell : Cell} :
    ReadSource L {X with clc := effects} k source e cell ↔
      ReadSource L X k source e cell := by
  simp only [ReadSource]
  rfl

 theorem loadReadOk_clcEffects (effects : EvId → Clc.Effects) :
    LoadReadOk L A {X with clc := effects} ↔ LoadReadOk L A X := by
  simp only [LoadReadOk, readSource_clcEffects, wrote_clcEffects]
  rfl

 theorem aReadOk_clcEffects (effects : EvId → Clc.Effects) :
    AReadOk L A {X with clc := effects} ↔ AReadOk L A X := by
  simp only [AReadOk, readSource_clcEffects, wrote_clcEffects]
  rfl

 theorem readOk_clcEffects (effects : EvId → Clc.Effects) :
    ReadOk L A {X with clc := effects} ↔ ReadOk L A X := by
  simp only [ReadOk, loadReadOk_clcEffects, aReadOk_clcEffects]

end
end PTX.TcMma
end

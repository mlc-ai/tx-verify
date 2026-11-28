-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Base
public import Lemmas.Flow.TypedIntG
import Kernels.InklingRelDecode.Flow.Code.Part044

@[expose] public section

/-! # The unpack between two word stores

The `mov.b64 {a, b} = rd` before every second store (pcs `2753 + 3m`) is a typed piece of the lane
whose written registers hold none of the control facts. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value}

/-- The pc of the `m`-th unpack. -/
def uPc (m : Fin 31) : Nat := 2753 + 3 * m.val

/-- The registers the abstract run of the unpack writes. -/
def uW (m : Fin 31) : List Nat := wrF absF5 (lateQt (uPc m)) ((kernel.code.drop (uPc m)).take 1)

theorem unpack_ok : ∀ m : Fin 31, checkW absF5 lateQt (uPc m) (uPc m + 1)
    ((kernel.code.drop (uPc m)).take (uPc m + 1 - uPc m)) (uW m) = true ∧
    epiOk (uPc m) (uPc m + 1) = true ∧ (∀ r ∈ ctlLive (uPc m + 1), r ∉ uW m) ∧
    (∀ r ∈ ctlLive (uPc m + 1), r ∈ ctlLive (uPc m - 1)) := by decide +kernel

/-- **The unpack before the stores `2m + 1` and `2m + 2`** keeps the control facts. -/
theorem unpack_span (m : Fin 31) (R : TState → Prop) :
    SegQ kernel Assumptions.all L g (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t)
      (uPc m) (facts e L g v (uPc m - 1)) (uPc m + 1) (facts e L g v (uPc m + 1)) := by
  obtain ⟨hc, hp, hw, hs⟩ := unpack_ok m
  refine SegQ.tauAll R (segQF5_runW lateQt (by omega) ?_ (fp3_epi hp) hc ?_ ?_)
  · have := kernel_code_length
    change uPc m + 1 ≤ kernel.code.length
    unfold uPc
    omega
  · intro p hp'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp'
    exact hw r hr
  · intro p hp'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp'
    exact mem_factsFrom (hs r hr)

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict

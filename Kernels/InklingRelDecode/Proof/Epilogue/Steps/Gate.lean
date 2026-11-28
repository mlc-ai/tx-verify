-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Store
import Kernels.InklingRelDecode.Gen.StepEpilogue03
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Value}
local notation "F" => facts e L g v
local notation "dst" => firstStore e.valid (lead (g%L.block))

private theorem select_row : SegU kernel Assumptions.all L g 2678 (F 2678) 2682 (F 2682) := by
  have mask : Seg kernel Assumptions.all L g 1 2678 (F 2678) 2679 (F 2679) := by
    intro t ht; seg_fp ht using rfl
  have cmp : Seg kernel Assumptions.all L g 1 2679 (F 2679) 2680 (F 2680) := by
    intro t ht; seg_fp ht using rfl
  have data : SegU kernel Assumptions.all L g 2680 (F 2680) 2681 (F 2681) :=
    Lib.control_span (by decide +kernel)
  have both : Seg kernel Assumptions.all L g 1 2681 (F 2681) 2682 (F 2682) := by
    intro t ht; seg_fp ht using rfl
  exact (SegU.of_seg (mask.comp cmp)).comp (data.comp (SegU.of_seg both))

private theorem masked_lse (h : (lead (g%L.block) && e.valid)=false) :
    SegU kernel Assumptions.all L g 2682 (F 2682) 2751 (F 2751) := by
  obtain ⟨a,ins,_,_,_⟩ := store_fetch (by decide +kernel : storeCheck 2682 174=true)
  have hv : valueOf e L g v 174 = .pred false := congrArg Value.pred h
  exact (SegU.of_seg (Seg.guardSkip ins (mem_factsFrom_eq (by decide : 174 ∈ ctlLive 2682) hv)
    rfl)).comp addr_from_lse

theorem store_gate :
    SegU kernel Assumptions.all L g 2674 (F 2674) (dst).pc (F (dst).pc) := by
  apply addr_head.comp
  apply select_row.comp
  cases ok : e.valid
  · simp only [firstStore,Bool.false_eq_true,↓reduceIte]
    exact (masked_lse (by simp [ok])).comp (skip_stores (n := 0) ok (by decide))
  · cases lane : lead (g%L.block)
    · simp only [firstStore,Bool.false_eq_true,↓reduceIte]
      exact masked_lse (by simp [lane])
    · simp only [firstStore,↓reduceIte]
      exact fun t ht => .inl ⟨t,.refl,ht⟩

theorem step_waitLd : (code e L g).StepAtU ⟨.waitLd,v⟩ := by
  apply straight (s := .waitLd) (z := dst) Flow.code_2608 rfl (fun _ => trivial)
    (fun _ => fires_async_next trivial) (fun _ => rfl) (fun _ => first_inv ..)
  exact (Lib.control_span (by decide +kernel : Lib.spanCheck ctlLive 2608 2609 2674)).comp
    store_gate

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control

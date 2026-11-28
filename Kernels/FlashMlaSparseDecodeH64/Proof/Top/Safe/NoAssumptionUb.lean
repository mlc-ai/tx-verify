-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NcAlloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.GlobalCls

@[expose] public section

/-! # the assumptions' conditions: no assumption declares the execution unsafe

The safety class of Core's `Unsafe` this file owns (`a.ub`). Of the kernel's assumptions only
the read-only declaration of the `.nc` loads (`Assumptions.ncReadOnly`) has a condition: no
operation writes a byte an `.nc` load of the declared sites covers. The `.nc` loads read the
launch's length arrays, the sink and the index rows, whose bytes `Pre` places apart from the two
buffers the kernel writes (`nc_alloc`: `NcRead.apart`), and every write of the kernel to a global
byte is to one of those two buffers (`global_at`). Nothing is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **No write to an `.nc` read's byte**: the read-only declaration's condition fails. -/
theorem Safe.noNcWrite (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ Assumptions.ncReadOnly.ub L mem0 X := by
  rintro ⟨⟨g, k⟩, pc, a, bs, w, a', l, he, -, hc, hi, hc'⟩
  have hR := nc_alloc hp hX hFw hnu he rfl l hc
  have hs : l.space ≠ .shared := by rw [hR.space]; decide
  cases global_at hp hX hFw hnu hi hc' hs with
  | lse _ _ hl _ _ => exact hR.apart.2 hl
  | store _ _ _ _ _ _ _ _ hl => exact hR.apart.1 hl

/-- **the assumptions' conditions**: no assumption declares the execution unsafe. -/
theorem Safe.noAssumptionUb (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ ∃ a ∈ Assumptions.all, a.ub L mem0 X := by
  rintro ⟨a, ha, hu⟩
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact (show False from hu)
    | exact Safe.noNcWrite hp hX hFw hnu hu

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

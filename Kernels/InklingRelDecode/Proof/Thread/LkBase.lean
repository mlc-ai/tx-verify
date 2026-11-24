-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompAll
public import Kernels.InklingRelDecode.Proof.Thread.WCompAll
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-!
# Warp lockstep: the synchronizing instructions of the program

A *synchronizing* instruction fires an event on which the lanes of a warp (or the threads of a CTA)
meet: a named barrier, a warp collective (`shfl.sync`, `elect.sync`, `bar.warp.sync`), a `tcgen05`
collective (the allocator operations, the loads and stores and their waits), a register request.
`syPcs` lists their positions in the decoded program (checked by `decide +kernel`: the list is
exactly the instructions of those forms), `nsync pc` is the first of them at or after `pc`.

The key of a state of a machine whose code runs forward (the common start, the prologue, the
epilogue) is `nsync` of its position, past the sub-step of a two-step instruction. The machines
with loops have a key by site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The instruction fires a synchronizing event. -/
def syOp : Op → Bool
  | .setMaxReg .. | .barSync .. | .barSyncN .. | .barArrive .. | .warp _ | .tcAlloc ..
  | .tcDealloc .. | .tcRelinquish .. | .tcLd .. | .tcWaitLd | .tcSt .. | .tcWaitSt => true
  | _ => false

/-- The positions of the synchronizing instructions of the program. -/
def syPcs : List Nat :=
  [11, 12, 14, 15, 17, 27, 130, 135, 139, 143, 147, 151, 155, 159, 163, 167, 171, 175, 180, 192,
    201, 202, 203, 212, 213, 222, 223, 227, 228, 236, 243, 244, 245, 254, 255, 264, 265, 269,
    270, 278, 285, 286, 287, 296, 297, 306, 307, 311, 312, 573, 574, 575, 999, 1009, 1010, 1012,
    1261, 1265, 1298, 1838, 2234, 2241, 2242, 2244, 2246, 2248, 2251, 2253, 2255, 2260, 2261,
    2326, 2328, 2329, 2333, 2334, 2335, 2336, 2337, 2338, 2344, 2346, 2377, 2387, 2388, 2392,
    2393, 2401, 2403, 2407, 2409, 2419, 2420, 2422, 2424, 2461, 2464, 2466, 2477, 2509, 2512,
    2514, 2525, 2550, 2551, 2554, 2555, 2557, 2558, 2603, 2607, 2608, 2846, 2847, 2849, 2850,
    2851, 2853, 2854]

/-- Every synchronizing instruction is listed. -/
theorem kernel_syPcs : OpPcsFast kernel.code syOp syPcs = true := by decide +kernel

/-- The position is a synchronizing instruction. -/
def syPc (pc : Nat) : Bool := syPcs.contains pc

/-- The first synchronizing position at or after `pc`. -/
def nsync (pc : Nat) : Nat := (syPcs.find? (fun q => decide (pc ≤ q))).getD pc

/-- The position of the next event of a state with sub-step `sub` at `pc`: the second step of a
two-step instruction is followed by the next instruction. -/
def keyPc (pc sub : Nat) : Nat := nsync (if sub = 0 then pc else pc + 1)

/-- The state's event is synchronizing. -/
def syAt (pc sub : Nat) : Bool := syPc pc && decide (sub = 0)

theorem nsync_all : syPcs.all (fun pc => nsync pc == pc) = true := by decide +kernel

theorem nsync_of_sy {pc : Nat} (h : syPc pc = true) : nsync pc = pc := by
  have h1 := List.all_eq_true.mp nsync_all pc (List.contains_iff_mem.mp h)
  simpa using h1

theorem syAt_key {pc sub : Nat} (h : syAt pc sub = true) : keyPc pc sub = pc := by
  simp only [syAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, rfl⟩ := h
  simp only [keyPc, ↓reduceIte]
  exact nsync_of_sy h1

end
end PTX.Kernels.InklingRelDecode.Proof.Lk

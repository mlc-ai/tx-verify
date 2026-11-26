-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.Entry
public import Kernels.FlashKdaFwd.Proof.Thread.ParamBridge
import Kernels.FlashKdaFwd.Flow.Code

@[expose] public section

/-! # The entry of the thread machine, and its launch facts

From a thread's first state, local steps reach its first site with the file `init` states
(`start`). The launch facts the machine needs (`Launched`: the scalar parameters the code loads
and two fields of by-value parameter objects) follow from the specification's precondition
(`Launched.of_pre`), so the step obligations and the entry need the precondition only. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

/-- A field of four bytes the launch gives as an integer is supplied. -/
theorem supplied_of_intBytes {x : Nat} {p : String} (h : intBytes x 128 p L) :
    ParamSupplied L p 128 (32 / 8) :=
  fun k hk => ⟨_, h k hk⟩

/-- **The launch facts of the thread machine hold under the specification's precondition.** -/
theorem Launched.of_pre {P : Params} {mem0 : Mem0} (h : Pre P L mem0) : Launched L where
  param := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [paramName_11]; exact h.paramOutput⟩
    · exact ⟨_, by rw [paramName_12]; exact h.paramTokens⟩
    · exact ⟨_, by rw [paramName_13]; exact h.paramHeads⟩
    · exact ⟨_, by rw [paramName_15]; exact h.paramOffsets⟩
    · exact ⟨_, by rw [paramName_16]; exact h.paramTiles⟩
  obj := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨_, _, by rw [paramName_0]; exact h.object0, by decide, by decide⟩
    · exact ⟨_, _, by rw [paramName_10]; exact h.object10, by decide, by decide⟩
  bytes := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rw [paramName_0]; exact supplied_of_intBytes h.scaleV
    · rw [paramName_10]; exact supplied_of_intBytes h.scaleOut

/-- A thread's first site is a first event: sub-step 0. -/
theorem init_sub (L : Launch) (g : Nat) : (init L g).site.sub = 0 := by
  simp only [init, entry]
  split_ifs <;> rfl

/-- A thread's first site is a first event: an empty accumulator. -/
theorem init_acc (L : Launch) (g : Nat) : (init L g).site.acc = [] := by
  simp only [init, entry]
  split_ifs <;> rfl

set_option maxRecDepth 100000 in
/-- **The entry**: three pieces. The eleven parameter addresses (instructions 0 to 10,
evaluated), the scalar parameter load (instruction 11, from the launch fact, `seg_ldParam`), and
the role computation with its two `selp`s and two branches on the thread index (`seg_sym`, the
branches decided by the conditions of `entry`). On the path of the low threads the walk is cut
after the branch at instruction 22: both ways from there reach instruction 48 in seven steps,
which `seg_fp` does not accept as one piece. -/
theorem start (hL : Launched L) (_hg : g < L.threads) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all L g) {} t ∧
      (code L g).AtD (code L g).init t ∧ (code L g).inv (code L g).init := by
  have hx : L.params (paramName 15) = some (paramBits L 15) := hL.p15
  have key : ∀ d : D, d = init L g → ∃ n, Seg kernel Assumptions.all L g n 12
      ((2262, .bits 64 (truncBits 64 (paramBits L 15))) :: factsAt 11 d) d.site.pc
      (facts d) := by
    intro d hd
    simp only [init, entry] at hd
    split_ifs at hd with h6 h7
    · refine Seg.comp_ex (q := 42) (H := factsAt 42 d) ?_ ?_ <;> subst hd <;>
        seg_sym using th_seg
    · subst hd; seg_sym using th_seg
    · subst hd; seg_sym using th_seg
  obtain ⟨n, hC⟩ := key _ rfl
  have hA : Seg kernel Assumptions.all L g 11 0 [] 11 (factsAt 11 (init L g)) := by
    th_seg
  have hB := seg_ldParam (L := L) (g := g) (F := factsAt 11 (init L g)) Flow.code_11 hx
    (not_mem_factsFrom (by lit_not_mem)) (by asms_none) segFree
  obtain ⟨t, hr, ht⟩ := ((hA.comp hB).comp hC) {} at_init
  exact ⟨t, run_rtg hr, ⟨ht.1, ht.2.1.trans (init_sub L g).symm, ht.2.2.1.trans (init_acc L g).symm,
    ht.2.2.2.1, ht.2.2.2.2⟩, trivial⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Thread

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OpPcs

@[expose] public section

/-! # Where a kind of instruction occurs, decided in one pass

`OpPcs` decides on the code that every instruction of a kind is at a listed position, reading
each position of the list in turn (quadratic in the code's length, so the kernel's decision takes
tens of seconds). `OpPcsFast` scans the code once, and `decide +kernel` checks it in a fraction
of a second; `OpPcsFast.mem` is `OpPcs.mem` for it. -/

namespace PTX.Flow

/-- Every instruction `p` selects is at a position in `l`, decided in one pass. -/
def OpPcsFast (code : List Instr) (p : Op → Bool) (l : List Nat) : Bool :=
  code.zipIdx.all fun x => !p x.1.op || l.contains x.2

theorem OpPcsFast.mem {code : List Instr} {p : Op → Bool} {l : List Nat}
    (h : OpPcsFast code p l = true) {pc : Nat} {ins : Instr} (hc : code[pc]? = some ins)
    (hp : p ins.op = true) : pc ∈ l := by
  have hmem : (ins, pc) ∈ code.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using hc
  have h' := List.all_eq_true.mp h (ins, pc) hmem
  simp only [hp, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h'
  exact h'

/-- The one-pass decision gives `OpPcs`. -/
theorem OpPcsFast.opPcs {code : List Instr} {p : Op → Bool} {l : List Nat}
    (h : OpPcsFast code p l = true) : OpPcs code p l = true := by
  unfold OpPcs
  refine List.all_eq_true.mpr fun pc hpc => ?_
  rcases hc : code[pc]? with _ | ins
  · rfl
  · cases hp : p ins.op
    · simp [hp]
    · simpa [hp] using OpPcsFast.mem h hc hp

end PTX.Flow

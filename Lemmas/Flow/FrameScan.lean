-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReachFrameGuard

@[expose] public section

/-! # A frame set checked by one scan of the code

A proof tool, generic over the kernel. `frameSetG` looks up each position of its set in the code,
which the kernel evaluates slowly; `scanOk` checks the same conditions over the code list of each
interval of a set in one pass (`frameSetG_of_scan`), the set being the union of the intervals
`(lo, n)`. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel}

/-- A position in one of the intervals `(lo, n)`. -/
def inIvs (ivs : List (Nat × Nat)) (q : Nat) : Bool :=
  ivs.any fun p => decide (p.1 ≤ q ∧ q < p.1 + p.2)

/-- The positions of the intervals. -/
def pcsOf (ivs : List (Nat × Nat)) : List Nat := ivs.flatMap fun p => List.range' p.1 p.2

theorem pcsOf_contains (ivs : List (Nat × Nat)) (q : Nat) :
    (pcsOf ivs).contains q = inIvs ivs q := by
  rw [Bool.eq_iff_iff]
  simp only [pcsOf, inIvs, List.contains_iff_mem, List.mem_flatMap, List.mem_range',
    List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, i, hi, rfl⟩
    exact ⟨a, ha, by omega, by omega⟩
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨a, ha, q - a.1, by omega, by omega⟩

/-- The conditions of `frameSetG` at one position, on the instruction there. -/
def scanAt (K : Kernel) (ivs : List (Nat × Nat)) (rs : List Nat) (ins : Instr) (pc : Nat) :
    Bool :=
  (if ins.op.isLocal then noBrx ins.op && rs.all (fun r => !(writesRegs ins.op).contains r)
    && [nextPc ins.op pc].all fun q => inIvs ivs q || evAtB K q
  else ins.guard.isSome) && [pc + 1].all fun q => inIvs ivs q || evAtB K q

/-- **One pass over the code of each interval.** -/
def scanOk (K : Kernel) (ivs : List (Nat × Nat)) (rs : List Nat) : Bool :=
  ivs.all fun p => decide (p.1 + p.2 ≤ K.code.length) &&
    (((K.code.drop p.1).take p.2).zipIdx p.1).all fun x => scanAt K ivs rs x.1 x.2

theorem frameSetG_of_scan {ivs : List (Nat × Nat)} {rs : List Nat}
    (h : scanOk K ivs rs = true) : frameSetG K (pcsOf ivs) rs = true := by
  unfold frameSetG
  simp only [List.all_eq_true]
  intro pc hpc
  obtain ⟨p, hp, hq⟩ : ∃ p ∈ ivs, p.1 ≤ pc ∧ pc < p.1 + p.2 := by
    have : inIvs ivs pc = true := by rw [← pcsOf_contains]; exact List.contains_iff_mem.mpr hpc
    simpa [inIvs] using this
  have hp' := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hlt : pc < K.code.length := by omega
  have hc : K.code[pc]? = some K.code[pc] := List.getElem?_eq_getElem hlt
  have hm : (K.code[pc], pc) ∈ ((K.code.drop p.1).take p.2).zipIdx p.1 := by
    apply List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    refine ⟨hq.1, ?_⟩
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hq.1]
    exact hc
  have := List.all_eq_true.mp hp'.2 _ hm
  simp only [scanAt] at this
  rw [hc]
  simp only [pcsOf_contains]
  exact this

end
end PTX.Flow.Code

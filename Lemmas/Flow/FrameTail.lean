-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReachFrameGuard
public import Lemmas.Flow.FrameScan

@[expose] public section

/-! # A frame set from a later position on

A proof tool, generic over the kernel. A frame set `S0` that writes no register
(`frameSetG K S0 []`), all of whose local steps go forward, gives the frame set of its
positions from `a` on for the registers that no instruction of those positions writes:
`frameSetG_tail`. One check of `S0` serves every `a`. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel}

/-- **One pass over the code of each interval** with a check on the instruction and position. -/
def scanBy (K : Kernel) (ivs : List (Nat × Nat)) (p : Instr → Nat → Bool) : Bool :=
  ivs.all fun iv => decide (iv.1 + iv.2 ≤ K.code.length) &&
    (((K.code.drop iv.1).take iv.2).zipIdx iv.1).all fun x => p x.1 x.2

theorem scanBy_at {ivs : List (Nat × Nat)} {p : Instr → Nat → Bool} (h : scanBy K ivs p = true)
    {pc : Nat} (hp : inIvs ivs pc = true) : ∃ ins, K.code[pc]? = some ins ∧ p ins pc = true := by
  obtain ⟨iv, hiv, hq⟩ : ∃ iv ∈ ivs, iv.1 ≤ pc ∧ pc < iv.1 + iv.2 := by simpa [inIvs] using hp
  have hp' := List.all_eq_true.mp h iv hiv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hlt : pc < K.code.length := by omega
  have hc : K.code[pc]? = some K.code[pc] := List.getElem?_eq_getElem hlt
  have hm : (K.code[pc], pc) ∈ ((K.code.drop iv.1).take iv.2).zipIdx iv.1 := by
    apply List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    refine ⟨hq.1, ?_⟩
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hq.1]
    exact hc
  exact ⟨_, hc, List.all_eq_true.mp hp'.2 _ hm⟩

/-- **The frame set of the positions from `a` on.** -/
theorem frameSetG_tail {S0 rs : List Nat} {a : Nat} (h0 : frameSetG K S0 [] = true)
    (hfwd : ∀ pc ∈ S0, ∀ ins, K.code[pc]? = some ins → ins.op.isLocal = true →
      pc < nextPc ins.op pc)
    (hw : ∀ pc ∈ S0, a ≤ pc → ∀ ins, K.code[pc]? = some ins → ins.op.isLocal = true →
      ∀ r ∈ rs, r ∉ writesRegs ins.op) : frameSetG K (S0.filter (a ≤ ·)) rs = true := by
  have hmem : ∀ q pc, pc ∈ S0 → a ≤ pc → pc < q → (S0.contains q || evAtB K q) = true →
      ((S0.filter (a ≤ ·)).contains q || evAtB K q) = true := by
    intro q pc hp ha hlt h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · refine Bool.or_eq_true_iff.mpr (.inl ?_)
      simp only [List.contains_iff_mem, List.mem_filter, decide_eq_true_eq] at h ⊢
      exact ⟨h, by omega⟩
    · exact Bool.or_eq_true_iff.mpr (.inr h)
  unfold frameSetG
  simp only [List.all_eq_true, List.mem_filter, decide_eq_true_eq]
  rintro pc ⟨hp, ha⟩
  have h1 := List.all_eq_true.mp h0 pc hp
  cases hc : K.code[pc]? with
  | none => rw [hc] at h1; exact h1
  | some ins =>
    rw [hc] at h1
    simp only at h1 ⊢
    by_cases hl : ins.op.isLocal = true
    · simp only [hl, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, List.all_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq] at h1 ⊢
      obtain ⟨⟨⟨hb, -⟩, hn⟩, hq⟩ := h1
      refine ⟨⟨⟨hb, fun r hr => ?_⟩, hmem _ pc hp ha (hfwd pc hp ins hc hl) hn⟩,
        hmem _ pc hp ha (by omega) hq⟩
      simpa using hw pc hp ha ins hc hl r hr
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq] at h1 ⊢
      exact ⟨h1.1, hmem _ pc hp ha (by omega) h1.2⟩

end
end PTX.Flow.Code

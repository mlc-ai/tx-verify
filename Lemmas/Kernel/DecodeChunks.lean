-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode

@[expose] public section

/-! # Decoding a kernel in chunks

`Decode.kernelIn` decodes the instruction list with `Decode.code` against an environment that
`Decode.prepare` computes once from the whole function. These lemmas assemble a decode equation
from equations about consecutive slices of the instruction list, so that each slice can be
checked by its own kernel reduction. -/

namespace PTX.Decode

/-- Decoding a concatenation decodes the first part and then the second part, whose first
instruction has the index after the first part. -/
theorem code_append_ok {env : Env} {pc : Nat} {xs ys : List SourceInstr} {r s : List Instr}
    (h1 : code env pc xs = .ok r) (h2 : code env (pc + xs.length) ys = .ok s) :
    code env pc (xs ++ ys) = .ok (r ++ s) := by
  simp only [code, List.zipIdx_append, List.mapM_append] at h1 h2 ⊢
  rw [h1, h2]
  rfl

/-- One chunk step: the slice of `n` instructions from index `a` and the rest from `a + n`
decode to the matching slices of `R`, so the rest from `a` decodes to the rest of `R`. -/
theorem code_chunk {env : Env} {l : List SourceInstr} {R : List Instr} {a n : Nat}
    (h1 : code env a ((l.drop a).take n) = .ok ((R.drop a).take n))
    (h2 : code env (a + n) (l.drop (a + n)) = .ok (R.drop (a + n))) :
    code env a (l.drop a) = .ok (R.drop a) := by
  rw [← List.take_append_drop n (l.drop a), ← List.take_append_drop n (R.drop a)]
  apply code_append_ok h1
  by_cases hn : n ≤ (l.drop a).length
  · have hl : ((l.drop a).take n).length = n := by
      simp only [List.length_drop] at hn; simp only [List.length_take, List.length_drop]; omega
    rw [hl, List.drop_drop, List.drop_drop]
    exact h2
  · have hd : l.drop (a + n) = [] := List.drop_eq_nil_iff.mpr (by simp at hn; omega)
    have hd' : (l.drop a).drop n = [] := by rw [List.drop_drop]; exact hd
    rw [hd] at h2
    have hR : R.drop (a + n) = [] := by
      simp only [code, List.zipIdx_nil, List.mapM_nil] at h2
      exact (Except.ok.inj h2).symm
    rw [hd', List.drop_drop, hR]
    rfl

/-- One chunk step for a list computed inside `Except`: equal slices from `a` of length `n` and
equal rests from `a + n` give equal rests from `a`. -/
theorem map_drop_chunk {ε β α : Type} {m : Except ε β} {h : β → List α} {L : List α}
    {a n : Nat}
    (h1 : m.map (fun p => ((h p).drop a).take n) = .ok ((L.drop a).take n))
    (h2 : m.map (fun p => (h p).drop (a + n)) = .ok (L.drop (a + n))) :
    m.map (fun p => (h p).drop a) = .ok (L.drop a) := by
  cases m with
  | error e => simp [Except.map] at h1
  | ok p =>
    simp only [Except.map, Except.ok.injEq] at h1 h2 ⊢
    rw [← List.take_append_drop n ((h p).drop a), ← List.take_append_drop n (L.drop a), h1,
      List.drop_drop, List.drop_drop, h2]

/-- `kernelIn` from the parts of `prepare` and the decoded code. -/
theorem kernelIn_of_parts {globals : List (List String)} {f : Syntax.Function} {env : Env}
    {instrs : List SourceInstr} {K : Kernel}
    (hh : (prepare globals f).map (fun p => (p.env, p.header)) = .ok (env, { K with code := [] }))
    (hi : (prepare globals f).map (fun p => p.instrs.drop 0) = .ok (instrs.drop 0))
    (hc : code env 0 (instrs.drop 0) = .ok (K.code.drop 0)) :
    kernelIn globals f = .ok K := by
  cases hp : prepare globals f with
  | error e => simp [hp, Except.map] at hh
  | ok p =>
    rcases p with ⟨penv, pinstrs, pheader⟩
    simp only [hp, Except.map, Except.ok.injEq, Prod.mk.injEq, List.drop_zero] at hh hi hc
    obtain ⟨rfl, rfl⟩ := hh
    subst hi
    simp only [kernelIn, hp, bind, Except.bind, hc, pure, Except.pure]

end PTX.Decode

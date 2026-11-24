-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Mma
public import Kernels.InklingRelDecode.Proof.Thread.MmaBits

@[expose] public section

/-! # Tools of the MMA warp's step lemmas

The segment tactic `ink_seg` with the bit lemmas of the loop, segments of some length (`SegE`),
and the conditional branches on a predicate fact (both guard polarities). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The value-table reduction used after evaluating a segment. -/
macro "ink_values" : tactic =>
  `(tactic| simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- Evaluate a segment from `h` and close the facts of its end state, with the lemmas of the
loop's descriptor and ring arithmetic. -/
syntax "ink_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ink_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      seg_fp $h using
        try ink_values
        all_goals seg_close [mulhi3, Nat.and_one_is_mod, bfe_u32, lor_field, qLo, kLo, vLo,
          desc, vdesc, descHi, $extra,*]))

theorem facts_ne {L : Launch} {pc : Nat} {d : D} {r : Nat} (hr : r ∉ Flow.live pc) :
    ∀ p ∈ factsAt L pc d, p.1 ≠ r := by
  intro p hp he
  simp only [factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r', hr', rfl⟩ := hp
  exact hr (he ▸ hr')

/-- The registers live at a pc are valued by the table of any state with the same loop state:
`factsAt` at another pc, a state at another site. -/
theorem holds_live {R : Nat → Option Value} {L : Launch} {pc pc' : Nat} {d d' : D}
    (h : Holds R (factsAt L pc d)) (hv : valueOf L d = valueOf L d')
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc) : Holds R (factsAt L pc' d') := by
  rw [factsAt, ← hv]
  exact Flow.holds_factsFrom_mono h hl

/-- The facts at `pc'` of a state at another site, when the broadcast tests' predicates are not
live there. -/
theorem holds_site {R : Nat → Option Value} {L : Launch} {pc pc' : Nat} {d : D} {s : Site}
    (h : Holds R (factsAt L pc d))
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc ∧ r ≠ 8 ∧ r ≠ 13) :
    Holds R (factsAt L pc' { d with site := s }) := by
  refine Flow.holds_of_pointwise fun r hr => ?_
  obtain ⟨h1, h8, h13⟩ := hl r hr
  rw [valueOf_site L d s h8 h13]
  exact holds_mem h (Flow.mem_factsFrom h1)

/-- Some number of local steps from `s` with facts `F` reach `b` with facts `G`. -/
def SegE (L : Launch) (g s : Nat) (F : List (Nat × Value)) (b : Nat) (G : List (Nat × Value)) :
    Prop := ∃ n, Seg kernel asms L g n s F b G

theorem SegE.of_seg {L : Launch} {g n s b : Nat} {F G : List (Nat × Value)}
    (h : Seg kernel asms L g n s F b G) : SegE L g s F b G := ⟨n, h⟩

theorem SegE.comp {L : Launch} {g s p b : Nat} {F G H : List (Nat × Value)}
    (h1 : SegE L g s F p G) (h2 : SegE L g p G b H) : SegE L g s F b H := by
  obtain ⟨m, h1⟩ := h1
  obtain ⟨n, h2⟩ := h2
  exact ⟨m + n, h1.comp h2⟩

theorem SegE.weaken_end {L : Launch} {g s b : Nat} {F G G' : List (Nat × Value)}
    (h : SegE L g s F b G) (hG : ∀ R, Holds R G → Holds R G') : SegE L g s F b G' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_end hG⟩

theorem SegE.weaken_start {L : Launch} {g s b : Nat} {F F' G : List (Nat × Value)}
    (h : SegE L g s F b G) (hF : ∀ R, Holds R F' → Holds R F) : SegE L g s F' b G := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_start hF⟩

/-- A segment from the facts at one pc holds from the facts at another pc whose live registers
include the first's, valued by the table of the same loop state. -/
theorem SegE.live_start {L : Launch} {g s s' b : Nat} {d d' : D} {G : List (Nat × Value)}
    (h : SegE L g s (factsAt L s d) b G) (hv : valueOf L d' = valueOf L d)
    (hl : ∀ r ∈ Flow.live s, r ∈ Flow.live s') : SegE L g s (factsAt L s' d') b G :=
  h.weaken_start fun _ hR => holds_live hR hv hl

/-! ### Branches

A conditional branch on a predicate fact, for a guard `@p` (taken when `p` holds) and a guard
`@!p` (taken when it does not). No assumption of the kernel names a branch. -/

theorem asms_bra_none (L : Launch) (g : Nat) (t : TState) (target : Nat) (uni : Bool) :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

/-- No assumption of the kernel takes a segment at a pc outside the software-`exp2` sites. -/
theorem asms_segFree {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc asms pc := by
  intro a ha L g t ht
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · rfl
  · have : pc ∉ Assumptions.emuSites := by simpa using h
    simp [Assumptions.swExp2, ht, this]
  all_goals rfl

/-- `SegFreePc asms pc` for a literal `pc` outside the software-`exp2` sites. -/
macro "asms_free" : tactic => `(tactic| exact asms_segFree (by decide +kernel))

/-- A branch `@!p` on the fact `p = pick`: taken when `p` is false. -/
theorem run_nbra {t : TState} {pc target p : Nat} {F : List (Nat × Value)} {uni : Bool}
    {L : Launch} {g : Nat}
    (hc : kernel.code[pc]? = some ⟨some (p, true), .bra target uni⟩) (pick : Bool)
    (h : At t pc F) (hp : t.regs p = some (.pred pick))
    (hA : Assumption.SegFreePc asms pc := by asms_free) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (if pick then pc + 1 else target) F := by
  cases pick with
  | true =>
    refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind,
      pure, Except.pure]
  | false =>
    refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
      Except.pure, hA.exec, execLocalRule_of_none (asms_bra_none L g t target uni), execLocal,
      Op.rule, execBranch, Op.isLocal]

variable {L : Launch} {g : Nat}

theorem seg_braT {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hp : (p, Value.pred true) ∈ F) (hA : Assumption.SegFreePc asms pc := by asms_free) :
    SegE L g pc F target F := by
  refine ⟨1, fun t h => ?_⟩
  obtain ⟨u, hr, hu⟩ := run_bra hc true h (holds_mem h.2.2.2.2 hp) (asms_bra_none L g t target uni)
    hA
  exact ⟨u, hr, by simpa using hu⟩

theorem seg_braF {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hp : (p, Value.pred false) ∈ F) (hA : Assumption.SegFreePc asms pc := by asms_free) :
    SegE L g pc F (pc + 1) F := by
  refine ⟨1, fun t h => ?_⟩
  obtain ⟨u, hr, hu⟩ := run_bra hc false h (holds_mem h.2.2.2.2 hp)
    (asms_bra_none L g t target uni) hA
  exact ⟨u, hr, by simpa using hu⟩

theorem seg_nbraT {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : (p, Value.pred false) ∈ F) (hA : Assumption.SegFreePc asms pc := by asms_free) :
    SegE L g pc F target F := by
  refine ⟨1, fun t h => ?_⟩
  obtain ⟨u, hr, hu⟩ := run_nbra hc false h (holds_mem h.2.2.2.2 hp) hA
  exact ⟨u, hr, by simpa using hu⟩

theorem seg_nbraF {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : (p, Value.pred true) ∈ F) (hA : Assumption.SegFreePc asms pc := by asms_free) :
    SegE L g pc F (pc + 1) F := by
  refine ⟨1, fun t h => ?_⟩
  obtain ⟨u, hr, hu⟩ := run_nbra hc true h (holds_mem h.2.2.2.2 hp) hA
  exact ⟨u, hr, by simpa using hu⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Mma

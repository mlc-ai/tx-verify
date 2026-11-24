-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmWiden
public import Lemmas.Flow.FmaPairCore

@[expose] public section

/-! # Tools of the score stage (pcs 1299-2233)

The score stage walks about 940 instructions between the wait for the S tile (pc 1298) and the
first shuffle after the row maximum (pc 1838) and the one after the row sum (pc 2234). Inside the
stage most registers are written once, so a checkpoint's facts are given as an overlay: the
registers live at the checkpoint, each with the first value of an explicit list `ex` of the
registers the stage wrote and else with its value in the table of the state at the start of the
stage (`valueEx`, `Seg.set1`). This file gives the overlay's lookup lemmas, a two-register step
(`Seg.set2`), the generalized assumption facts for the stage's floating forms, a `bf16` bias word
as a number (`BfOk`, `bfR`), and the local steps of the bias widening that hold for every bias
word, a loaded `bf16` number or the zero half-word the masked loads leave. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### The overlay -/

theorem valueEx_nil (base : Nat → Value) : valueEx base [] = base := rfl

theorem valueEx_cons_self (base : Nat → Value) (ex : List (Nat × Value)) (r : Nat) (v : Value) :
    valueEx base ((r, v) :: ex) r = v := by
  simp [valueEx, List.lookup]

theorem valueEx_cons_ne (base : Nat → Value) (ex : List (Nat × Value)) {r r' : Nat} {v : Value}
    (h : r' ≠ r) : valueEx base ((r, v) :: ex) r' = valueEx base ex r' := by
  simp [valueEx, List.lookup, beq_false_of_ne h]

/-- Facts of one overlay hold as facts of another that agrees with it on the live registers. -/
theorem holds_overlay {R : Nat → Option Value} {live : List Nat} {B B' : Nat → Value}
    (h : Holds R (factsFrom live B)) (heq : ∀ r ∈ live, B' r = B r) :
    Holds R (factsFrom live B') := by
  refine holds_of_pointwise fun r hr => ?_
  rw [heq r hr]
  exact holds_mem h (mem_factsFrom hr)

/-- A piece whose end overlay is restated: the two agree on the live registers. -/
theorem Seg.overlay_end {K : Kernel} {A : List Assumption} {n s b : Nat} {F : List (Nat × Value)}
    {liveT : List Nat} {B B' : Nat → Value}
    (h : Seg K A L g n s F b (factsFrom liveT B)) (heq : ∀ r ∈ liveT, B' r = B r) :
    Seg K A L g n s F b (factsFrom liveT B') :=
  h.weaken_end fun _ hR => holds_overlay hR heq

/-- **One step that writes two registers**, from facts with explicit values in front of a table to
the same form with the two written registers in front. -/
theorem Seg.set2 {K : Kernel} {A : List Assumption} {pc d1 d2 : Nat} {op : Op}
    {liveS liveT : List Nat} {base : Nat → Value} {ex : List (Nat × Value)} {v1 v2 : Value}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true) (hne : d1 ≠ d2)
    (hex : ∀ t, At t pc (factsFrom liveS (valueEx base ex)) →
      execLocalA A L g t op = .ok (PTX.next (setReg (setReg t d1 v1) d2 v2)))
    (hcov : ∀ r ∈ liveT, r = d1 ∨ r = d2 ∨ (r ≠ d1 ∧ r ≠ d2 ∧ r ∈ liveS)) :
    Seg K A L g 1 pc (factsFrom liveS (valueEx base ex)) (pc + 1)
      (factsFrom liveT (valueEx base ((d2, v2) :: (d1, v1) :: ex))) := by
  intro t h
  refine ⟨_, run_local hc hl h (hex t h), congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  refine holds_of_pointwise fun r hr => ?_
  rcases hcov r hr with rfl | rfl | ⟨h1, h2, h3⟩
  · rw [valueEx_cons_ne _ _ hne, valueEx_cons_self]
    simp [PTX.next, setReg, Function.update_of_ne hne]
  · rw [valueEx_cons_self]
    simp [PTX.next, setReg]
  · rw [valueEx_cons_ne _ _ h2, valueEx_cons_ne _ _ h1]
    have := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx base ex) h3)
    simpa [PTX.next, setReg, Function.update_of_ne h1, Function.update_of_ne h2] using this

/-! ### The assumptions at the stage's pcs -/

/-- The floating forms of the stage that the ideal reading names. -/
abbrev stageForms : List FloatForm :=
  [.add .f32, .mul .f32, .fma .f32, .subRn .f32, .mulF32x2, .addRnF32x2, .fmaRnF32x2, .min .f32,
    .max .f32, .setp .f32, .setpInf .f32]

/-- At a pc outside the software `exp2` instances the stage's forms are read as exact. -/
theorem idealAtSc {f : FloatForm} (hf : f ∈ stageForms) {t : TState}
    (h : Assumptions.emuSites.contains t.pc = false) : IdealAt asms f L g t := by
  show IdealAt (idealReal _ _ _ :: _) f L g t
  exact idealAt_head hf (segFree h).tail

/-- A stage form that the ideal rule declines takes the Core rule, at a pc that is no software
`exp2` instance and no single-instruction reading's site. -/
theorem declineAtSc {f : FloatForm} (hfs : f ∈ stageForms) {t : TState}
    (h : Assumptions.emuSites.contains t.pc = false) (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) : DeclineAt asms f L g t := by
  intro op hf hn
  have hfs' := hfs
  rw [(segFree h).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ asms.drop 2
  · refine asms_tail_none' h1 h2 h3 (fun c hc => ?_) a hd
    subst hc
    simp only [stageForms, List.mem_cons, List.not_mem_nil, or_false] at hfs
    rcases hfs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Assumption.FloatForm.ofOp] at hf
      split_ifs at hf <;> simp at hf
  · simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
      List.drop_succ_cons, List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs with hm
      · exact hn
      · exact absurd hfs' hm
    · exact Assumption.approxExact_localRule_none fun f' h' => by
        rw [Flow.approxForm_none_of_float hf] at h'; cases h'
    · exact absurd ha' hd

/-! ### A bias word as a number

A bias word the loads return is a `bf16` number; the word of a masked load is the zero half-word
(`z16`, bits). Both read as a number in the extended reals. -/

theorem readEReal_bfOk {v : Value} (h : BfOk v) :
    readEReal .bf16 v = some (.ok ((bfR v : ℝ) : EReal)) := by
  rcases h with ⟨x, rfl⟩ | rfl
  · simp [readEReal, bfR, pure, Except.pure]
  · have : readEReal .bf16 z16 = some (.ok (0 : EReal)) := by rfl
    rw [this]
    simp [bfR]

theorem bfOk_bytes {v : Value} (h : BfOk v) : v.bytes = 2 := by
  rcases h with ⟨x, rfl⟩ | rfl <;> rfl

/-- Packing two bias words and splitting the pack gives the words back. -/
theorem split32_join {a b : Value} (ha : BfOk a) (hb : BfOk b) :
    splitValue 32 (joinValue a b) = (a, b) := by
  rcases ha with ⟨x, rfl⟩ | rfl <;> rcases hb with ⟨y, rfl⟩ | rfl
  · rfl
  · rfl
  · rfl
  · decide +kernel

/-! ### The local steps of the widening, for every bias word -/

/-- `mov.b32 {lo, hi}, %r` of a register whose value splits into two half-words. -/
theorem exec_unpackV {t : TState} {a b r : Nat} {v lo hi : Value}
    (hS : Assumption.SegFreePc asms t.pc) (hr : t.regs r = some v) (hv : v.bytes = 4)
    (hsp : splitValue 32 v = (lo, hi)) (hlo : lo.bytes = 2) (hhi : hi.bytes = 2) :
    execLocalA asms L g t (.move ⟨.unpack, .int .b 32, [some a, some b], [.reg r]⟩) =
      .ok (PTX.next (setReg (setReg t a lo) b hi)) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, hr, hv, hsp,
    hlo, hhi, bind, Except.bind, pure, Except.pure]

/-- **`cvt.f32.bf16`** of a register whose value reads as the extended real `x`. -/
theorem exec_cvtWidenE {t : TState} {d a : Nat} {v : Value} {x : EReal}
    (hS : Assumption.SegFreePc asms t.pc) (ha : t.regs a = some v)
    (hx : readEReal .bf16 v = some (.ok x)) :
    execLocalA asms L g t (.cvt (cvtW d a)) =
      .ok (PTX.next (setReg t d (erealValue .f32 x))) := by
  have hx' : readERealOpnd t .bf16 (.reg a) = some (.ok x) := by
    rw [readERealOpnd_reg ha]; exact hx
  have h1 : Assumptions.idealArith.localRule L g t (.cvt (cvtW d a)) = none :=
    Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp, cvtW, CvtInstr.widenF16?, CvtInstr.packF16?] at h
  have h2 : Assumptions.approx.localRule L g t (.cvt (cvtW d a)) = none :=
    Assumption.approxExact_localRule_none fun f h => by simp [Assumption.ApproxForm.ofOp] at h
  have h4 : Assumptions.lg2Exact.localRule L g t (.cvt (cvtW d a)) = none := by
    simp [Assumptions.lg2Exact]
  have h5 : Assumptions.divFullExact.localRule L g t (.cvt (cvtW d a)) = none := by
    simp [Assumptions.divFullExact]
  have h6 : Assumptions.negExact.localRule L g t (.cvt (cvtW d a)) = none := by
    simp [Assumptions.negExact]
  have h7 : Assumptions.bf16Exact.localRule L g t (.cvt (cvtW d a)) =
      some (.ok (PTX.next (setReg t d (erealValue .f32 x)))) := by
    simp [Assumptions.bf16Exact, cvtW, CvtInstr.plain, hx', bindRead, pure, Except.pure]
  rw [hS.exec rfl]
  simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h4, h5, h6, h7]
  rfl

theorem erealValue_f32_coe (x : ℝ) : erealValue .f32 ((x : ℝ) : EReal) = .float .f32 x :=
  erealValue_coe .f32 x

/-! ### Liveness, checked in linear time

`∀ r ∈ live (pc + 1), r ∈ xs ∨ r ∈ live pc` by `decide` compares every pair of registers. The
live lists are sorted, so a merge walk (`subS`) decides the inclusion in linear time; its
soundness needs no sortedness. -/

/-- The inclusion of one list in another, by a merge walk of two sorted lists. -/
def subS : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then subS as bs else if b < a then subS (a :: as) bs else false

theorem subS_sound : ∀ (l1 l0 : List Nat), subS l1 l0 = true → ∀ r ∈ l1, r ∈ l0
  | [], _, _, r, hr => absurd hr (by simp)
  | _ :: _, [], h, _, _ => by simp [subS] at h
  | a :: as, b :: bs, h, r, hr => by
    unfold subS at h
    by_cases h1 : (a == b) = true
    · have hab : a = b := by simpa using h1
      subst hab
      rw [if_pos h1] at h
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (subS_sound as bs h r hr)
    · rw [if_neg h1] at h
      by_cases h2 : b < a
      · rw [if_pos h2] at h
        exact List.mem_cons_of_mem _ (subS_sound (a :: as) bs h r hr)
      · rw [if_neg h2] at h
        cases h

/-- The registers of `l1` outside `xs` are among those of `l0`. -/
def subX (l1 l0 xs : List Nat) : Bool := subS (l1.filter fun r => !xs.contains r) l0

theorem subX_sound {l1 l0 xs : List Nat} (h : subX l1 l0 xs = true) :
    ∀ r ∈ l1, r ∈ xs ∨ (r ∉ xs ∧ r ∈ l0) := by
  intro r hr
  by_cases hx : r ∈ xs
  · exact Or.inl hx
  · refine Or.inr ⟨hx, subS_sound _ _ h r ?_⟩
    simp only [List.mem_filter, hr, true_and, Bool.not_eq_true']
    simpa using hx

theorem subX_cov2 {l1 l0 : List Nat} {a b : Nat} (h : subX l1 l0 [a, b] = true) :
    ∀ r ∈ l1, r = a ∨ r = b ∨ (r ≠ a ∧ r ≠ b ∧ r ∈ l0) := by
  intro r hr
  rcases subX_sound h r hr with hx | ⟨hx, hl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact Or.inr (Or.inr ⟨hx.1, hx.2, hl⟩)

/-- The registers of `l` are none of `xs`. -/
def disj (l xs : List Nat) : Bool := l.all fun r => !xs.contains r

theorem disj_sound {l xs : List Nat} (h : disj l xs = true) : ∀ r ∈ l, r ∉ xs := by
  intro r hr hx
  have := List.all_eq_true.mp h r hr
  simp [hx] at this

end
end PTX.Kernels.InklingRelDecode.Proof.Sm

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.FactsInv

@[expose] public section

/-! # The run invariant of a thread

Along a thread's run one invariant holds (`RunFacts`): the state's invariant, the position of its
event, the numbers of barrier arrivals and shuffles before it, and the data of its row
(`RowData`). Each step keeps it (`runFacts_step`): the position advances by one event, the counts
by the event's kind, and a transition that sets a datum sets it from the event it fires on. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The run invariant of thread `g` at abstract state `d` after events `es`. -/
def RunFacts (P : Params) (g : Nat) (d : D) (es : List Event) : Prop :=
  Inv P g d ∧ es.length = d.idx g ∧ es.countP (Execution.isBarId 0) = d.bc0 ∧
    es.countP (Execution.isBarId 1) = d.bc1 ∧ es.countP Execution.isShfl = d.sc g ∧
    RowData P g d es ∧ (d.site = .shfl0 → d.i = 0)

theorem countP_snoc (p : Event → Bool) (pre : List Event) (e : Event) :
    (pre ++ [e]).countP p = pre.countP p + if p e then 1 else 0 := by
  simp [List.countP_append]

/-- Arithmetic of positions and counts: unfold them and split on the thread's lane and warp. -/
syntax "rf_arith" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rf_arith $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      simp only [D.idx, D.pos, D.bc0, D.bc1, D.sc, rowBase, rowLen, Site.vec, Site.vload,
        Site.inRow, List.length_append, List.length_cons, List.length_nil, Bool.false_eq_true,
        ↓reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceBEq, beq_self_eq_true, $extra,*]
      all_goals first
        | omega
        | ((try split_ifs) <;> omega)
        | (simp only [p1, l0, l8, w0, t0]; (try split_ifs) <;> omega)))

/-- The condition of a kept datum: unfold the positions and close by `omega`. -/
syntax "rf_cond" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rf_cond $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      intros
      simp only [D.pos, Site.inRow, Site.vload, Site.vec, p1, Bool.false_eq_true, true_and,
        and_true,
        ↓reduceIte, $extra,*] at *
      all_goals first
        | omega
        | (simp only [l0, l8, w0, t0] at *; (try split_ifs at *) <;> omega)))

/-- `omega`, after unfolding the lane and warp indicators if needed. -/
macro "rf_omega" : tactic => `(tactic| (
  first
    | omega
    | (simp only [l0, l8, w0, t0] at *; (try split_ifs at *) <;> omega)))

/-- All data of a row kept, leaving the values a vector load holds and the conditions. -/
macro "rd_keep" hD:term:max hl:term:max : tactic => `(tactic| (
  refine ⟨?_, keep_xa $hD $hl rfl rfl ?_, keep_xb $hD $hl rfl rfl ?_,
    keep_ra $hD $hl rfl (fun _ _ => rfl) ?_, keep_u $hD $hl rfl rfl ?_,
    keep_rb $hD $hl rfl (fun _ _ => rfl) ?_,
    keep_tt $hD $hl rfl rfl ?_, keep_rawa $hD $hl rfl rfl ?_, keep_rawb $hD $hl rfl rfl ?_,
    keep_rs0a $hD $hl rfl rfl ?_, keep_rs0b $hD $hl rfl rfl ?_,
    keep_rs1a $hD $hl rfl rfl ?_, keep_rs1b $hD $hl rfl rfl ?_⟩))

/-- A step that keeps every datum: the invariant, the position, the counts, the data. -/
macro "rf_std" hs:term:max hlen:term:max hb0:term:max hb1:term:max hsc:term:max hD:term:max
    hl:term:max : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [$hs:term]⟩
  · inv_tac
  · rw [List.length_append, $hlen:term]; rf_arith [$hs:term]
  · rw [countP_snoc, $hb0:term]; simp only [Execution.isBarId]; rf_arith [$hs:term]
  · rw [countP_snoc, $hb1:term]; simp only [Execution.isBarId]; rf_arith [$hs:term]
  · rw [countP_snoc, $hsc:term]; simp only [Execution.isShfl]; rf_arith [$hs:term]
  · rd_keep $hD $hl
    all_goals rf_cond [$hs:term]))


end
end PTX.Kernels.RmsNorm.Proof

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem hlen_of {d : D} {pre : List Event} (h : pre.length = d.idx g) :
    d.site.inRow = true → pre.length = rowBase g d.i + d.pos g := by
  intro hr
  rw [h]
  unfold D.idx
  split <;> simp_all [Site.inRow]

end
end PTX.Kernels.RmsNorm.Proof

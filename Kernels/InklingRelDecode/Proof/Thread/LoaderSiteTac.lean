-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderStart
public import Kernels.InklingRelDecode.Proof.Thread.LoaderCopy
public import Kernels.InklingRelDecode.Proof.Thread.LoaderEnd
public import Lemmas.Flow.Step.SiteIte

@[expose] public section

/-! # What `site_cases` needs of the loader

The loader as a code machine (`code`) and the tactics with which `site_cases` proves its
obligations (`LoaderSteps`):

* `lw_pre` (the role's `seg_pre`): the invariant in context writes the state's registers as the
  inherited ones and the two loaded words (`Inv.proW`), so that the evaluation reads the table;
  a segment to the state after an iteration (`afterIter`) is cut at the counter's increment
  (pc 2413) and the rest is `loopEnd`, which reads the loaded counter and `num_iters` words;
* `lw_seg_site`: a segment, by evaluation (`lw_seg`);
* `lw_inv`: the successor's invariant (`inv_to`, `afterIter_inv`);
* `lw_guard`: the guards (the elections' predicates, true in the table, and lane 0's at the
  arrival, from the invariant);
* a rule of `lands_auto` for the successors `afterIter d`, whose sub-step and accumulator are
  `sub_afterIter`, `acc_afterIter` (not `rfl`: `afterIter` is an `if`).

`stepOk_of` turns a step lemma of the form `Step` (the sites with their own proofs) into the
machine's `StepOk`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The loader role as a code machine, from its `setmaxnreg.dec`, with the inherited registers
`P`. -/
@[reducible] def code (L : Launch) (g : Nat) (P : Pro) : Flow.Code kernel asms L g where
  D := D
  init := D.start L g P
  pc := (·.site.pc)
  facts := facts L g
  sub := sub
  acc := acc
  inv := Inv L g
  next := next L g

theorem AtS.at {d : D} {t : TState} (h : AtS L g d t) (hs : sub d = 0) (ha : acc d = []) :
    At t d.site.pc (facts L g d) :=
  ⟨h.1, hs ▸ h.2.1, ha ▸ h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A step lemma of the form `Step` as the machine's `StepOk`. -/
theorem stepOk_of {P : Pro} {d : D}
    (hs : ∀ {t e u ins}, Inv L g d → AtS L g d t → kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → Step L g d e u) :
    (code L g P).StepOk d where
  step := by
    intro t e u ins h hi hc hf
    rcases hs hi h hc hf with (hn | ⟨hn, hd⟩) | ⟨d', t', hn, hr, ht, hi'⟩
    · exact .inl (.inl hn)
    · exact .inr ⟨hn, hd⟩
    · exact .inl (.inr ⟨d', t', hn, hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi'⟩)

/-- The invariant after the first element of the vector load. -/
theorem inv_readI {d : D} (hi : Inv L g d) (v : Value) : Inv L g (readI d v) := by
  obtain ⟨Q, hQ⟩ := hi.pro
  refine ⟨⟨Q, fun r h1 h2 => ?_⟩, fun _ => by simp [readI, wordI],
    fun h => by simp [readI, Site.bounded, Site.inLoop] at h,
    fun h => by simp [readI, Site.inLoop] at h, fun h => by simp [readI, Site.inLoop] at h,
    hi.ln, fun h => by simp [readI] at h⟩
  simpa [readI, Function.update_of_ne h1] using hQ r h1 h2

/-- The registers live at the vector load are neither the table's nor the counter register, so
the first element leaves its facts as they are. -/
theorem facts_readI (d : D) (v : Value) : factsAt L g 2345 (readI d v) = factsAt L g 2345 d := by
  have hl : ∀ r ∈ Flow.live 2345, r ∉ tableKeys ∧ r ≠ 1905 := by decide +kernel
  unfold factsAt Flow.factsFrom
  refine List.map_congr_left fun r hr => ?_
  obtain ⟨h1, h2⟩ := hl r hr
  rw [valueOf_pro h1, valueOf_pro h1]
  simp [readI, Function.update_of_ne h2]

/-- The first element of the vector load of `(num_pre, num_iters)`: the counter register holds the
value read (`readI`), with the second element still to come. -/
theorem ov_ld0 (P : Pro) (pro : Nat → Value) (i n p0 p1 : Nat) (ln : Bool) :
    (code L g P).StepOk ⟨.ld0, pro, i, n, p0, p1, ln⟩ :=
  Code.step_ldv_mid_sel (nv := fun v => some (some (readI ⟨.ld0, pro, i, n, p0, p1, ln⟩ v)))
    Flow.code_2345 rfl rfl rfl (of_decide_eq_true rfl) (fun _ _ _ hv => by simp [next, hv])
    (fun _ _ _ hv => .inl (by simp [next, hv])) (by simp) fun v d' h => by
      obtain rfl := Option.some.inj (Option.some.inj h)
      exact ⟨rfl, rfl, rfl, facts_readI _ v, fun hi => inv_readI hi v⟩

/-- The invariant after the second element of the vector load. -/
theorem inv_readN {d : D} (hi : Inv L g d) (hs : d.site = .ld1) (v : Value) :
    Inv L g (readN d v) := by
  obtain ⟨Q, hQ⟩ := hi.pro
  refine ⟨⟨Q, fun r h1 h2 => ?_⟩, fun _ => ?_, fun _ => by simp [readN, wordN],
    fun h => by simp [readN, Site.inLoop] at h, fun h => by simp [readN, Site.inLoop] at h,
    hi.ln, fun h => by simp [readN] at h⟩
  · simpa [readN, Function.update_of_ne h2] using hQ r h1 h2
  · simpa [readN, wordI] using hi.wi (.inl hs)

/-- The second element of the vector load: `num_iters` is the value read (`readN`), and the
counter register holds the first element's. -/
theorem ov_ld1 (P : Pro) (pro : Nat → Value) (i n p0 p1 : Nat) (ln : Bool) :
    (code L g P).StepOk ⟨.ld1, pro, i, n, p0, p1, ln⟩ :=
  Code.step_ldv_last_sel (nv := fun v => some (some (readN ⟨.ld1, pro, i, n, p0, p1, ln⟩ v)))
    Flow.code_2345 rfl rfl rfl (of_decide_eq_false rfl) (by decide)
    (fun _ _ _ hv => by simp [next, hv]) (fun _ _ _ hv => .inl (by simp [next, hv])) (by simp)
    fun v d' h => by
      obtain rfl := Option.some.inj (Option.some.inj h)
      refine ⟨fun _ => ⟨0, Seg.weaken_end (Seg.refl _ _) fun R hR => ?_⟩, rfl, rfl,
        fun hi => inv_readN hi rfl v⟩
      have hl : ∀ r ∈ Flow.live 2346, r ∉ tableKeys ∧
          (r = 1905 ∨ r = 467 ∨ (r ≠ 1905 ∧ r ≠ 467 ∧ r ∈ Flow.live 2345)) := by decide +kernel
      refine holds_of_pointwise fun r hr => ?_
      obtain ⟨h1, h2⟩ := hl r hr
      rw [valueOf_pro h1]
      rcases h2 with rfl | rfl | ⟨h2, h3, h4⟩
      · simpa [readN, wordI] using hR.1
      · simpa [readN] using hR.2.1
      · have hm := holds_mem hR.2.2 (List.mem_filter.mpr ⟨List.mem_filter.mpr
          ⟨Flow.mem_factsFrom (val := valueOf L g ⟨.ld1, pro, i, n, p0, p1, ln⟩) h4,
            by simpa using h2⟩, by simpa using h3⟩)
        rw [valueOf_pro h1] at hm
        simpa [readN, Function.update_of_ne h3] using hm

open Lean Elab Tactic Meta

/-- The loader's invariant in context. -/
meta def findInv : TacticM (Option (TSyntax `term)) := withMainContext do
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars ld.type)
    if ty.isAppOfArity ``Inv 3 then return some (← Term.exprToSyntax ld.toExpr)
  return none

/-- `lw_pre` (the role's `seg_pre`): the registers of the state as the inherited ones and the two
loaded words; a segment to `afterIter d` is cut at pc 2413 and closed by `loopEnd`. Fails where
there is no loader invariant, so other roles' rules apply there. -/
elab "lw_pre" : tactic => do
  let some hi ← findInv | throwError "lw_pre: no loader invariant"
  Term.withoutErrToSorry <| evalTactic (← `(tactic| (
    obtain ⟨_, _, _, hP⟩ := Inv.proW $hi
    simp only at hP
    subst hP)))
  let ty ← instantiateMVars (← getMainTarget)
  if (ty.find? (·.isAppOfArity ``afterIter 1)).isSome then
    let some hi ← findInv | throwError "lw_pre: no loader invariant"
    Term.withoutErrToSorry <| evalTactic (← `(tactic| (
      obtain ⟨hwi, hwn⟩ := Inv.bits $hi rfl
      simp only [wordI, wordN, Pro.valW, Nat.reduceEqDiff, ↓reduceIte] at hwi hwn
      refine Seg.comp_ex ?_ (loopEnd _ _ _ _ _ _ _ _ _ hwi hwn))))

macro_rules | `(tactic| seg_pre) => `(tactic| lw_pre)

/-- A segment by evaluation. -/
macro "lw_seg_site" : tactic => `(tactic| (intro t h; lw_seg h))

set_option hygiene false in
/-- The successor's invariant. -/
macro "lw_inv" : tactic => `(tactic| (intro hi; first
  | exact hi
  | exact afterIter_inv hi rfl
  | inv_to hi
  | (split <;> inv_to hi)
  | fail "lw_inv"))

/-- The guard of a site: an election's predicate, true in the table, or lane 0's at the
arrival. -/
macro "lw_guard" : tactic => `(tactic| first
  | rfl
  | exact congrArg Value.pred (Inv.lane ‹Inv _ _ _› rfl)
  | fail "lw_guard")

/-- `lands_auto` for the loader: as `SiteIte`'s rule, and the sub-step and accumulator of the
state after an iteration by `sub_afterIter`, `acc_afterIter`. -/
macro_rules
  | `(tactic| lands_auto ($seg) ($inv)) => `(tactic| (
      intros
      refine ⟨?seg, ?sub, ?acc, ?inv⟩
      case sub =>
        first
          | rfl
          | ((repeat' split) <;> rfl)
          | exact sub_afterIter _
          | fail "lands_auto: sub-step"
      case acc =>
        first
          | rfl
          | ((repeat' split) <;> rfl)
          | exact acc_afterIter _
          | fail "lands_auto: accumulator"
      case seg =>
        intro _
        site_norm
        try dsimp only [PTX.Flow.Code.electFacts]
        try drop_norm
        seg_pre
        first
          | seg_auto using $seg
          | ((repeat' ite_cases) <;> seg_auto using $seg)
          | seg_sym using $seg
          | fail "lands_auto: segment"
      case inv =>
        site_norm
        ($inv)))

end
end PTX.Kernels.InklingRelDecode.Proof.Loader

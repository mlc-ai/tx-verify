-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Coll
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollCommon
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collective sites of a role, from a check of its sites -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The instruction at a position. -/
def insAt (n : Nat) : Option Instr := codeFrom (n / 256 * 256) n

theorem insAt_eq {n : Nat} : insAt n = kernel.code[n]? := codeFrom_eq (by omega)

/-- A site at `pc` is a collective's exactly when `wc`, with a static part unless `dyn`. -/
def siteCk (dyn wc : Bool) (pc : Nat) : Bool :=
  warpO (insAt pc) == wc && (insAt pc).isSome && (!wc || dyn || staticO (insAt pc)) && (!dyn ||
    match insAt pc with
    | some ins => !ins.op.isLocal && ins.op.isShfl
    | none => false)

theorem siteCk_ok {dyn wc : Bool} {pc : Nat} (h : siteCk dyn wc pc = true) : warpPc pc = wc ∧
    (kernel.code[pc]?).isSome = true ∧ (wc = true → dyn = true ∨ staticPc pc = true) ∧
    (dyn = true → ∀ ins, kernel.code[pc]? = some ins →
      ins.op.isLocal = false ∧ ins.op.isShfl = true) := by
  simp only [siteCk, insAt_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun hc => ?_, fun hd ins hi => ?_⟩
  · rcases h3 with (h3 | h3) | h3
    · rw [h3] at hc; cases hc
    · exact .inl h3
    · exact .inr h3
  · rcases h4 with h4 | h4
    · rw [h4] at hd; cases hd
    · rw [hi] at h4
      simpa using h4

/-- The startup's collective sites. -/
def startAt : Startup.Site → Bool
  | .sh _ | .elect _ => true
  | _ => false

private theorem start_ck : (∀ j : Fin 3, siteCk false true (Startup.Site.sh j).pc = true) ∧
    (∀ j : Fin 16, siteCk false true (Startup.Site.elect j).pc = true) ∧
    (∀ j : Fin 34, siteCk false false (Startup.Site.init j).pc = true) ∧
    siteCk false false Startup.Site.fence.pc = true ∧
    siteCk false false Startup.Site.bar.pc = true := by
  decide +kernel

/-- **A startup site is a collective's exactly at the shuffles and elections**, of static parts. -/
theorem start_site {s : Startup.Site} (h : ∀ r, s ≠ .enter r) :
    siteCk false (startAt s) s.pc = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := start_ck
  cases s with
  | sh j => exact h1 j
  | elect j => exact h2 j
  | init j => exact h3 j
  | fence => exact h4
  | bar => exact h5
  | enter r => exact absurd rfl (h r)

/-- **A state is at a collective exactly when its site is one.** -/
theorem collAt_of_site {σ : (thread p L g).D} {dyn wc : Bool}
    (h : siteCk dyn wc ((thread p L g).pc σ) = true) : CollAt p L g σ ↔ wc = true := by
  obtain ⟨h1, h2, -⟩ := siteCk_ok h
  rw [collAt_iff h2, h1]

/-- The static part of a choice's shuffle with the ballot `bal`. -/
def choiceShape (tiles : Bool) (bal : BitVec 64) : Sched.CollShape :=
  if tiles then .shfl .idx (truncBits 32 (Epilogue.popc bal)).toNat 31
  else .shfl .idx (truncBits 32 (Epilogue.addi (Epilogue.popc bal) (-1))).toNat 31

private theorem tmplShape_mk {md : ShflMode} {a : Value} {b c : Nat}
    {k : Value → Bool → TState} :
    Sched.tmplShape (.shfl md a b c k) = some (.shfl md b c) := rfl

/-- **The static part of a state at a choice's shuffle**, from the events it fires. -/
theorem shapeAt_choice {σ : (thread p L g).D} {S : ∀ g, (thread p L g).D → Sched.CollShape}
    {tiles l : Bool} {d : Epilogue.D} {wc : Bool}
    (hck : siteCk true wc ((thread p L g).pc σ) = true)
    (hd : d.site = if tiles then .tiles l else .pre l) (hS : S g σ = choiceShape tiles d.bal)
    (hEv : ∀ t ins e o, (thread p L g).AtD σ t → (thread p L g).inv σ →
      kernel.code[(thread p L g).pc σ]? = some ins →
      Fires ((thread p L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e o →
      (∀ f, e.kind ≠ .ub f) → Epilogue.Ev p L g d e) :
    Sched.ShapeAt (Progress.timed p L) S g σ := by
  refine ⟨?_, fun t ins hAt hinv hi => ?_⟩
  · rw [hS]
    cases tiles <;> simp [choiceShape, Sched.CollShape.Full]
  · obtain ⟨-, -, -, hdyn⟩ := siteCk_ok hck
    obtain ⟨hloc, hsh⟩ := hdyn rfl ins hi
    refine ⟨hloc, ?_⟩
    rcases shfl_tmpl (L := L) (g := g) (t := t) hsh with hu | ⟨md, a, b, c, k', hm⟩
    · exact .inl hu
    · right
      have := hEv t ins ⟨_, .shfl md a b c (.bits 32 0) false⟩ _ hAt hinv hi
        (by rw [hm]; exact ⟨_, _, rfl, rfl⟩) (fun _ => nofun)
      rw [hm, hS]
      cases tiles <;>
        simp only [Epilogue.Ev, hd, Bool.false_eq_true, ite_true, ite_false] at this <;>
        obtain ⟨recv, ok, hk⟩ := this <;>
        simp only [Kind.shfl.injEq] at hk <;>
        obtain ⟨e1, -, e2, e3, -, -⟩ := hk <;>
        rw [tmplShape_mk, e1, e2, e3] <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top

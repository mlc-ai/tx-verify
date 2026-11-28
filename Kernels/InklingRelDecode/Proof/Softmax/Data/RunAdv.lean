-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Kernels.InklingRelDecode.Proof.Lib.Segments
public import Lemmas.Flow.RunFrame
public import Lemmas.Flow.FloatRun
public import Lemmas.Flow.ReachSegU
public import Lemmas.Flow.CtlStepsU
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # A generated run as a step of a register file

A generated run (`Tools/out_gen.py`) is a template over the register values `V` at its start:
from the facts `factsFrom live V` it reaches the explicit facts `fs V`. `segU_adv` moves a state
that knows the registers `K` (their values under `V`) across the run: it knows `keep ins K`, the
registers of `K` the run does not write, with `V`, and the run's facts, as the register file
`valueEx V fs`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section
variable {L : Launch} {g : Nat}

/-- The registers of `K` the instructions do not write. -/
def keep (ins : List Instr) (K : List Nat) : List Nat :=
  K.filter fun r => ins.all fun i => !(writesRegs i.op).contains r

theorem frameB_keep {ins : List Instr} (K : List Nat)
    (h : ins.all (fun i => i.op.isLocal && noJump i.op) = true) :
    frameB ins (keep ins K) = true := by
  simp only [frameB, keep, List.all_eq_true, Bool.and_eq_true, List.mem_filter] at h ⊢
  intro i hi
  refine ⟨h i hi, fun r hr => ?_⟩
  simpa using hr.2 i hi

theorem mem_of_lookup : ∀ {fs : List (Nat × Value)} {r : Nat} {v : Value},
    fs.lookup r = some v → (r, v) ∈ fs
  | [], _, _, h => by simp [List.lookup] at h
  | (q, w) :: fs, r, v, h => by
    by_cases e : r = q
    · subst e
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      simp
    · have hb : (r == q) = false := by simpa using e
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- The facts of a run and the facts it keeps are the facts of the changed register file. -/
theorem holds_ex {R : Nat → Option Value} {fs : List (Nat × Value)} {Kf : List Nat}
    {V : Nat → Value} (h : Holds R (fs ++ factsFrom Kf V)) :
    Holds R (factsFrom (Kf ++ fs.map Prod.fst) (valueEx V fs)) := by
  rw [holds_append] at h
  refine holds_of_pointwise fun r hr => ?_
  rcases List.mem_append.mp hr with hk | ho
  · have h1 := holds_mem h.2 (mem_factsFrom hk)
    cases hl : fs.lookup r with
    | none => simp [valueEx, hl, h1]
    | some w =>
      have h2 := holds_mem h.1 (mem_of_lookup hl)
      simp only [valueEx, hl, Option.getD_some]
      exact h2
  · obtain ⟨⟨q, w⟩, hq, rfl⟩ := List.mem_map.mp ho
    cases hl : fs.lookup q with
    | none =>
      obtain ⟨v, hv⟩ := lookup_some (F := fs) (r := q) (List.mem_map.mpr ⟨_, hq, rfl⟩)
      simp [hl] at hv
    | some w' =>
      simp only [valueEx, hl, Option.getD_some]
      exact holds_mem h.1 (mem_of_lookup hl)

/-- A piece that may end dead, as a segment. -/
theorem segU_of_segD' {n a b : Nat} {F G : List (Nat × Value)} {C : Prop}
    (h : SegD kernel Assumptions.all L g n a F b G C) :
    SegU kernel Assumptions.all L g a F b G := by
  intro t ht
  by_cases hc : C
  · obtain ⟨u, hr, hu⟩ := (h t ht).1 hc
    exact .inl ⟨u, run_rtg hr, hu⟩
  · exact .inr ((h t ht).2 hc)

/-- **A generated run on a register file**: a state that knows the registers `K` under `V` reaches
the end of the run knowing the registers it kept and the run's facts, under `valueEx V fs`. -/
theorem segU_adv {n s b : Nat} {V : Nat → Value} {live K : List Nat} {fs : List (Nat × Value)}
    {C : Prop} {ins : List Instr}
    (seg : SegD kernel Assumptions.all L g n s (factsFrom live V) b fs C)
    (hcode : (kernel.code.drop s).take n = ins) (hlen : ins.length = n)
    (hS : ∀ i < n, Assumption.SegFreePc Assumptions.all (s + i))
    (hlive : live.all (fun r => K.contains r) = true)
    (hl : ins.all (fun i => i.op.isLocal && noJump i.op) = true) :
    SegU kernel Assumptions.all L g s (factsFrom K V) b
      (factsFrom (keep ins K ++ fs.map Prod.fst) (valueEx V fs)) := by
  have h := segU_of_segD' (SegD.frame (H := factsFrom (keep ins K) V) Lib.rulesFrame seg hcode hlen
    (by rw [factsFrom_keys]; exact frameB_keep K hl) hS)
  intro t ht
  obtain ⟨-, -, -, -, hreg⟩ := id ht
  have hF : At t s (factsFrom live V ++ factsFrom (keep ins K) V) := by
    refine At.mono ht (holds_append _ _ _ |>.mpr ⟨holds_factsFrom_mono hreg fun r hr => by
      simpa using List.all_eq_true.mp hlive r hr, ?_⟩)
    exact holds_factsFrom_mono hreg fun r hr => (List.mem_filter.mp hr).1
  rcases h t hF with ⟨u, hr, hu⟩ | hd
  · obtain ⟨-, -, -, -, hur⟩ := id hu
    exact .inl ⟨u, hr, At.mono hu (holds_ex hur)⟩
  · exact .inr hd

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

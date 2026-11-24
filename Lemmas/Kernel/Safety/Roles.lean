-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Table
public import Lemmas.Flow.Roles

@[expose] public section

/-! # The role table of a thread machine with roles

A proof skeleton, generic over the kernel. For the thread machine `Code.roleThread` (the first
fragment, then the role its exit selects, or a stub, with the ghost ledger), the invariant and the
shape table of every state are the first fragment's or the selected role's, read with the ledger's
counts; a stub has neither (`roleJ`, `roleEv`). The obligations of `RoleTable.Ok` at such a state
are the fragment's own (`roleThread_shape`, `roleThread_safe`, `roleThread_death`), so a kernel
states its role table by declaring `JP`, `JR`, `EvP`, `EvR` and proving one shape, `ref_safe` and
death fact per fragment. -/

namespace PTX.Flow.Code

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
variable {P : Code K A L g} {ι E κ : Type} {R : ι → Code K A L g} {pcOf : E → Nat}
  {enterOf : P.D → Option E} {sel : E → P.D → Option ι} {cls : κ → Event → Bool}

/-- The invariant of a state of the thread machine: the first fragment's or the selected role's,
with the ledger's counts; false at a stub. -/
def roleJ (JP : P.D → (κ → Nat) → Prop) (JR : ∀ i, (R i).D → (κ → Nat) → Prop) :
    (roleThread P R pcOf enterOf sel cls).D → Prop
  | (.inl d, n) => JP d n
  | (.inr ⟨.inl i, d⟩, n) => JR i d n
  | (.inr ⟨.inr _, _⟩, _) => False

/-- The shape table of a state of the thread machine: the first fragment's or the selected
role's; none at a stub. -/
def roleEv (EvP : P.D → Event → Prop) (EvR : ∀ i, (R i).D → Event → Prop) :
    (roleThread P R pcOf enterOf sel cls).D → Event → Prop
  | (.inl d, _) => EvP d
  | (.inr ⟨.inl i, d⟩, _) => EvR i d
  | (.inr ⟨.inr _, _⟩, _) => fun _ => False

variable {JP : P.D → (κ → Nat) → Prop} {JR : ∀ i, (R i).D → (κ → Nat) → Prop}
  {EvP : P.D → Event → Prop} {EvR : ∀ i, (R i).D → Event → Prop}

/-- **The shape obligation of the thread machine**, from each fragment's shape table at its
states (the first fragment's at the states that are not exits). -/
theorem roleThread_shape
    (hP : ∀ d n t ins e o, JP d n → P.AtD d t → P.inv d → enterOf d = none →
      K.code[P.pc d]? = some ins → Fires (P.pc d) (eventTmpl A L g t ins.op) e o → EvP d e)
    (hR : ∀ i d n t ins e o, JR i d n → (R i).AtD d t → (R i).inv d →
      K.code[(R i).pc d]? = some ins → Fires ((R i).pc d) (eventTmpl A L g t ins.op) e o →
      EvR i d e)
    (σ : (roleThread P R pcOf enterOf sel cls).D) (t : TState) (ins : Instr) (e : Event)
    (o : Option TState) (hJ : roleJ (pcOf := pcOf) (enterOf := enterOf) (sel := sel) JP JR σ)
    (hat : (roleThread P R pcOf enterOf sel cls).AtD σ t)
    (hi : (roleThread P R pcOf enterOf sel cls).inv σ)
    (hc : K.code[(roleThread P R pcOf enterOf sel cls).pc σ]? = some ins)
    (hf : Fires ((roleThread P R pcOf enterOf sel cls).pc σ) (eventTmpl A L g t ins.op) e o) :
    roleEv (pcOf := pcOf) (enterOf := enterOf) (sel := sel) (cls := cls) EvP EvR σ e := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with d | ⟨j, d⟩
  · exact hP d n t ins e o hJ hat hi.1 (gatedExit_none.mp hi.2) hc hf
  · rcases j with i | r
    · exact hR i d n t ins e o hJ hat hi hc hf
    · exact hJ.elim

/-- **The `ref_safe` obligation of the thread machine**, from each fragment's. -/
theorem roleThread_safe
    (hP : ∀ d n e, P.inv d → JP d n → EvP d e → ∀ f, e.kind ≠ .ub f)
    (hR : ∀ i d n e, (R i).inv d → JR i d n → EvR i d e → ∀ f, e.kind ≠ .ub f)
    (σ : (roleThread P R pcOf enterOf sel cls).D) (e : Event)
    (hi : (roleThread P R pcOf enterOf sel cls).inv σ)
    (hJ : roleJ (pcOf := pcOf) (enterOf := enterOf) (sel := sel) JP JR σ)
    (hev : roleEv (pcOf := pcOf) (enterOf := enterOf) (sel := sel) (cls := cls) EvP EvR σ e) :
    ∀ f, e.kind ≠ .ub f := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with d | ⟨j, d⟩
  · exact hP d n e hi.1 hJ hev
  · rcases j with i | r
    · exact hR i d n e hi hJ hev
    · exact hJ.elim

/-- **The death obligation of the thread machine**, from each fragment's: a fragment's machine
dies only at an exit event. -/
theorem roleThread_death
    (hP : ∀ d n e, P.inv d → JP d n → EvP d e → P.next d e = none → e.kind = .exit)
    (hR : ∀ i d n e, (R i).inv d → JR i d n → EvR i d e → (R i).next d e = none →
      e.kind = .exit)
    (σ : (roleThread P R pcOf enterOf sel cls).D) (e : Event)
    (hi : (roleThread P R pcOf enterOf sel cls).inv σ)
    (hJ : roleJ (pcOf := pcOf) (enterOf := enterOf) (sel := sel) JP JR σ)
    (hev : roleEv (pcOf := pcOf) (enterOf := enterOf) (sel := sel) (cls := cls) EvP EvR σ e)
    (hn : (roleThread P R pcOf enterOf sel cls).next σ e = none) : e.kind = .exit := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with d | ⟨j, d⟩
  · refine hP d n e hi.1 hJ hev ?_
    simp only [roleThread, counted, glue, Option.map_eq_none_iff] at hn
    exact hn
  · rcases j with i | r
    · refine hR i d n e hi hJ hev ?_
      simp only [roleThread, counted, glue, withStubs, Option.map_eq_none_iff] at hn
      exact hn
    · exact hJ.elim

end

end PTX.Flow.Code

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.Frame
import Lemmas.Flow.GlueStep

@[expose] public section

/-! # Induction over the data states of a role

A property of a role's data states that holds at its first state and is kept by its steps holds at
every data state of the role on a trace (`role_induct`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {X : Execution} {g : Nat}

theorem role_induct {r : Role} {Q : Nat → (fragD p L g r).D → Prop}
    (init : ∀ i, Q i (fragD p L g r).init)
    (step : ∀ {i : Nat} {d d' : (fragD p L g r).D} {n : Cls → Nat} {e : Event},
      X.get (g, i) = some e →
      Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨r, d⟩, n)) → Q i d →
      (fragD p L g r).next d e = some (some d') → Q (i + 1) d') :
    ∀ {i : Nat} {d : (fragD p L g r).D} {n : Cls → Nat}, i ≤ (X.tr g).length →
      Frame.stateAt (threadD p L) X g i = some (some (.inr ⟨r, d⟩, n)) → Q i d := by
  intro i
  induction i with
  | zero => intro d n _ hs; rw [Frame.stateAt_zero] at hs; cases hs
  | succ i ih =>
    intro d n hil hs
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e :=
      ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
    have hst := Frame.stateAt_succ (C := threadD p L) (show (X.tr g)[i]? = some e from he)
    rw [hs] at hst
    cases hs0 : Frame.stateAt (threadD p L) X g i with
    | none => rw [hs0] at hst; simp at hst
    | some o =>
      cases o with
      | none => rw [hs0] at hst; exact absurd hst (by simp [Flow.Code.toMachine])
      | some σ =>
        rw [hs0] at hst
        have hn : (threadD p L g).next σ e = some (some (.inr ⟨r, d⟩, n)) := hst.symm
        obtain ⟨s, n0⟩ := σ
        obtain ⟨hn1, -⟩ := Code.counted_next_some (C := gluedD p L g) hn
        cases s with
        | inl s =>
          obtain ⟨s', -, hen⟩ := Flow.Code.glue_inl_some hn1
          unfold Code.enter at hen
          split at hen
          · cases hen
            exact init _
          · cases hen
        | inr a =>
          obtain ⟨r', d0⟩ := a
          obtain ⟨d1, hn2, hen⟩ := Flow.Code.glue_inr_some hn1
          cases hen
          exact step he hs0 (ih (by omega) hs0) hn2

end PTX.Kernels.TmlFa4Fwd.Proof

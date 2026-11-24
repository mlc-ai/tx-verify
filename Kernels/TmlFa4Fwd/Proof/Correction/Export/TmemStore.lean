-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction lane's stores are followed by a `wait::st` of their stage

The rescale stores of stage `st` (`rst st c`) wait at `rwait st`, after the stage's eighth store.
From a store at position `f`, every later state of the lane is a state of the stage's rescale
loop (`StPend st`: `rst`, `rld`, `rldw`, `rwait` of `st`) until a `wait::st` (the event at
`rwait st`) or an undefined-behaviour event (`corr_st_pend`, by induction along the trace on the
role's `succ` at those sites). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites of stage `st`'s rescale loop from a store to its wait. -/
def StPend (st : Fin 2) : Correction.Site → Bool
  | .rst s _ | .rld s _ | .rldw s _ | .rwait s => s == st
  | _ => false

/-- The successor of a state of stage `st`'s loop, or of its store, is in the loop, unless the
state is the wait. -/
theorem pend_next {st0 : Fin 2} {d d' : Correction.Control.D} {e : Event}
    (hp : StPend st0 d.site = true) (hw : ∀ s, d.site ≠ .rwait s)
    (hn : Correction.Control.succ p L g d e = some (some d')) : StPend st0 d'.site = true := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> (try simp only [StPend, Bool.false_eq_true] at hp)
  case rst s c =>
    simp only [Correction.Control.succ, Correction.Control.D.scheduler, Correction.succ,
        Option.map_some, Option.map_none] at hn
    split_ifs at hn <;> (cases hn; simpa [StPend, Correction.Control.erase, Correction.D.mk']
        using hp)
  case rld s c =>
    simp only [Correction.Control.succ, Correction.Control.D.scheduler, Correction.succ,
        Option.map_some, Option.map_none] at hn
    split at hn
    · cases hn; simpa [StPend] using hp
    · cases hn
  case rldw s c =>
    by_cases h : k = 1
    · change (if k = 1 then some (some _) else some none).map _ = _ at hn
      simp only [h, ↓reduceIte] at hn
      cases hn
      exact hp
    · change (if k = 1 then some (some _) else some none).map _ = _ at hn
      simp only [h, ↓reduceIte] at hn
      cases hn
  case rwait s => exact absurd rfl (hw s)

set_option maxHeartbeats 8000000 in
/-- **From a correction store, the lane stays in its stage's loop until a `wait::st`** (or an
undefined-behaviour event). -/
theorem corr_st_pend (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {f : Nat} {st0 : Fin 2} {c0 : Fin 8} {v0 : Correction.Control.V} {k0 : Fin 4} {n0 : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g f =
      some (some (CorrWarp.cinj p L g ⟨.rst st0 c0, v0, k0⟩ n0))) :
    ∀ q, f < q → q ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread p L) X g q = some (some σ) →
      (∃ w, f < w ∧ w < q ∧ ∃ pc, X.get (g, w) = some ⟨pc, .tc .waitSt⟩) ∨
      (∃ u, f < u ∧ u < q ∧ ∃ pc fl, X.get (g, u) = some ⟨pc, .ub fl⟩) ∨
      ∃ d n, σ = CorrWarp.cinj p L g d n ∧ StPend st0 d.site = true := by
  intro q
  induction q with
  | zero => intro h; omega
  | succ q ih =>
    intro hq hql σ' h'
    have heq : (X.tr g)[q]? = some ((X.tr g)[q]'(by omega)) := List.getElem?_eq_getElem _
    set eq := (X.tr g)[q]'(by omega)
    rw [Frame.stateAt_succ heq] at h'
    rcases hs : Frame.stateAt (thread p L) X g q with _ | _ | σ
    · rw [hs] at h'; cases h'
    · rw [hs] at h'; cases h'
    rw [hs] at h'
    -- the state before: the store's, or (after the store) one of the loop's
    have hpre : (∃ w, f < w ∧ w < q + 1 ∧ ∃ pc, X.get (g, w) = some ⟨pc, .tc .waitSt⟩) ∨
        (∃ u, f < u ∧ u < q + 1 ∧ ∃ pc fl, X.get (g, u) = some ⟨pc, .ub fl⟩) ∨
        ∃ d n, σ = CorrWarp.cinj p L g d n ∧ StPend st0 d.site = true := by
      rcases Nat.lt_or_ge f q with hfq | hfq
      · rcases ih hfq (by omega) σ hs with ⟨w, h1, h2, h3⟩ | ⟨u, h1, h2, h3⟩ | h
        · exact .inl ⟨w, h1, by omega, h3⟩
        · exact .inr (.inl ⟨u, h1, by omega, h3⟩)
        · exact .inr (.inr h)
      · have : f = q := by omega
        subst this
        rw [hσ] at hs
        simp only [Option.some.injEq] at hs
        exact .inr (.inr ⟨_, _, hs.symm, by simp [StPend]⟩)
    rcases hpre with h | h | ⟨d, n, rfl, hpd⟩
    · exact .inl h
    · exact .inr (.inl h)
    -- one step from a loop state
    have hn : (thread p L g).next (CorrWarp.cinj p L g d n) eq = some (some σ') := h'
    rw [CorrWarp.next_cinj] at hn
    obtain ⟨o, ho1, ho⟩ := Option.map_eq_some_iff.mp hn
    cases o with
    | none => cases ho
    | some d' =>
      simp only [Option.map_some, Option.some.injEq] at ho
      subst ho
      by_cases hw : ∃ s, d.site = .rwait s
      · -- the wait: its event is the `wait::st` or undefined behaviour
        obtain ⟨s, hs'⟩ := hw
        have hget : X.get (g, q) = some eq := heq
        have hfq : f < q := by
          rcases Nat.lt_or_ge f q with h | h
          · exact h
          · exfalso
            have : f = q := by omega
            subst this
            rw [hσ] at hs
            obtain ⟨site, v, k⟩ := d
            simp only at hs'
            subst hs'
            simp at hs
        by_cases ub : ∃ f, eq.kind = .ub f
        · obtain ⟨fl, hk⟩ := ub
          exact .inr (.inl ⟨q, hfq, by omega, eq.pc, fl, hget.trans (congrArg some (congrArg
              (Event.mk eq.pc) hk))⟩)
        have hu : ∀ f, eq.kind ≠ .ub f := fun f h => ub ⟨f,h⟩
        have hev := (CorrWarp.fired_both hp hX hget hs hu).1
        obtain ⟨site, v, k⟩ := d
        simp only at hs'
        subst hs'
        simp only [Correction.Control.Ev, Correction.Control.D.scheduler, Correction.Ev] at hev
        rcases hev with hk | ⟨fl, hk⟩
        · exact .inl ⟨q, by omega, by omega, eq.pc, by rw [hget, ← hk]⟩
        · exact .inr (.inl ⟨q, by omega, by omega, eq.pc, fl, by rw [hget, ← hk]⟩)
      · push Not at hw
        exact .inr (.inr ⟨d', _, rfl, pend_next hpd hw ho1⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof

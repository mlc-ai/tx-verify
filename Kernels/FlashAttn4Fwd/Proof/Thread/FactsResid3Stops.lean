-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsResid3Tmpl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreCross
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin

@[expose] public section

/-! # Where the prologue's, the loader's, the store warp's and the idle warp's machines stop

* `Cross.NextStops_pro`, `_loader`, `_store`, `_idle`: these parts of
  `Cross.NextStopsAtExitOrBadRead`. An event at a followed state fires from its site's
  instruction (`Frame.fired_site`). When the thread does not continue, the event ends it
  (`fires_none_ends`); it is not undefined behaviour, since no site has an undefined-behaviour
  template (`Cross.sitesTmplOk`), so it is the exit. When the thread continues, the role's step
  (`Prologue.step`, `Loader.step`, `Store.step`, `Idle.step_setMaxReg`) gives a successor, so
  the successor function does not reject the event.
* `Cross.NoRegReentry_loader`, `_idle`: no loader or idle step reaches the role's register
  request. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- An event at a followed state is the exit, or a continuing event of the state's site. -/
theorem Cross.exit_or_cont {g i : Nat} {d : ThreadD} {e : Event}
    (hσ : St L X g i = some (some d)) (he : X.get (g, i) = some e) :
    (∃ pc, e = ⟨pc, .exit⟩) ∨ ∃ t ins u, (code L g).AtD d t ∧ (code L g).inv d ∧
      kernel.code[(code L g).pc d]? = some ins ∧
      Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e (some u) := by
  have hg := Frame.lt_of_get hX he
  have hσ' : Frame.stateAt (code L) X g i = some (some d) := hσ
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ :=
    Frame.fired_site (C := code L) (fun _ hg => sound hpre hg) hX he hσ'
  cases o with
  | none =>
    rcases fires_none_ends hf with ⟨f, hk⟩ | hk
    · obtain ⟨pc, k⟩ := e
      simp only at hk
      subst hk
      exact absurd (fires_ub hf rfl) (Cross.sitesTmplOk hpre g hg d t ins hat hinv hc f)
    · exact .inl ⟨e.pc, by rw [← hk]⟩
  | some u => exact .inr ⟨t, ins, u, hat, hinv, hc, hf⟩

/-- **The prologue's part of `Cross.NextStopsAtExitOrBadRead`**: it stops only at the exit. -/
theorem Cross.NextStops_pro {g i : Nat} {p : Prologue.D} {e : Event}
    (hσ : St L X g i = some (some (.inl p))) (he : X.get (g, i) = some e)
    (hn : (code L g).next (.inl p) e = none) : ∃ pc, e = ⟨pc, .exit⟩ := by
  have hg := Frame.lt_of_get hX he
  refine (Cross.exit_or_cont hpre hX hσ he).resolve_right fun ⟨t, ins, u, hat, hi, hc, hf⟩ => ?_
  have hs := Prologue.step hpre hg hi ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf
  simp only [code, Option.map_eq_none_iff] at hn
  rcases hs with h | ⟨_, _, h, -⟩ <;> rw [hn] at h <;> cases h

/-- **The loader's part of `Cross.NextStopsAtExitOrBadRead`**: it stops only at the exit. -/
theorem Cross.NextStops_loader {g i : Nat} {d : Loader.D} {e : Event}
    (hσ : St L X g i = some (some (.inr (.loader d)))) (he : X.get (g, i) = some e)
    (hn : (code L g).next (.inr (.loader d)) e = none) : ∃ pc, e = ⟨pc, .exit⟩ := by
  have hg := Frame.lt_of_get hX he
  refine (Cross.exit_or_cont hpre hX hσ he).resolve_right fun ⟨t, ins, u, hat, hi, hc, hf⟩ => ?_
  have hs := Loader.step hpre hg hi ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf
  simp only [code, Option.map_eq_none_iff] at hn
  rcases hs with h | ⟨_, _, h, -⟩ <;> rw [hn] at h <;> cases h

/-- **The store warp's part of `Cross.NextStopsAtExitOrBadRead`**: it stops only at the exit. -/
theorem Cross.NextStops_store {g i : Nat} {d : Store.D} {e : Event}
    (hσ : St L X g i = some (some (.inr (.store d)))) (he : X.get (g, i) = some e)
    (hn : (code L g).next (.inr (.store d)) e = none) : ∃ pc, e = ⟨pc, .exit⟩ := by
  have hg := Frame.lt_of_get hX he
  refine (Cross.exit_or_cont hpre hX hσ he).resolve_right fun ⟨t, ins, u, hat, hi, hc, hf⟩ => ?_
  simp only [code, Option.map_eq_none_iff] at hn
  have hs := Store.step hpre hg hi ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hc hf
  rcases hs with h | ⟨_, _, h, -⟩ <;> rw [hn] at h <;> cases h

/-- **The idle warp's part of `Cross.NextStopsAtExitOrBadRead`**: it stops only at the exit. -/
theorem Cross.NextStops_idle {g i : Nat} {s : Idle.D} {e : Event}
    (hσ : St L X g i = some (some (.inr (.idle s)))) (he : X.get (g, i) = some e)
    (hn : (code L g).next (.inr (.idle s)) e = none) : ∃ pc, e = ⟨pc, .exit⟩ := by
  refine (Cross.exit_or_cont hpre hX hσ he).resolve_right fun ⟨t, ins, u, _, _, hc, hf⟩ => ?_
  simp only [code, Option.map_eq_none_iff] at hn
  obtain ⟨site⟩ := s
  cases site with
  | setMaxReg => simp [Idle.next] at hn
  | exit => exact Idle.exit_no_step rfl hc hf

end

/-! ### No step returns to the register request -/

namespace Loader

theorem itemEndOf_ne (L : Launch) (g : Nat) (d : D) :
    (afterUse.itemEndOf L g d).site ≠ .setMaxReg := by
  unfold afterUse.itemEndOf
  split_ifs <;> simp

theorem afterUse_ne (L : Launch) (g : Nat) (d : D) (u : UseK) :
    (afterUse L g d u).site ≠ .setMaxReg := by
  cases u <;> simp only [afterUse] <;> (try split_ifs) <;>
    first | exact itemEndOf_ne _ _ _ | simp

theorem afterCopy_ne (L : Launch) (g : Nat) (d : D) (u : UseK) (j : Fin 2) :
    (afterCopy L g d u j).site ≠ .setMaxReg := by
  unfold afterCopy
  split_ifs
  · simp
  · exact afterUse_ne _ _ _ _

/-- The loader's successor is never its register request. -/
theorem next_not_setMaxReg {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) : d'.site ≠ .setMaxReg := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  cases site <;> simp only [next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals first
    | exact afterCopy_ne _ _ _ _ _
    | simp

end Loader

/-- **`Cross.NoRegReentry`, loader part.** -/
theorem Cross.NoRegReentry_loader {g : Nat} {d : Loader.D} {r' : Role} {e : Event}
    (h : (code L g).next (.inr (.loader d)) e = some (some (.inr r'))) :
    nextKind (.inr r') ≠ .reg := by
  obtain ⟨r'', hr, hk⟩ := code_next_inr h
  cases hr
  cases r' with
  | loader d' =>
    have hn := next_role (fun _ _ h => Role.loader.inj h) h
    have hs := Loader.next_not_setMaxReg hn
    simp only [nextKind]
    cases hd : d'.site <;> simp_all [loaderKind]
  | _ => simp [Role.kind] at hk

/-- **`Cross.NoRegReentry`, idle part**: the idle warp's only step goes to its exit. -/
theorem Cross.NoRegReentry_idle {g : Nat} {s : Idle.D} {r' : Role} {e : Event}
    (h : (code L g).next (.inr (.idle s)) e = some (some (.inr r'))) :
    nextKind (.inr r') ≠ .reg := by
  obtain ⟨site⟩ := s
  cases site <;> simp only [code, Idle.next, Option.map_some, Option.map_none, Function.comp,
    Option.some.injEq, reduceCtorEq, Sum.inr.injEq] at h
  subst h
  simp [nextKind, idleKind]

end
end PTX.Kernels.FlashAttn4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Expect
public import Kernels.TmlFa4Fwd.Proof.Loader.RefBase
public import Kernels.TmlFa4Fwd.Proof.Loader.ShapeAll
import Kernels.TmlFa4Fwd.Proof.Loader.RefRows
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepArr
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepScan
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' reference invariant is kept by every step

`Ref` (`Ref.lean`) holds at the first state (`ref_init`) and, under it, an event of the state's
shape that returns a value of the site's kind (`Expect`) and is not undefined behaviour neither
stops the counted machine nor leads to a state that breaks it (`ref_next`), for warps 14 and 15.
The steps are the families of `RefRows.lean` (inside a packet) and `RefStep*.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

/-- The exit has no successor. -/
theorem step_exit : StepRef p L g w .exit := by
  intro v kk n e d' k A _ _ _ _ hn
  simp [succ] at hn

/-- **Every step keeps the reference invariant and follows the step spec** (`w` is 14 or 15). -/
theorem ref_post (hp : Pre p L m) (hw : w = 14 ∨ w = 15) {d : D} {n : Cnt → Nat} {e : Event}
    {d' : D} (hJ : Ref p L g w (d, n)) (hev : Ev p L g w d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g w d e = some (some d')) :
    Ref p L g w (d', Code.bump (cls L g) n e) ∧ Move L g w (d, n) e d' := by
  have hR := hJ.toRefRing
  have hC := hJ.toRefCounts
  obtain ⟨s, v, kk⟩ := d
  suffices h : Post p L g w (⟨s, v, kk⟩, n) e d' from ⟨h.1.ref, h.2⟩
  by_cases hrows : s.inRows = true
  · exact ref_step_rows hR hC hrows hev hub hn
  have h : StepRef p L g w s := by
    cases s with
    | setmax => exact step_setmax
    | word sk => exact step_word sk
    | down sk => exact step_down sk
    | up sk j => exact step_up sk j
    | total sk => exact step_total sk
    | vote l => exact step_vote l
    | pre l => exact step_pre l
    | tiles l => exact step_tiles l
    | q0 => exact step_req _ (.inl rfl)
    | q1 => exact step_req _ (.inr (.inl rfl))
    | uk => exact step_req _ (.inr (.inr rfl))
    | pgLd per it => exact step_pgLd per it
    | pgSt per it => exact step_pgSt hp per it
    | rwSt per it => exact step_rwSt hp per it
    | slot per b => exact step_slot hp per b
    | ptP per b it => exact step_ptP per b it
    | ptR per b it => exact step_ptR per b it
    | ptS per b it => exact step_ptS hp per b it
    | arrive per b => exact step_arrive hp hw per b
    | tw t => exact step_tw hp t
    | te t i => exact step_te t i
    | ta t => exact step_ta hp t
    | tc t c => exact step_tc t c
    | dw j => exact step_dw hp hw j
    | dq => exact step_dq hp
    | de => exact step_de
    | da => exact step_da hp
    | exit => exact step_exit
    | lw _ _ _ | xl _ _ _ | xh _ _ _ | cp _ _ _ _ | commit _ _ => exact absurd rfl hrows
  exact h v kk n e d' _ _ hR hC hev hub hn

/-- **Every step keeps the reference invariant** (`w` is 14 or 15). -/
theorem ref_step (hp : Pre p L m) (hw : w = 14 ∨ w = 15) {d : D} {n : Cnt → Nat} {e : Event}
    {d' : D} (hJ : Ref p L g w (d, n)) (hev : Ev p L g w d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g w d e = some (some d')) : Ref p L g w (d', Code.bump (cls L g) n e) :=
  (ref_post hp hw hJ hev hub hn).1

/-- **The step spec** (`Spec.lean`): a step from a state with the reference invariant on an event
of the state's shape that is not undefined behaviour moves as `Move` says. -/
theorem step_spec (hp : Pre p L m) (hw : w = 14 ∨ w = 15) {d : D} {n : Cnt → Nat} {e : Event}
    {d' : D} (hJ : Ref p L g w (d, n)) (hev : Ev p L g w d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hn : succ p L g w d e = some (some d')) : Move L g w (d, n) e d' :=
  (ref_post hp hw hJ hev hub hn).2

/-- The first state satisfies the reference invariant. -/
theorem ref_init : Ref p L g w (MC p L g w ent).init := by
  exact RefE.ref ⟨0, 0, ⟨fun h => by simp [Site.isTma] at h, trivial⟩, rfl, fun _ _ => rfl⟩

/-- **The `ref_next` obligation of the loader warps**: at a counted state satisfying `Ref`, an
expected event of the state's shape that is not undefined behaviour neither stops the counted
machine nor leads to a state that breaks `Ref` (for warps 14 and 15). -/
theorem ref_next (hp : Pre p L m) (hw : w = 14 ∨ w = 15) {dn : D × (Cnt → Nat)} {e : Event}
    (hi : (MC p L g w ent).inv dn) (hJ : Ref p L g w dn) (hE : Expect dn e)
    (hev : Ev p L g w dn.1 e) (hub : ∀ f, e.kind ≠ .ub f) :
    (MC p L g w ent).next dn e ≠ some none ∧
      ∀ dn', (MC p L g w ent).next dn e = some (some dn') → Ref p L g w dn' := by
  obtain ⟨d, n⟩ := dn
  refine ⟨fun h => next_ne_stop hi hev hE (Code.counted_next_none_iff.mp h), fun dn' h => ?_⟩
  obtain ⟨hn, h2⟩ := Code.counted_next_some h
  obtain ⟨d', n'⟩ := dn'
  simp only at h2 hn
  subst h2
  exact ref_step hp hw hJ hev hub hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader

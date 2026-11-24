-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepAt
public import Kernels.TmlFa4Fwd.Proof.Softmax.EvS
public import Kernels.TmlFa4Fwd.Proof.Softmax.Open
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefDef
public import Kernels.TmlFa4Fwd.Proof.Softmax.Stop
import Kernels.TmlFa4Fwd.Proof.Softmax.Safe
import Kernels.TmlFa4Fwd.Proof.Softmax.SafeBld
import Kernels.TmlFa4Fwd.Proof.Softmax.Shapes
import Kernels.TmlFa4Fwd.Proof.Softmax.Steps
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.RefNext

@[expose] public section

/-! # The softmax warps as a fragment

`frag p L g` is the softmax warps' fragment (plan §2.2): the counted machine `MC`, the shape table
without undefined behaviour (`EvS`: the event of `Ev`, and no undefined behaviour), the return
kinds `ret`, the reference invariant `Ref` and the expected values `Expect`. `ok` proves
`Fragment.Ok` from two named premises, both about the data plane, which the control-register
table does not name:

- `NumSteps`: the step obligation at the closing bias poll (`D.numeric`), whose local code
  reads data registers;
- `DataStoreSafe`: the stores of data registers (the P stores after their wait, the statistics
  and final stores) are no undefined behaviour; Core faults such a store when the register's value
  does not have four bytes, which only the data plane's facts exclude.

Every other site's template has no fault under the facts (`Safe.lean`, `SafeBld.lean`), and a site
whose shape has no undefined-behaviour alternative needs nothing more (`ev_noUb`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The sites whose shape admits undefined behaviour. -/
def Site.ubAlt : Site → Bool
  | .barEnd _ | .word _ | .q0 | .q1 | .uk | .bld _ _ | .sld _ _ | .sldw _ | .pst _ _
  | .pwst _ _ | .stat _ | .fin _ | .pws _ | .pel _ => true
  | _ => false

/-- A site whose shape has no undefined-behaviour alternative fires none. -/
theorem ev_noUb {d : D} {e : Event} (hev : Ev p L g d e) (hs : d.site.ubAlt = false) :
    NoUb d e := by
  intro f hk
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases s <;> simp [Site.ubAlt] at hs <;> simp [Ev, Epilogue.Ev, Site.toE] at hev

/-- A state its invariant excludes satisfies every shape obligation. -/
theorem shapeAt_out {P : D → Event → Prop} {d : D}
    (h : ¬ ((d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc)) :
    (codeD p L g).ShapeAt P d :=
  fun _ hi => absurd hi h

/-- **No undefined behaviour at any state**, given the data stores'. -/
theorem noUbAt (hp : Pre p L m) (hD : DataStoreSafe p L g) (d : D) :
    (codeD p L g).ShapeAt NoUb d := by
  obtain ⟨s, v, k, acc⟩ := d
  by_cases hu : s.ubAlt = false
  · intro hat hi hc hf
    exact ev_noUb (shapeAt (g := g) hp ⟨s, v, k, acc⟩ (atD_mono hat) hi hc hf) hu
  cases s with
  | bld b c => exact shapeAtD (safe_bld hp b c k v acc)
  | sldw c =>
    by_cases hk : k = 1
    · subst hk; exact shapeAtD (safe_sldw hp c v acc)
    · exact shapeAt_out (by simp [Site.first, Site.midOk, hk])
  | pst r q =>
    by_cases hdk : (Site.pst r q).delayed = true ∧ k = 0
    · obtain ⟨hd, rfl⟩ := hdk
      cases r <;> fin_cases q <;> simp [Site.delayed] at hd
      · exact shapeAtD (safe_pstw hp false v acc)
      · exact shapeAtD (safe_pstw hp true v acc)
    · refine hD _ ?_
      simp only [D.dataStore]
      by_cases hd : (Site.pst r q).delayed = true
      · have : k.val ≠ 0 := fun h => hdk ⟨hd, Fin.ext h⟩
        simp [hd, this]
      · simp [hd]
  | stat b => exact hD _ rfl
  | fin j => exact hD _ rfl
  | _ =>
    by_cases hk : k = 0
    swap
    · exact shapeAt_out (by simp [Site.first, Site.midOk, hk])
    subst hk
    first
    | exact shapeAtD (safe_barEnd hp _ v acc)
    | exact shapeAtD (safe_word hp _ v acc)
    | exact shapeAtD (safe_req hp v acc).1
    | exact shapeAtD (safe_req hp v acc).2.1
    | exact shapeAtD (safe_req hp v acc).2.2
    | exact shapeAtD (safe_sld hp _ _ v acc)
    | exact shapeAtD (safe_pwst hp _ _ v acc)
    | exact shapeAtD (safe_pws hp _ v acc)
    | exact shapeAtD (safe_pel hp _ v acc)
    | exact absurd rfl hu

theorem shapeS (hp : Pre p L m) (hD : DataStoreSafe p L g) : (codeD p L g).Shape (EvS p L g) :=
  Code.Shape.of_at fun d _ _ _ _ hat hi hc hf =>
    And.intro (shapeAt hp d (atD_mono hat) hi hc hf) (noUbAt hp hD d hat hi hc hf)

/-- **The softmax warps' fragment.** -/
@[reducible] def frag (p : Params) (L : Launch) (g : Nat) :
    Fragment kernel Assumptions.all L g where
  code := MC p L g
  Ev := fun dn e => EvS p L g dn.1 e
  ret := fun dn => ret dn.1
  Ref := Ref p L g
  Expect := Expect p L g

/-- **The fragment's obligations**, from the numeric steps and the data stores' safety. -/
theorem ok (hp : Pre p L m) (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    (hN : NumSteps p L g) (hD : DataStoreSafe p L g) : (frag p L g).Ok := fun dn =>
  { step := Code.counted_steps (stepAt hp hg hw hN dn.1) dn.2
    shape := fun hat hi hc hf => (Code.Shape.counted (shapeS hp hD)) hat hi hc hf
    stop_iff := fun hi hev => by
      rw [Code.counted_next_none_iff]; exact stop_iff dn.1 hi hev.1
    ref_next := fun _ hJ hE hev => by
      obtain ⟨h1, h2⟩ := ref_next hp hJ hE hev.1 hev.2
      exact ⟨h1, fun h => next_ends hE hev.1 (Code.counted_next_eq_none_iff.mp h), h2⟩
    ref_safe := fun _ _ hev => hev.2 }

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

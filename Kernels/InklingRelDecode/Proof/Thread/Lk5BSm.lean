-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkB0

@[expose] public section

/-!
# The softmax region's `bar.sync 0, 128` before a state, as a function of its site and iteration

The loop of the softmax region has five `bar.sync 0, 128`: `bar20`, `bar21` in every iteration,
`bar22`, `bar23` in the iterations after the first, and `bar24` on the rescale path. `phi s i`
is the number of the first four kinds before a state at site `s` of iteration `i` (from the
region's first state on): `4 i - 2` at the start of an iteration `i ≥ 1` (two in the first, four
in each later one), then `bar22`, `bar23` and the `bar20`, `bar21` of the iteration. `bar24` is
not counted (it depends on the decision at `shfl12`, the count of its states is kept apart).

* `sm_b0At`: the barrier-0 instructions of the region's sites;
* `phi_next`: a step adds its own instruction's barrier-0 event unless it is `bar24`;
* `late`: the sites from the decision at `shfl12` on; `late_next`: a step in one iteration from a
  late site goes to a late site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-- The barrier-0 instruction of a softmax site: `2` for `bar.sync 0, 128`. -/
def smB0 : Sm.Site → Nat
  | .bar20 | .bar21 | .bar22 | .bar23 | .bar24 => 2
  | _ => 0

theorem sm_b0At (s : Sm.Site) : b0At s.pc = smB0 s := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

/-- The number of the loop's `bar.sync 0, 128` other than `bar24` before a state. -/
def phi (s : Sm.Site) (i : Nat) : Int :=
  match s with
  | .waitO | .bar22 => 4 * (i : Int) - 2
  | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 => 4 * (i : Int) - 1
  | .ldL | .shfl11 | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO | .bar20 =>
    4 * (i : Int)
  | .tmemSt | .tmemWait | .bar21 => 4 * (i : Int) + 1
  | .arrive => 4 * (i : Int) + 2
  | _ => if i = 0 then 0 else 4 * (i : Int) - 2

/-- The increment of a site: its barrier-0 event, unless it is `bar24`. -/
def phiInc (s : Sm.Site) : Int :=
  match s with
  | .bar20 | .bar21 | .bar22 | .bar23 => 1
  | _ => 0

theorem toBar20_iff {d d' : Sm.D} :
    Sm.toBar20 d = some (some d') ↔ d.updOk = true ∧ d' = { d.upd with site := .bar20 } := by
  unfold Sm.toBar20
  constructor
  · intro h
    split at h
    · rename_i hu
      exact ⟨hu, (Option.some.inj (Option.some.inj h)).symm⟩
    · cases h
  · rintro ⟨h1, rfl⟩
    simp only [h1, ↓reduceIte]

/-- **A softmax step adds its own instruction's `bar.sync 0, 128`, except `bar24`'s.** -/
theorem phi_next {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some d')) :
    phi d'.site d'.i = phi d.site d.i + phiInc d.site := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;>
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup] at h <;>
    (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [toBar20_iff] at h
       obtain ⟨-, rfl⟩ := h
       simp_all [phi, phiInc, Sm.D.upd, Sm.D.afterSum] <;> omega)
    | (obtain rfl := Option.some.inj (Option.some.inj h)
       (try split_ifs) <;>
         (try simp_all [phi, phiInc, Sm.D.afterSum, Sm.D.afterMax, Sm.D.afterMaxT]) <;> omega)

/-- The sites from the decision at `shfl12` on. -/
def late : Sm.Site → Bool
  | .ldO | .waitLdO | .bar24 | .stO | .waitStO | .bar20 | .tmemSt | .tmemWait | .bar21
  | .arrive => true
  | _ => false

/-- **In one iteration, a late site goes to a late site.** -/
theorem late_next {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some d')) (hl : late d.site = true) (hi : d'.i = d.i) :
    late d'.site = true := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp [late] at hl <;>
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup] at h <;>
    (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [toBar20_iff] at h
       obtain ⟨-, rfl⟩ := h
       rfl)
    | (obtain rfl := Option.some.inj (Option.some.inj h)
       simp_all [late])

end
end PTX.Kernels.InklingRelDecode.Proof.Lk5B

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Kernel.Safety.TableU
import Lemmas.Step.ExitLast
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # How producer lemmas state undefined behaviour

A producer lemma never takes the global no-undefined-behaviour hypothesis. It takes the lane prefix
`NoUbBefore X g k` (free from `noUbBefore_of_get` at a known event), the whole-lane form
`NoUbLane`, or
`NoUbOutside L X`: an undefined-behaviour event occurs only in a data lane
(`g % L.block < 128`)
at a pc from 574 on (the softmax, the epilogue and the shared exit; the prologue's pcs are
excluded by `Prologue.Export.noUb_prologue`). Every worker lane is then fault-free
(`NoUbOutside.worker`). -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX
variable {L : Launch}

/-- The pcs of the softmax and epilogue regions and the exit. -/
def SoftEpiPc (pc : Nat) : Prop := 574 ≤ pc

/-- Undefined behaviour occurs only in a data lane at a pc from 574 on. -/
def NoUbOutside (L : Launch) (X : Execution) : Prop :=
  ∀ g k pc f, X.get (g,k) = some ⟨pc,.ub f⟩ → g % L.block < 128 ∧ SoftEpiPc pc

/-- No event of the lane is undefined behaviour. -/
def NoUbLane (X : Execution) (g : Nat) : Prop := Frame.NoUbBefore X g (X.tr g).length

/-- A worker lane (index 128 or more in its block) never faults. -/
theorem NoUbOutside.worker {L : Launch} {X : Execution} (h : NoUbOutside L X) {g : Nat}
    (hw : 128 ≤ g % L.block) : NoUbLane X g := by
  rintro j _ ⟨pc,kd⟩ he f rfl
  have := (h g j pc f he).1
  omega

/-- A lane that exited has no undefined-behaviour event: both end the lane's thread. -/
theorem NoUbLane.of_exit {m : Mem0} {X : Execution} {g k pc : Nat}
    (hX : Consistent L kernel Assumptions.all m X) (exit : X.get (g, k) = some ⟨pc, .exit⟩) :
    NoUbLane X g := by
  intro j hj e he f hf
  obtain ⟨pj, kd⟩ := e
  change kd = .ub f at hf
  subst hf
  have last := Execution.exit_last hX (Frame.lt_of_get hX exit) exit
  have le := ub_last hX he exit
  have : j = k := by change j < (X.tr g).length at hj; omega
  subst this
  rw [he] at exit
  cases exit

theorem NoUbLane.before {X : Execution} {g : Nat} (h : NoUbLane X g) (k : Nat) :
    Frame.NoUbBefore X g k := by
  intro j hj e he
  exact h j (by
    have := (List.getElem?_eq_some_iff.mp he).1
    exact this) e he

theorem NoUbLane.kind {X : Execution} {g k : Nat} {e : Event} (h : NoUbLane X g)
    (he : X.get (g,k) = some e) : ∀ f, e.kind ≠ .ub f :=
  h k (List.getElem?_eq_some_iff.mp he).1 e he

theorem NoUbBefore.mono {X : Execution} {g j k : Nat} (h : Frame.NoUbBefore X g k) (le : j ≤ k) :
    Frame.NoUbBefore X g j := fun u hu => h u (by omega)

/-- A known nonfaulting event extends the prefix of its own lane. -/
theorem NoUbBefore.succ {m : Mem0} {X : Execution} {g k : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some e)
    (hk : ∀ f, e.kind ≠ .ub f) : Frame.NoUbBefore X g (k+1) := by
  intro u hu e' he'
  rcases Nat.lt_or_ge u k with h|h
  · exact Frame.noUbBefore_of_get hX he u h e' he'
  · obtain rfl : u = k := by omega
    rw [he] at he'
    cases he'
    exact hk

theorem noUbUpto {m : Mem0} {X : Execution} {g k j : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some e)
    (hk : ∀ f, e.kind ≠ .ub f) (le : j ≤ k+1) : Frame.NoUbBefore X g j :=
  NoUbBefore.mono (NoUbBefore.succ hX he hk) le

end PTX.Kernels.InklingRelDecode.Proof

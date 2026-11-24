-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5VSm
public import Kernels.InklingRelDecode.Proof.Thread.Lk5VPro
public import Kernels.InklingRelDecode.Proof.Thread.DCompBase

@[expose] public section

/-!
# The shuffles of the common start and of the epilogue, counted by site

The common start has one shuffle (`shfl`, the broadcast of the warp index), the epilogue one
(`shfl`, skipped where `num_iters < 1`). `dsW`, `epW` count the region's shuffles before a state;
`dsW_next`, `epW_next` say a step adds one exactly at the shuffle site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace DStart

/-- The common start's shuffles before a state. -/
def dsW (d : D) : Nat := if d.site = .toProA then 1 else 0

/-- The common start's shuffle site. -/
def dsShfl (s : Site) : Bool := decide (s = .shfl)

theorem dsW_next {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) :
    dsW d' = dsW d + (if dsShfl d.site then 1 else 0) := by
  obtain ⟨s, tm⟩ := d
  cases s <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp [dsW, dsShfl])
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp at h; done)

end DStart

namespace Epi

/-- The epilogue's shuffles before a state. -/
def epW (d : D) : Nat :=
  match d.site with
  | .wait | .shfl => 0
  | .ld | .waitLd => 1
  | _ => if d.sk then 0 else 1

/-- The epilogue's shuffle site. -/
def epShfl (s : Site) : Bool := decide (s = .shfl)

/-- The sites of the branch that `num_iters < 1` skips. -/
def epLoad (s : Site) : Bool := decide (s = .shfl) || decide (s = .ld) || decide (s = .waitLd)

/-- The sites after the load (and after the poll where it is skipped). -/
def epRest (s : Site) : Bool :=
  !(decide (s = .wait) || decide (s = .shfl) || decide (s = .ld) || decide (s = .waitLd))

theorem epW_rest {d : D} (h : epRest d.site = true) : epW d = if d.sk then 0 else 1 := by
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> first | rfl | (simp [epRest] at h)

theorem epLoad_rest {s : Site} (h : epRest s = true) : epLoad s = false := by
  cases s <;> first | rfl | (exfalso; revert h; decide)

theorem stores_rest (d : D) : epRest d.stores = true := by
  unfold D.stores
  split <;> (try split) <;> decide

theorem epW_st (d : D) (pr : Prm) (o : List Value) (sk : Bool) :
    epW { site := d.stores, pr := pr, o := o, sk := sk } = if sk then 0 else 1 :=
  epW_rest (d := { site := d.stores, pr := pr, o := o, sk := sk }) (stores_rest d)

theorem stNext_rest (d : D) (k : Fin 64) : epRest (stNext d k).site = true ∧
    (stNext d k).sk = d.sk := by
  unfold stNext
  split <;> exact ⟨by simp [epRest], rfl⟩

/-- **An epilogue step adds one shuffle exactly at the shuffle site.** -/
theorem epW_next {d d' : D} {e : Event} (h : next d e = some (some d'))
    (hl : epLoad d.site = true → d.sk = false) :
    epW d' = epW d + (if epShfl d.site then 1 else 0) ∧
      (epLoad d'.site = true → d'.sk = false) := by
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       simp_all [epW, epShfl, epLoad]
       done)
    | (simp only [Option.some.injEq] at h
       subst h
       rename_i k
       obtain ⟨h1, h2⟩ := stNext_rest { site := .stO k, pr := pr, o := o, sk := sk } k
       refine ⟨?_, fun h3 => absurd h3 (by rw [epLoad_rest h1]; decide)⟩
       rw [epW_rest h1, h2]
       simp [epW, epShfl])
    | (simp only [Option.some.injEq] at h
       subst h
       refine ⟨?_, fun h3 => absurd h3 (by rw [epLoad_rest (stores_rest _)]; decide)⟩
       rw [epW_st]
       simp_all [epW, epShfl, epLoad])

end Epi

end
end PTX.Kernels.InklingRelDecode.Proof

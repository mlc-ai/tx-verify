-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkWStep

@[expose] public section

/-!
# Warp lockstep: the loop counters of the loader and of the MMA warp

The keys of `LkW` say at which site the next synchronizing state is. The loader's and the MMA
warp's branches at their loop ends also depend on the counters `i` and `n`, which the keys do not
carry. `exW` is the pair `(i, n)` that a worker state has at its next synchronizing state, as a
function of the state: it is constant along the silent steps (`exSilent_W`), and after a step of a
synchronizing state it is `stW` of that state (`exStep_W`). The counters that a silent step reads
from memory (the loader's `ld0`, `ld1` and the MMA warp's `ldNum`) are not part of the value before
the loop's first synchronizing state (`bar0`): the value is `(0, 0)` until then, and `stW` at
`bar0` is the pair the state carries.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {e : Event}

/-- The counters of a loader state at its next synchronizing state (`(0, 0)` before the loop's
entry). -/
def exL (d : Loader.D) : Nat × Nat :=
  match d.site with
  | .setMaxDec | .ld0 | .ld1 | .bar0 => (0, 0)
  | .cp3a | .cp3b => (d.i + 1, d.n)
  | _ => (d.i, d.n)

/-- The counters of an MMA state at its next synchronizing state (`(0, 0)` before the loop's
entry). -/
def exM (d : Mma.D) : Nat × Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => (0, 0)
  | .qk _ | .qkCommit => ((Mma.afterQk d).i, d.n)
  | .pv _ | .pvCommit1 | .pvCommit2 => (d.i + 1, d.n)
  | _ => (d.i, d.n)

/-- The counters of a worker state. -/
def exW : WComp.WSt → Nat × Nat
  | .loader d _ => exL d
  | .mma d _ => exM d
  | _ => (0, 0)

/-- The counters after a step of a synchronizing loader state. -/
def stL (d : Loader.D) : Nat × Nat :=
  match d.site with
  | .setMaxDec | .setMaxInc => (0, 0)
  | .el3 => (d.i + 1, d.n)
  | _ => (d.i, d.n)

/-- The counters after a step of a synchronizing MMA state. -/
def stMm (d : Mma.D) : Nat × Nat :=
  match d.site with
  | .setMaxReg | .setMaxRegInc => (0, 0)
  | .qkElect | .qkSkip => ((Mma.afterQk d).i, d.n)
  | .pvElect | .pvSkip => (d.i + 1, d.n)
  | _ => (d.i, d.n)

/-- The counters after a step of a synchronizing worker state. -/
def stW : WComp.WSt → Nat × Nat
  | .loader d _ => stL d
  | .mma d _ => stMm d
  | _ => (0, 0)

/-! ### Silent steps -/

theorem exSilent_L {d d' : Loader.D} {P : Loader.Pro}
    (h : Loader.next L g d e = some (some d')) (hs : wSy (.loader d P) = false) :
    exL d' = exL d := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub, Bool.or_false] at hs <;>
    first
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Loader.next, Loader.afterIter, Loader.readI, Loader.readN] at h
       (repeat' split at h) <;>
         first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            simp only [exL]))

theorem exSilent_M {d d' : Mma.D} {P : Loader.Pro}
    (h : Mma.next L g d e = some (some d')) (hs : wSy (.mma d P) = false) :
    exM d' = exM d := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs <;>
    first
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Mma.next, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext] at h
       (repeat' split at h)
       all_goals
         first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            simp only [exM, Mma.afterQk, Mma.iterNext]
            (repeat' split)
            all_goals (try dsimp only)
            all_goals omega))

/-- **A silent step of a worker state keeps the counters.** -/
theorem exSilent_W {s t : WComp.WSt} (h : WComp.next L g s e = some (some t))
    (hs : wSy s = false) : exW t = exW s := by
  cases s with
  | worker w =>
    have hl : w.site ≠ .ldRole := by
      obtain ⟨s, P⟩ := w
      intro hw
      simp only at hw
      subst hw
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_true] at hs
      exact absurd hs (by decide)
    rw [next_worker hl] at h
    obtain ⟨d', hd', rfl⟩ := mapInv h
    rfl
  | idle d =>
    have hl : d.site ≠ .inc := by
      obtain ⟨s, P⟩ := d
      intro hw
      simp only at hw
      subst hw
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    rw [next_idle hl] at h
    obtain ⟨d', hd', rfl⟩ := mapInv h
    rfl
  | loader d P =>
    have hl : d.site ≠ .setMaxInc := by
      obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      intro hw
      simp only at hw
      subst hw
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    rw [next_loader hl] at h
    obtain ⟨d', hd', rfl⟩ := mapInv h
    exact exSilent_L hd' hs
  | mma d P =>
    have hl : d.site ≠ .setMaxRegInc := by
      obtain ⟨s, i, n, tm, pro⟩ := d
      intro hw
      simp only at hw
      subst hw
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    rw [next_mma hl] at h
    obtain ⟨d', hd', rfl⟩ := mapInv h
    exact exSilent_M hd' hs
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site
    · exfalso
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    · simp [WComp.next] at h

/-! ### Steps of synchronizing states -/

theorem exStep_L {d d' : Loader.D} {P : Loader.Pro}
    (h : Loader.next L g d e = some (some d')) (hs : wSy (.loader d P) = true) :
    exL d' = stL d := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub, Bool.or_false] at hs <;>
    first
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Loader.next, Loader.afterIter] at h
       (repeat' split at h) <;>
         first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            simp only [exL, stL]))

theorem exStep_M {d d' : Mma.D} {P : Loader.Pro}
    (h : Mma.next L g d e = some (some d')) (hs : wSy (.mma d P) = true) :
    exM d' = stMm d := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs <;>
    first
    | (exfalso; revert hs; decide +kernel)
    | (exfalso; clear h; rename_i j; revert hs j; decide +kernel)
    | (simp only [Mma.next, Mma.afterQk, Mma.iterNext, Mma.start] at h
       (repeat' split at h)
       all_goals
         first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            simp only [exM, stMm, Mma.afterQk, Mma.iterNext]
            (repeat' split)
            all_goals (try dsimp only)
            all_goals omega))

/-- **The counters after a role's entry are `(0, 0)`.** -/
theorem roleStart_ex {P : Loader.Pro} {x : Worker.Site} {t : WComp.WSt}
    (h : WComp.roleStart L g P x = some (some t)) : exW t = (0, 0) := by
  cases x <;> simp only [WComp.roleStart] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       rfl)

/-- **A step of a synchronizing worker state has the counters `stW`.** -/
theorem exStep_W {s t : WComp.WSt} (h : WComp.next L g s e = some (some t))
    (hs : wSy s = true) : exW t = stW s := by
  cases s with
  | worker w =>
    by_cases hl : w.site = .ldRole
    · obtain ⟨s, P⟩ := w
      simp only at hl
      subst hl
      simp only [WComp.next, WComp.dispatch] at h
      split at h
      · rename_i d' hd'
        exact roleStart_ex h
      · simp at h
      · simp at h
    · rw [next_worker hl] at h
      obtain ⟨d', hd', rfl⟩ := mapInv h
      rfl
  | idle d =>
    by_cases hl : d.site = .inc
    · obtain ⟨s, P⟩ := d
      simp only at hl
      subst hl
      simp only [WComp.next, Option.some.injEq] at h
      subst h
      rfl
    · rw [next_idle hl] at h
      obtain ⟨d', hd', rfl⟩ := mapInv h
      rfl
  | loader d P =>
    by_cases hl : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hl
      subst hl
      simp only [WComp.next, Option.some.injEq] at h
      subst h
      rfl
    · rw [next_loader hl] at h
      obtain ⟨d', hd', rfl⟩ := mapInv h
      exact exStep_L hd' hs
  | mma d P =>
    by_cases hl : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hl
      subst hl
      simp only [WComp.next, Option.some.injEq] at h
      subst h
      rfl
    · rw [next_mma hl] at h
      obtain ⟨d', hd', rfl⟩ := mapInv h
      exact exStep_M hd' hs
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site
    · simp only [WComp.next, Option.some.injEq] at h
      subst h
      rfl
    · simp [WComp.next] at h

end
end PTX.Kernels.InklingRelDecode.Proof.Lk

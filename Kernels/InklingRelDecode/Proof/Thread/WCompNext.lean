-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompEntry

@[expose] public section

/-!
# The worker thread machine: what its successors preserve

The composed machine follows a role through the role's own successors, so the facts a role's
step lemmas give about its next state (`Loader.Step`, `Mma.Step`) carry over to the thread's
state once the data the thread adds (the `Pro` the role was handed) is shown to be unchanged
by them: every role successor changes the site and the counters only, never the registers the
role inherited (`pro`, and for the MMA warp the Tensor Memory base `tm`). The dispatch's
successor is one of the four role entries, with the inherited registers it had.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.WComp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro Pro.val Pro.table)

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {e : Event}

/-! ### The dispatch -/

/-- A role byte leads to the entry of one of the four roles, or, if it is above 3, to the barriers
of the branch the code takes; the inherited registers are unchanged. -/
theorem dispatch_some {P : Pro} {bs : List (Option Byte)} {d' : Worker.D}
    (h : Worker.dispatch P bs = some (some d')) :
    d'.P = P ∧ (d'.site = .toLoader ∨ d'.site = .toMma ∨ d'.site = .toIdle ∨
      d'.site = .toExit ∨ d'.site = .bad0) := by
  unfold Worker.dispatch at h
  cases hr : rebuild 3 bs with
  | error f => simp [hr] at h
  | ok v =>
    cases hx : extendLoaded (MemExt.zero 32) 8 v with
    | error f => simp [hr, hx] at h
    | ok w =>
      obtain ⟨y, rfl⟩ := Worker.extend_zero_bits hx
      simp only [hr, hx, Option.some.injEq] at h
      subst h
      refine ⟨rfl, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k, (truncBits 32 y).toNat = k := ⟨_, rfl⟩
      rw [hk]
      match k with
      | 0 => simp [Worker.roleSite]
      | 1 => simp [Worker.roleSite]
      | 2 => simp [Worker.roleSite]
      | 3 => simp [Worker.roleSite]
      | k + 4 => simp [Worker.roleSite]

/-! ### The roles' successors keep the inherited registers -/

/-- A loader successor keeps the inherited registers, except the two loaded words. -/
theorem loader_next_pro {d d' : Loader.D}
    (h : Loader.next L g d e = some (some d')) :
    ∀ r, r ≠ 1905 → r ≠ 467 → d'.pro r = d.pro r :=
  Loader.next_pro h

/-- An MMA successor keeps the inherited registers and the Tensor Memory base. -/
theorem mma_next_pro {d d' : Mma.D}
    (h : Mma.next L g d e = some (some d')) :
    (∀ r, r ≠ 471 → d'.pro r = d.pro r) ∧ d'.tm = d.tm := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       exact ⟨fun r hr => by simp [Function.update_of_ne hr], rfl⟩)

/-! ### Where the MMA warp's machine follows the thread -/

/-- **The MMA warp's machine follows the thread** at every state: the loaded `num_iters` word and
the two broadcasts' received words are followed for every value (an unreadable or bitless word is a
fault, `none`), and the last event returns to the dispatch. -/
theorem mma_next_follows {d : Mma.D} (P : Pro) :
    next L g (.mma d P) e ≠ some none := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;>
    simp only [next, Mma.next, Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext] <;>
    (repeat' split) <;> simp_all

/-- **The worker's machine follows the thread** at every state but the broadcast of the warp
index (`shfl`), the dispatch (`ldRole`, whose role byte, warp and Tensor Memory base word
`roleStart` checks) and the four role-entry sites (never states: the dispatch steps into the
role's first state). -/
theorem worker_next_follows {w : Worker.D}
    (h : w.site = .bar0 ∨ w.site = .ld0 ∨ w.site = .bar1 ∨ w.site = .loop ∨ w.site = .bar2 ∨
      w.site = .bad0 ∨ w.site = .bad1) :
    next L g (.worker w) e ≠ some none := by
  obtain ⟨s, P⟩ := w
  rcases h with h | h | h | h | h | h | h <;> simp only at h <;> subst h <;>
    simp only [next, Worker.next] <;> (repeat' split) <;> simp_all

/-- The idle roles' machine follows the thread at every state. -/
theorem idle_next_follows (d : Worker.Idle.D) : next L g (.idle d) e ≠ some none := by
  obtain ⟨s, P⟩ := d
  cases s <;> simp [next, Worker.Idle.next]

/-- The exit role's machine follows the thread at every state. -/
theorem exit_next_follows (x : ExitD) : next L g (.exit x) e ≠ some none := by
  obtain ⟨s, P⟩ := x
  cases s <;> simp [next]

/-- **The loader's machine follows the thread** at every state: every loaded word is followed, a
read whose bytes do not rebuild and a word the code cannot read as bits are faults (`none`), and
the last event returns to the dispatch. -/
theorem loader_next_follows {d : Loader.D} (P : Pro) :
    next L g (.loader d P) e ≠ some none := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;>
    simp only [next, Loader.next, Loader.afterIter, Loader.readI, Loader.readN] <;>
    (repeat' split) <;> simp_all

end
end PTX.Kernels.InklingRelDecode.Proof.WComp

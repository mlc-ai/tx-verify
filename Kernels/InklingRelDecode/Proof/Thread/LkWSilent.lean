-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkW

@[expose] public section

/-!
# Warp lockstep: the worker warps, silent states

A state that is not synchronizing keeps its key through any step (`w_silent`), role by role.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {e : Event}

/-! ### The composed successor, role by role -/

/-- A successor under `Option.map` of a successor of a role's machine. -/
theorem mapInv {α β : Type} {f : α → β} {x : Option (Option α)} {b : β}
    (h : x.map (Option.map f) = some (some b)) : ∃ a, x = some (some a) ∧ f a = b := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a => exact ⟨a, rfl, by simpa using h⟩

theorem next_worker {w : Worker.D} (hl : w.site ≠ .ldRole) :
    WComp.next L g (.worker w) e = (Worker.next L g w e).map (Option.map .worker) := by
  obtain ⟨s, P⟩ := w
  cases s <;> first | rfl | exact absurd rfl hl

theorem next_idle {d : Worker.Idle.D} (hl : d.site ≠ .inc) :
    WComp.next L g (.idle d) e = (Worker.Idle.next d e).map (Option.map .idle) := by
  obtain ⟨s, P⟩ := d
  cases s <;> first | rfl | exact absurd rfl hl

theorem next_loader {d : Loader.D} {P : Loader.Pro} (hl : d.site ≠ .setMaxInc) :
    WComp.next L g (.loader d P) e =
      (Loader.next L g d e).map (Option.map (fun d' => .loader d' P)) := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> first | rfl | exact absurd rfl hl

theorem next_mma {d : Mma.D} {P : Loader.Pro} (hl : d.site ≠ .setMaxRegInc) :
    WComp.next L g (.mma d P) e =
      (Mma.next L g d e).map (Option.map (fun d' => .mma d' P)) := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> first | rfl | exact absurd rfl hl

/-! ### Silent states, role by role -/

theorem silent_W {d d' : Worker.D} (h : Worker.next L g d e = some (some d'))
    (hs : wSy (.worker d) = false) : wkW d' = wkW d := by
  obtain ⟨s, Q⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs <;>
    first
    | (exfalso; revert hs; decide +kernel)
    | (simp only [Worker.next] at h
       (repeat' split at h) <;>
         first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            simp only [wkW]
            decide +kernel))

theorem silent_I {d d' : Worker.Idle.D}
    (_h : Worker.Idle.next d e = some (some d')) (hs : wSy (.idle d) = false) :
    wkI d' = wkI d := by
  obtain ⟨s, Q⟩ := d
  cases s <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs <;>
    (exfalso; revert hs; decide +kernel)

theorem silent_L {d d' : Loader.D} {P : Loader.Pro}
    (h : Loader.next L g d e = some (some d')) (hs : wSy (.loader d P) = false) :
    wkL d' = wkL d := by
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
            simp only [wkL, Loader.sub]
            (repeat' split)
            all_goals first | decide +kernel | omega))

theorem silent_M {d d' : Mma.D} {P : Loader.Pro}
    (h : Mma.next L g d e = some (some d')) (hs : wSy (.mma d P) = false) :
    wkM d' = wkM d := by
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
            simp only [wkM, Mma.afterQk, Mma.iterNext]
            (repeat' split)
            all_goals (try dsimp only)
            all_goals first | decide +kernel | omega))

/-- **A state that is not synchronizing keeps its key through any step.** -/
theorem w_silent {s t : WComp.WSt} (h : WComp.next L g s e = some (some t))
    (hs : wSy s = false) : wKey L g t = wKey L g s := by
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
    exact silent_W hd' hs
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
    exact silent_I hd' hs
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
    exact silent_L hd' hs
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
    exact silent_M hd' hs
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site
    · exfalso
      simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at hs
      revert hs
      decide +kernel
    · simp [WComp.next] at h

end
end PTX.Kernels.InklingRelDecode.Proof.Lk

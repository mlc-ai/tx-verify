-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Sites

@[expose] public section

/-! # The reference invariant of the CarryLoad phase is kept: the steps

From the invariant at a position (`RefAt`), what the machine's successor is and that it
satisfies the invariant of the next position, or the exit condition:

* `st_ld`: at carry load `j`, the successor across the event is `ldNext0 e f` (the event is a
  read whose four bytes have a value `v`; the next state is `f v`), and every `f v` is at the
  next position (load `j + 1`, or the proxy fence after load 127) with its invariant. The
  pointer run behind the load always continues: its condition is that the address of the next
  load, before the swizzle, is inside the shared window (`Lib.lean: ldAddr_frame`). The loaded
  value `v` only goes to the carry register, about which the invariant says nothing.
* `st_fence`: the successor of the proxy fence is the exit state at `bar_5`.
* `st_bar`: the exit state's own successor (the transition of the barrier at 1402) is a state:
  the transition has no condition.

`keep_frame`: the registers of `Conversion.Keep` are words and predicates; a transition that
only rewrites opaque slots keeps them. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value} {e : Event}

/-- **The kept registers do not depend on the site and on the opaque slots**: a state with the
same word and predicate files has them. -/
theorem keep_frame {s s' : Site} {x x' : Nat → Value} (h : Keep P g ⟨s, w, p, x⟩) :
    Keep P g ⟨s', w, p, x'⟩ := by
  obtain ⟨⟨b1, b2, b3⟩, hf, hr, ⟨s1, s2, s3, s4⟩, he⟩ := h
  exact ⟨⟨b1, b2, b3⟩, hf, hr, ⟨s1, s2, s3, s4⟩, he⟩

/-- The state at the entry of the phase is at the first position of the thread's role: the
first carry load for a compute thread, the proxy fence for the others. -/
theorem entry_at {d : D} (h : Entry P g d) :
    ∃ pos, RefAt P g pos d ∧ done g pos = 0 := by
  by_cases hc : tid g < 128
  · refine ⟨.ld 0, ⟨?_, h.keep, hc, h.base hc, h.first hc⟩, rfl⟩
    have hs := h.site
    simp only [hc, ↓reduceIte] at hs
    exact hs
  · refine ⟨.fence, ⟨?_, h.keep, trivial⟩, ?_⟩
    · have hs := h.site
      simp only [hc, ↓reduceIte] at hs
      exact hs
    · simp only [done, hc, ↓reduceIte]

/-- **A step from carry load `j`**: the machine's successor is `ldNext0 e f`, and for every
loaded value `v` the state `f v` is at the next position, which has `j + 1` events of the
phase before it. -/
theorem st_ld (hpre : Pre P L mem0) (j : Fin 128)
    (h : RefAt P g (.ld j) ⟨(Pos.ld j).site, w, p, x⟩) (e : Event) :
    ∃ f : Value → D, Thread.next L g ⟨(Pos.ld j).site, w, p, x⟩ e = ldNext0 e f ∧
      ∀ v, ∃ pos', RefAt P g pos' (f v) ∧ done g pos' = j.val + 1 := by
  obtain ⟨-, hk, hc, hb, hp⟩ := h
  by_cases hj : j.val < 127
  · have hj1 : j.val + 1 < 128 := by omega
    have hfr := (ldAddr_frame hpre hc hj1).2.2.2.2
    refine ⟨_, next_ld hj hb hfr e, fun v =>
      ⟨.ld ⟨j.val + 1, hj1⟩, ⟨rfl, keep_frame hk, hc, ?_, ?_⟩, rfl⟩⟩
    · exact (two_ne (dst_ne_base j.isLt).symm (ptr_ne_base _).symm).trans hb
    · exact one_eq _ _ _
  · have hj' : j.val = 127 := by omega
    have hs : (Pos.ld j).site = ldSite 127 := by
      show ldSite j.val = ldSite 127
      rw [hj']
    rw [hs]
    refine ⟨_, next_last e, fun v => ⟨.fence, ⟨rfl, keep_frame hk, trivial⟩, ?_⟩⟩
    simp only [done, hc, ↓reduceIte, hj']

/-- **The step from the proxy fence**: the successor is the exit state at `bar_5`. -/
theorem st_fence (h : RefAt P g .fence ⟨.fenceProxy 1, w, p, x⟩) :
    Thread.next L g ⟨.fenceProxy 1, w, p, x⟩ e = some (some ⟨.bar 5, w, p, x⟩) ∧
      Exit P g ⟨.bar 5, w, p, x⟩ :=
  ⟨Thread.next_fenceProxy_1 w p x e, keep_frame h.keep, rfl⟩

/-- **The step from the exit state**: the transition of the barrier at 1402 is a state. -/
theorem st_bar :
    Thread.next L g ⟨.bar 5, w, p, x⟩ e = some (some (after_bar_5 L g ⟨.bar 5, w, p, x⟩)) :=
  Thread.next_bar_5 w p x e

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad

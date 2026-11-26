-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Exports
public import Kernels.FlashKdaFwd.Proof.Thread.Never

@[expose] public section

/-! # Tracking: the machine follows every thread

The generated machine gives up (`next d e = some none`) only at one of the 21 loads of the
offsets array, when the bytes read rebuild to a value that is not a 64-bit integer
(`Thread.next_giveUp`). All 21 loads are in the startup phase, and at a state of that phase the
reference invariant places the read inside the array, where the assumption `inputReadOnly` and
`Pre.offsets` make it return a 64-bit integer (`startup_followed`). So every launched thread is
followed (`Frame.Tracked`), given one fact about the later phases, `Later P L X`
(`Startup/Shfl.lean`): a followed state of a thread that has left the startup phase is at no
site of the startup phase, in particular at none of these loads (`Later.notLoad`). Each later
phase's invariant says at which sites its states are.

Soundness of the machine (`Thread.sound`) and consistency are used; tracking is the conclusion,
not a hypothesis.

`shflWarp`: with tracking and the fact that a shuffle event is fired only at a shuffle site
(`Ref/Kinds/Event.lean: shfl_sites`), every shuffle of every launched thread returned a value
whose word is the thread's warp index: the complete form of the hypothesis `ShflWarp` of
`Trace.lean`. No theorem of the phase needs it (the invariant uses only the first three
shuffles, `Shfl.lean: shfl_first`); it is stated for the record. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every launched thread is followed by its machine.** -/
theorem tracked (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hlater : Later P L X) : Frame.Tracked (code L) X := by
  have hC := sounds hpre
  refine Frame.tracked_of fun g k d e hg he hσ hn => ?_
  obtain ⟨j, hsite, hj, a, bs, v, hk, -, -⟩ := next_giveUp L g d e hn
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases startup_inv hpre hX hg hklt hσ with hI | hleft
  · have h3 : ((X.tr g).take (k + 1)).countP Execution.isShfl ≤ 3 := by
      obtain ⟨pos, -, hl⟩ := hI
      have h1 : ((X.tr g).take k).countP Execution.isShfl = (led g pos).shfls :=
        congrArg Led.shfls hl
      have h2 := count_snoc Execution.isShfl he
      have h4 := led_shfls_le g pos
      have h5 : Execution.isShfl e = false := by
        obtain ⟨pc, kd⟩ := e
        simp only at hk
        subst hk
        rfl
      simp only [h5, Bool.false_eq_true, ↓reduceIte] at h2
      omega
    exact startup_followed hpre hC hX hg he hσ hI
      (retEv_upto hpre hX (shfl_first hpre hC hX hg h3) (Nat.lt_succ_self k) he) hn
  · rw [hlater.notLoad g k d j hg hleft hσ hsite] at hj
    cases hj

/-- **Every shuffle of a launched thread returned a value whose word is the thread's warp
index.** `hlater` is what the later phases owe (their sites are not startup sites). -/
theorem shflWarp (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hlater : Later P L X) : ∀ g < L.threads, ShflWarp X g := by
  have hC := sounds hpre
  intro g hg k pc b c md a v ok he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, hσ⟩ := Frame.event_state hC hX (tracked hpre hX hlater) he
    (fun _ _ h => by cases h)
  rcases startup_inv hpre hX hg hk hσ with ⟨pos, hr, hl⟩ | hleft
  · have h1 : ((X.tr g).take k).countP Execution.isShfl = (led g pos).shfls :=
      congrArg Led.shfls hl
    have h2 := count_snoc Execution.isShfl he
    simp only [Execution.isShfl, ↓reduceIte] at h2
    have h3 : (led g pos).shfls < 3 := by
      obtain ⟨site, w, p, x⟩ := s
      obtain rfl : site = pos.site := hr.site
      obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site hC hX he hσ
      have hev := ev_full hpre hg pos hr hat hc hf
      rcases pos with j | j | j | j | j | j | _ | j | _ <;>
        simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
          false_and] at hev
      rw [led_shfl]
      exact j.isLt
    exact shfl_first hpre hC hX hg (k := k + 1) (by omega) (Nat.lt_succ_self k) he
  · exact (hlater.noShfl hpre hX hg hleft hσ he).elim

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup

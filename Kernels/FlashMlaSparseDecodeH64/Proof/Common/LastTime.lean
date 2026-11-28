-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
public import Lemmas.Kernel.Progress.NextEv

@[expose] public section

/-! # A lane's time at its trace's end

The glued table's time of a lane (`Sched.threadTime (timed P L)`) is `0`, the time of its state
at the trace's end, or one past the time of its state before the last event when the machine
stops at that event (`time_last`). For the roles' time exports: a property of every such time
follows from the three cases, and the third one only at states where the machine can stop
(`tma_arr_next`: never at the TMA lane's arrivals). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {X : Execution} {g : Nat}

/-- **The three cases of a lane's time.** -/
theorem time_last {Q : Nat → Prop} (h0 : Q 0)
    (h1 : ∀ σ, Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ) →
      Q (time P L g σ))
    (h2 : ∀ σ f, Frame.stateAt (thread P L) X g ((X.tr g).length - 1) = some (some σ) →
      (X.tr g)[(X.tr g).length - 1]? = some f → (thread P L g).toMachine.next (some σ) f = none →
      Q (time P L g σ + 1)) :
    Q (Sched.threadTime (timed P L) X g) := by
  rw [timed_eq]
  unfold Sched.threadTime
  cases hs : Frame.stateAt (thread P L) X g (X.tr g).length with
  | some o =>
    cases o with
    | none => exact h0
    | some σ => exact h1 σ hs
  | none =>
    simp only
    cases hs' : Frame.stateAt (thread P L) X g ((X.tr g).length - 1) with
    | none => exact h0
    | some o =>
      cases o with
      | none => exact h0
      | some σ =>
        have hpos : 0 < (X.tr g).length := by
          rcases Nat.eq_zero_or_pos (X.tr g).length with h | h
          · rw [h, Frame.stateAt_zero] at hs
            cases hs
          · exact h
        obtain ⟨f, hf⟩ : ∃ f, (X.tr g)[(X.tr g).length - 1]? = some f :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hn := Frame.stateAt_succ (C := thread P L) hf
        rw [Nat.sub_add_cancel hpos, hs, hs'] at hn
        exact h2 σ f hs' hf hn.symm

/-- **The TMA lane's machine moves on at its arrivals.** -/
theorem tma_arr_next {d : Tma.D} {n : Cls → Nat} {f : Event}
    (hs : d.site = .rawArrive ∨ d.site = .coordFree) :
    (thread P L g).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)) f ≠ none := by
  rcases hs with hs | hs <;>
    simp [Code.toMachine, Code.glue, Code.withStubs, Code.withStubsAt, frag, wg1Code, subFrag,
      tmaCode, Tma.succ, hs]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

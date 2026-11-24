-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Select

@[expose] public section

/-!
# The thread machine family of the bound layer

The bound layer (`Proof/Bound/Goal.lean`, `Bound.threadCode L Q g`) follows thread `g` by the
selected component machine itself: `DComp.code L g Q` if `g % L.block < 128`, else
`WComp.code L g Q`. `selectCode` is that family, written the same way; the interface's
`threadCode` is the machine whose states are the sum of the two components' states, so that
statements about abstract states need no dependent type. `tracked_select` shows that following
every thread by the sum machine is following it by the selected component machine, so the
interface's `tracked` supplies the bound layer's `htr`
(`Bound.threadCode L Q` unfolds to `selectCode L Q`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The bound layer's family of thread machines. -/
def selectCode (L : Launch) (Q : Params) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  if g % L.block < 128 then DComp.code L g Q else WComp.code L g Q

variable {L : Launch} {g : Nat} {Q : Params} {X : Execution}

/-- **A machine that embeds another's states follows its runs.** -/
theorem after_map {C1 C2 : Flow.Code kernel asms L g} (f : C1.D → C2.D)
    (hn : ∀ d e, C2.next (f d) e = (C1.next d e).map (Option.map f)) :
    ∀ (es : List Event) (σ : Option C1.D),
      C2.toMachine.after (σ.map f) es = (C1.toMachine.after σ es).map (Option.map f) := by
  intro es
  induction es with
  | nil => intro σ; rfl
  | cons e es ih =>
    intro σ
    cases σ with
    | none => exact ih none
    | some d =>
      have h1 : C2.toMachine.next (some (f d)) e = (C1.next d e).map (Option.map f) := hn d e
      have h2 : C1.toMachine.next (some d) e = C1.next d e := rfl
      show (C2.toMachine.next (some (f d)) e).bind (fun σ' => C2.toMachine.after σ' es) =
        Option.map (Option.map f)
          ((C1.toMachine.next (some d) e).bind (fun σ' => C1.toMachine.after σ' es))
      rw [h1, h2]
      cases C1.next d e with
      | none => rfl
      | some o => exact ih o

/-- **Following every thread by the sum machine is following it by the selected component
machine**: the interface's `tracked` is the bound layer's `htr`. -/
theorem tracked_select (ht : Frame.Tracked (code L Q) X) : Frame.Tracked (selectCode L Q) X := by
  intro g k hg h
  apply ht g k hg
  by_cases hd : g % L.block < 128
  · have hc : selectCode L Q g = DComp.code L g Q := by
      simp only [selectCode, hd, ↓reduceIte]
    have h' : (DComp.code L g Q).toMachine.after (some (DComp.code L g Q).init)
        ((X.tr g).take k) = some none := by
      have : Frame.stateAt (selectCode L Q) X g k = some none := h
      unfold Frame.stateAt at this
      rw [hc] at this
      exact this
    have key := after_map (C1 := DComp.code L g Q) (C2 := threadCode L g Q) TSt.d
      (fun d e => next_d d e) ((X.tr g).take k) (some (DComp.code L g Q).init)
    have hi : (threadCode L g Q).init = .d (DComp.code L g Q).init := by
      simp only [threadCode, hd, ↓reduceIte]
    show (threadCode L g Q).toMachine.after (some (threadCode L g Q).init) _ = some none
    rw [hi]
    simpa [h'] using key
  · have hc : selectCode L Q g = WComp.code L g Q := by
      simp only [selectCode, hd, ↓reduceIte]
    have h' : (WComp.code L g Q).toMachine.after (some (WComp.code L g Q).init)
        ((X.tr g).take k) = some none := by
      have : Frame.stateAt (selectCode L Q) X g k = some none := h
      unfold Frame.stateAt at this
      rw [hc] at this
      exact this
    have key := after_map (C1 := WComp.code L g Q) (C2 := threadCode L g Q) TSt.w
      (fun d e => next_w d e) ((X.tr g).take k) (some (WComp.code L g Q).init)
    have hi : (threadCode L g Q).init = .w (WComp.code L g Q).init := by
      simp only [threadCode, hd, ↓reduceIte]
    show (threadCode L g Q).toMachine.after (some (threadCode L g Q).init) _ = some none
    rw [hi]
    simpa [h'] using key

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

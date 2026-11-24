-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PollSynced

@[expose] public section

/-! # Polls of one position, by round

A thread that polls at a position in a loop polls there once per round, spinning on failed polls
until one succeeds. The round of a poll is the number of successful polls at its position before
it (`pollRound`). `PollSynced` follows from three facts (`PollSynced.of_rounds`):

* the object and the parity of a poll are a function of the thread's warp, the position and the
  round;
* every poll branch is selected with `uniPoll` (ASM-POLL-AGREE), so two lanes polling one object
  in one round need no order;
* two distinct lanes of a warp polling at one position in different rounds, when they poll
  different objects or at a branch no assumption selects, are ordered: an event the lane in the
  earlier round performs after its poll precedes the other lane's poll in the execution-dependency
  order (`PollRoundsMet`). -/

namespace PTX

noncomputable section

/-- A successful poll at position `pc`. -/
def okPollAt (pc : Nat) : Event → Bool
  | ⟨pc', .wait _ _ true _ _⟩ => pc' == pc
  | _ => false

/-- The round of a poll at position `pc` after the events `es`: the successful polls at `pc`
among them. -/
def pollRound (pc : Nat) (es : List Event) : Nat := es.countP (okPollAt pc)

/-- Two threads of one warp, in the other order. -/
theorem SameWarp.symm {L : Launch} {g h : Nat} (hw : SameWarp L g h) : SameWarp L h g :=
  ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩

/-- Two distinct lanes of a warp polling at one position whose next instruction is a poll branch
(`Kernel.pollBranch`) in different rounds, when they poll different objects or at a branch that no
assumption selects with `uniPoll`: the lane in the earlier round is ordered before the other. -/
def PollRoundsMet (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop :=
  ∀ g h k k' pc m m' p p' ok ok' acq acq' sc sc', g < L.threads → h < L.threads → g ≠ h →
    SameWarp L g h → X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
    X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩ → K.pollBranch (pc + 1) = true →
    (m ≠ m' ∨ A.any (·.uniPoll (pc + 1)) = false) →
    pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k') →
    PollBefore L K X (g, k) (h, k')

/-- **Polls are synchronized** when the object and the parity of each poll are a function `R` of
the thread's warp (through `key`, equal on the lanes of a warp), the position and the round,
every poll branch is selected with `uniPoll`, and lanes in different rounds of a position are
met. -/
theorem PollSynced.of_rounds {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}
    {κ : Type}
    (key : Nat → κ) (R : κ → Nat → Nat → Loc × Nat) (hkey : ∀ {g h}, SameWarp L g h → key g = key h)
    (hR : ∀ {g k pc m p ok acq sc}, g < L.threads →
      X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩ →
      R (key g) pc (pollRound pc ((X.tr g).take k)) = (m, p % 2))
    (hsel : ∀ pc, K.pollBranch (pc + 1) = true → A.any (·.uniPoll (pc + 1)) = true)
    (hord : PollRoundsMet L K A X) : PollSynced L K A X := by
  intro g h k k' pc m m' p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hpb hd
  rcases Nat.lt_trichotomy (pollRound pc ((X.tr g).take k)) (pollRound pc ((X.tr h).take k'))
    with hlt | heq | hgt
  · exact .inl (hord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hh hgh hw he he' hpb hd hlt)
  · have h1 := hR hg he
    have h2 := hR hh he'
    rw [heq, hkey hw, h2] at h1
    simp only [Prod.mk.injEq] at h1
    rcases hd with hd | hd
    · exact absurd h1.1.symm hd
    · rw [hsel pc hpb] at hd
      cases hd
  · exact .inr (hord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh hg (Ne.symm hgh) hw.symm he' he hpb
      (hd.imp Ne.symm id) hgt)

end

end PTX

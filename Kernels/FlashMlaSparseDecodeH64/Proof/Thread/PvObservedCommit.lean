-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents

@[expose] public section

/-! # The own PV commit before any observed covering commit -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PvObservedCommit

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i observe block : Nat} {k : Fin 8}

private def phase (step block : Nat) : Wg1Mma.D :=
  ⟨if h : step < 8 then .pvMma ⟨step, h⟩ else .pvCommit, block⟩

private theorem advance {n : Nat}
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩)))
    (hn : k.val + n ≤ 8) (hlen : i + n ≤ (X.tr g).length) :
    Frame.stateAt (Machine.code P L) X g (i + n) =
      some (some (.mma (phase (k.val + n) block))) := by
  induction n with
  | zero =>
    simpa only [Nat.add_zero, phase, dite_eq_left k.isLt, Fin.eta] using hd
  | succ n ih =>
    have hj : i + n < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i + n) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
    have hstage : k.val + n < 8 := by omega
    rw [Nat.add_succ, Frame.stateAt_succ he, ih (by omega) hj.le, Option.bind_some]
    change Machine.next P L g (.mma (phase (k.val + n) block)) e =
      some (some (.mma (phase (k.val + (n + 1)) block)))
    simp [Machine.next, Wg1Mma.next, Wg1Mma.nextSite, phase, hstage, Nat.add_assoc]

/-- A commit tracking an actual PV issue cannot be issued before that PV block's own commit.
The own commit immediately follows the remaining PV issues of the block. -/
theorem own_commit_of_observed (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.pvMma k, block⟩)))
    (hTrack : TracksMma X (g, i) (g, observe)) :
    ∃ own tag sp, i + (8 - k.val) = own ∧ own ≤ observe ∧
      X.get (g, own) = some ⟨tag, .tc (.commit sp)⟩ ∧
      Frame.stateAt (Machine.code P L) X g own = some (some (.mma ⟨.pvCommit, block⟩)) := by
  obtain ⟨_, hBefore, _, _, tag, hObserve⟩ := hTrack
  have hBefore : i < observe := hBefore
  have hLen : observe < (X.tr g).length := PTX.len_of_get hObserve
  have hg := Frame.lt_of_get hX hObserve
  have hk := k.isLt
  let own := i + (8 - k.val)
  have hTime : own ≤ observe := by
    by_contra! h
    let n := observe - i
    have hStage : k.val + n < 8 := by dsimp [own, n] at *; omega
    have hn : i + n = observe := by dsimp [n]; omega
    have hState := advance hd hStage.le (show i + n ≤ (X.tr g).length by omega)
    rw [hn, phase, dite_eq_left hStage] at hState
    obtain ⟨_, hf⟩ := (Frame.trace hs hX hg).fired_at hObserve hState
    have hCommit := RingCommitEvents.commit_site hf rfl
    rcases hCommit with h | h | h <;> cases h
  have hOwnLt : own < (X.tr g).length := lt_of_le_of_lt hTime hLen
  have hStep : k.val + (8 - k.val) = 8 := by omega
  have hState := advance hd (n := 8 - k.val) hStep.le hOwnLt.le
  rw [hStep] at hState
  change Frame.stateAt (Machine.code P L) X g own =
    some (some (.mma ⟨.pvCommit, block⟩)) at hState
  obtain ⟨e, he⟩ : ∃ e, X.get (g, own) = some e := ⟨_, List.getElem?_eq_getElem hOwnLt⟩
  obtain ⟨_, hf⟩ := (Frame.trace hs hX hg).fired_at he hState
  obtain ⟨sp, hk, _, _⟩ := RingCommitEvents.commit_issue hpre hg (.inr (.inr rfl)) hf
  obtain ⟨tag, kind⟩ := e
  change kind = .tc (.commit sp) at hk
  subst kind
  exact ⟨own, tag, sp, rfl, hTime, he, hState⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PvObservedCommit

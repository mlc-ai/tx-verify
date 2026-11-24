-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.WarpScan
public import Lemmas.Step.WarpShfl

@[expose] public section

namespace PTX

noncomputable section

/-- Counts both ballot and mode votes, as required by the vote instance rule. -/
def isWarpVote (mask : Nat) (e : Event) : Bool :=
  (voteClass e.kind).any (·.mask == mask)

abbrev isFullWarpVote : Event → Bool := isWarpVote (2 ^ 32 - 1)

theorem countP_take_ballot {X : Execution} {g j pc mask : Nat} {input : Bool}
    {word : BitVec 32} (he : X.get (g, j) = some ⟨pc, .vote mask input word⟩) :
    ((X.tr g).take (j + 1)).countP (isWarpVote mask) =
      ((X.tr g).take j).countP (isWarpVote mask) + 1 :=
  Flow.countP_take_succ he (by simp only [isWarpVote, voteClass, Option.any_some, beq_self_eq_true])

/-- All lanes have the same counts of shuffles and full-mask votes before their respective
trace positions. The positions may differ because lanes can execute different ordinary events. -/
structure WarpOrdinals (L : Launch) (X : Execution) (g : Nat) (pos : Nat → Nat)
    (shuffles votes : Nat) : Prop where
  shfl : ∀ lane < 32,
    ((X.tr (warpLane L g lane)).take (pos lane)).countP Execution.isShfl = shuffles
  vote : ∀ lane < 32,
    ((X.tr (warpLane L g lane)).take (pos lane)).countP isFullWarpVote = votes

/-- Moving over ordinary trace events preserves the collective ordinals. -/
theorem WarpOrdinals.advance {L : Launch} {X : Execution} {g : Nat} {pos : Nat → Nat}
    {shuffles votes : Nat} (h : WarpOrdinals L X g pos shuffles votes)
    (ordinary : Nat → List Event)
    (hPrefix : ∀ lane < 32, ∃ suffix,
      (X.tr (warpLane L g lane)).drop (pos lane) = ordinary lane ++ suffix)
    (hShfl : ∀ lane < 32, (ordinary lane).countP Execution.isShfl = 0)
    (hVote : ∀ lane < 32, (ordinary lane).countP isFullWarpVote = 0) :
    WarpOrdinals L X g (fun lane => pos lane + (ordinary lane).length) shuffles votes := by
  have advance (test : Event → Bool) (n : Nat) (old : ∀ lane < 32,
      ((X.tr (warpLane L g lane)).take (pos lane)).countP test = n)
      (skip : ∀ lane < 32, (ordinary lane).countP test = 0) :
      ∀ lane < 32,
        ((X.tr (warpLane L g lane)).take (pos lane + (ordinary lane).length)).countP test = n := by
    intro lane hl
    obtain ⟨suffix, hDrop⟩ := hPrefix lane hl
    rw [List.take_add, hDrop, List.take_append_length, List.countP_append, old lane hl,
      skip lane hl, Nat.add_zero]
  exact ⟨advance _ _ h.shfl hShfl, advance _ _ h.vote hVote⟩

variable {L : Launch} {K : Kernel} {A : List Assumption}

/-- An identified shuffle rules out the exited case for its own ordinal. -/
theorem ShflK.not_exited {m : Mem0} {X : Execution} (hX : Consistent L K A m X) {g j n : Nat}
    (hg : g < L.threads) (hK : X.ShflK (g, j) n) : ¬ ShflExited X g n := by
  rintro ⟨k, pc, he, hc⟩
  obtain ⟨⟨pc', mode, a, b, c, recv, ok, hs⟩, hn⟩ := hK
  have hLast := Execution.exit_last hX hg he
  have hJ : j < (X.tr g).length := List.getElem?_eq_some_iff.mp hs |>.1
  have hne : j ≠ k := by
    rintro rfl
    rw [he] at hs
    cases hs
  have hLe := Flow.countP_take_mono Execution.isShfl (X.tr g) (show j + 1 ≤ k by omega)
  rw [Flow.countP_take_succ hs rfl, hn] at hLe
  omega

/-- The observed next shuffle in each lane has the shared ordinal. Advancing past those
events adds a shuffle in every lane. -/
theorem WarpOrdinals.shuffle {L : Launch} {X : Execution} {g : Nat} {pos : Nat → Nat}
    {shuffles votes : Nat} (h : WarpOrdinals L X g pos shuffles votes)
    (pc : Nat → Nat) (mode : ShflMode) (a recv : Nat → Value)
    (b c : Nat → Nat) (ok : Nat → Bool)
    (hEvent : ∀ lane < 32, X.get (warpLane L g lane, pos lane) =
      some ⟨pc lane, .shfl mode (a lane) (b lane) (c lane) (recv lane) (ok lane)⟩) :
    (∀ lane < 32, X.ShflK (warpLane L g lane, pos lane) shuffles) ∧
      WarpOrdinals L X g (fun lane => pos lane + 1) (shuffles + 1) votes := by
  refine ⟨fun lane hl => ⟨⟨_, _, _, _, _, _, _, hEvent lane hl⟩, h.shfl lane hl⟩, ?_, ?_⟩
  · intro lane hl
    rw [Flow.countP_take_succ (hEvent lane hl) rfl, h.shfl lane hl]
  · intro lane hl
    rw [List.take_add_one]
    rw [show (X.tr (warpLane L g lane))[pos lane]? = _ from hEvent lane hl]
    simp only [Option.toList_some, List.countP_append, List.countP_singleton, isFullWarpVote,
      isWarpVote, voteClass, Option.any_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact h.vote lane hl

/-- A shuffle of the entire warp returns the actual source lane's operand and validity bit.
Each source is present because its trace contains the shuffle of this ordinal. -/
theorem WarpOrdinals.shuffle_value {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    (hBlock : L.block % 32 = 0) {g : Nat} (hg : g < L.threads) {pos : Nat → Nat}
    {shuffles votes : Nat} (h : WarpOrdinals L X g pos shuffles votes) (pc : Nat → Nat)
    (mode : ShflMode) (a recv : Nat → Value) (b c : Nat → Nat) (ok : Nat → Bool)
    (hEvent : ∀ lane < 32, X.get (warpLane L g lane, pos lane) =
      some ⟨pc lane, .shfl mode (a lane) (b lane) (c lane) (recv lane) (ok lane)⟩) :
    ∀ lane < 32, let source := shflSource mode lane (b lane) (c lane)
      recv lane = a source.1 ∧ ok lane = source.2 := by
  intro lane hl
  dsimp only
  let source := (shflSource mode lane (b lane) (c lane)).1
  have hs : source < 32 := Step.shflSource_lt mode hl _ _
  have hLane : laneOf L (warpLane L g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hSrcThread : warpLane L g source < L.threads := (Step.sameWarp_lane hBlock hg hs).1.1.2.1
  have hSource : warpLane L g lane - laneOf L (warpLane L g lane) +
      (shflSource mode (laneOf L (warpLane L g lane)) (b lane) (c lane)).1 =
        warpLane L g source := by
    rw [hLane]
    change warpLane L g lane - lane + source = warpLane L g source
    unfold warpLane
    omega
  have hk := (h.shuffle pc mode a recv b c ok hEvent).1
  have hLive := ShflK.not_exited hX hSrcThread (hk source hs)
  have hRecv := Flow.shfl_source_value hX (hEvent lane hl) (hk lane hl)
    (by rw [hSource]; exact hEvent source hs) (by rw [hSource]; exact hk source hs)
    (by rw [hSource]; exact hLive)
  exact ⟨hRecv.1, by simpa only [hLane] using hRecv.2⟩

/-- Observed full-mask ballots form one live instance. Both ballot and mode votes are counted
before it, so the instance uses the Core full-mask vote ordinal. -/
theorem WarpOrdinals.ballot {L : Launch} {X : Execution} {g : Nat} {pos : Nat → Nat}
    {shuffles votes : Nat} (h : WarpOrdinals L X g pos shuffles votes)
    (pc : Nat → Nat) (input : Nat → Bool) (word : Nat → BitVec 32)
    (hEvent : ∀ lane < 32, X.get (warpLane L g lane, pos lane) =
      some ⟨pc lane, .vote (2 ^ 32 - 1) (input lane) (word lane)⟩) :
    (∀ lane < 32, X.MaskK voteClass (warpLane L g lane, pos lane) (2 ^ 32 - 1) votes) ∧
      MaskInstance L voteClass X g (2 ^ 32 - 1) votes .ballot (fun lane => some (input lane)) ∧
      WarpOrdinals L X g (fun lane => pos lane + 1) shuffles (votes + 1) := by
  have hOrdinal (lane : Nat) (hl : lane < 32) :
      X.MaskK voteClass (warpLane L g lane, pos lane) (2 ^ 32 - 1) votes :=
    ⟨⟨_, _, hEvent lane hl, rfl, rfl⟩, h.vote lane hl⟩
  refine ⟨hOrdinal, ?_, ?_, ?_⟩
  · intro lane hl
    have hBit : (2 ^ 32 - 1 : Nat).testBit lane = true := by
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      exact hl
    exact ⟨fun _ => .inl ⟨_, _, _, _, hEvent lane hl, rfl, hOrdinal lane hl, rfl⟩,
      fun hf => (Bool.noConfusion (hBit.symm.trans hf))⟩
  · intro lane hl
    rw [List.take_add_one]
    rw [show (X.tr (warpLane L g lane))[pos lane]? = _ from hEvent lane hl]
    simp only [Option.toList_some, List.countP_append, List.countP_singleton, Execution.isShfl,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero, h.shfl lane hl]
  · intro lane hl
    exact (countP_take_ballot (hEvent lane hl)).trans (congrArg (· + 1) (h.vote lane hl))

/-- The next continuing event of a terminated run is present at the run's actual trace
position, and the remaining run starts at the following position. -/
theorem Next.continuing_at {X : Execution} {g pos : Nat} {t s : TState} {tm : Tmpl}
    (hn : Next K A L g t s tm) (hContinue : ∀ e, ¬ Fires s.pc tm e none)
    (hr : Run K A L g t ((X.tr g).drop pos) none) :
    ∃ e u, X.get (g, pos) = some e ∧ Fires s.pc tm e (some u) ∧
      Run K A L g u ((X.tr g).drop (pos + 1)) none := by
  cases hTail : (X.tr g).drop pos with
  | nil =>
    rw [hTail] at hr
    cases hr
  | cons e es =>
    have hRest : (X.tr g).drop (pos + 1) = es := by
      rw [← List.drop_drop, hTail]
      rfl
    rw [hTail] at hr
    obtain ⟨u, hf, hu⟩ := hn.continuing_event (hContinue e) hr
    refine ⟨e, u, ?_, hf, hRest.symm ▸ hu⟩
    change (X.tr g)[pos]? = some e
    rw [show (X.tr g)[pos]? = ((X.tr g).drop pos)[0]? by simp, hTail]
    rfl

/-- A terminated run already at its next full-mask ballot supplies the observed event
and the post-ballot cursor with the ordinal required by the Core vote rule. -/
theorem Next.ballot_at {X : Execution} {g pos : Nat} {t s : TState} {input : Bool} {ordinal : Nat}
    {step : BitVec 32 → TState} (hn : Next K A L g t s (.vote (2 ^ 32 - 1) input step))
    (hr : Run K A L g t ((X.tr g).drop pos) none)
    (hCount : ((X.tr g).take pos).countP isFullWarpVote = ordinal) :
    ∃ word, X.get (g, pos) = some ⟨s.pc, .vote (2 ^ 32 - 1) input word⟩ ∧
      X.MaskK voteClass (g, pos) (2 ^ 32 - 1) ordinal ∧
      Run K A L g (step word) ((X.tr g).drop (pos + 1)) none := by
  obtain ⟨e, u, he, hf, hRest⟩ := hn.continuing_at (by
    rintro e ⟨word, _, hNone⟩
    cases hNone) hr
  obtain ⟨word, rfl, ht⟩ := hf
  obtain rfl := Option.some.inj ht
  exact ⟨word, he, ⟨⟨_, _, he, rfl, rfl⟩, hCount⟩, hRest⟩

end
end PTX

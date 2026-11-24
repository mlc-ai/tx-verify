-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals
public import Lemmas.Step.WarpVote
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.WarpScan
public import Lemmas.Step.WarpShfl

@[expose] public section

namespace PTX

noncomputable section

section
variable {L : Launch} {K : Kernel} {A : List Assumption}

/-- Read the next continuing event of a prefix whose suffix contains an event. -/
theorem Next.continuing_at_nonempty {X : Execution} {g pos : Nat} {t s : TState} {tm : Tmpl}
    {o : Option TState} (hn : Next K A L g t s tm) (hContinue : ∀ e, ¬ Fires s.pc tm e none)
    (hr : Run K A L g t ((X.tr g).drop pos) o) (hne : (X.tr g).drop pos ≠ []) :
    ∃ e u, X.get (g, pos) = some e ∧ Fires s.pc tm e (some u) ∧
      Run K A L g u ((X.tr g).drop (pos + 1)) o := by
  cases hTail : (X.tr g).drop pos with
  | nil => exact (hne hTail).elim
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

/-- A scheduler read observed at a site that later events cannot revisit has the
footprint of its first read template, irrespective of the returned bytes. -/
theorem Next.uniqueScalarReadAt {X : Execution} {g i j site reg : Nat} {t s : TState}
    {o : Option TState} {a observed : Acc} {data : List (Option Byte)}
    (hn : Next K A L g t s (.read a (afterLoad s [reg]))) (hPc : s.pc = site)
    (hr : Run K A L g t ((X.tr g).drop i) o) (hi : i ≤ j)
    (he : X.get (g,j) = some ⟨site, .rd observed data⟩)
    (hSuffix : ∀ u events, site < u.pc → Run K A L g u events o → ∀ e ∈ events, site < e.pc) :
    j = i ∧ observed = a := by
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hMore : (X.tr g).drop i ≠ [] :=
    fun h => Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hi)
  obtain ⟨_, _, hRead, ⟨bytes, _, rfl, hRet⟩, hTail⟩ :=
    hn.continuing_at_nonempty (by rintro _ ⟨_, _, _, hBad⟩; cases hBad) hr hMore
  obtain rfl := Option.some.inj hRet
  rcases Nat.eq_or_lt_of_le hi with rfl | hLater
  · rw [he] at hRead
    exact ⟨rfl, (Kind.rd.inj (congrArg Event.kind (Option.some.inj hRead))).1⟩
  · have hIndexed : ((X.tr g).drop (i + 1))[j - (i + 1)]? = some ⟨site, .rd observed data⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
      exact he
    cases hValue : rebuild 3 bytes with
    | error f =>
      have hFault : (afterLoad s [reg] bytes).fault = some f := by rw [afterLoad, hValue]
      cases hTail.eventOfFault hFault hIndexed
    | ok v =>
      have hFloor : site < (afterLoad s [reg] bytes).pc := by simp [afterLoad, hValue, hPc]
      have hEventFloor := hSuffix _ _ hFloor hTail _ (List.mem_of_getElem? hIndexed)
      exact (Nat.lt_irrefl site hEventFloor).elim

/-- The next shuffle and successor cursor of a consistent execution prefix. -/
theorem Next.shuffle_at_nonempty {X : Execution} {g pos : Nat} {t s : TState} {mode : ShflMode}
    {a : Value} {b c ordinal : Nat} {step : Value → Bool → TState} {o : Option TState}
    (hn : Next K A L g t s (.shfl mode a b c step)) (hr : Run K A L g t ((X.tr g).drop pos) o)
    (hne : (X.tr g).drop pos ≠ []) (hCount : ((X.tr g).take pos).countP Execution.isShfl = ordinal)
    :
    ∃ recv ok, X.get (g, pos) = some ⟨s.pc, .shfl mode a b c recv ok⟩ ∧
      X.ShflK (g, pos) ordinal ∧ Run K A L g (step recv ok) ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨e, u, he, hf, hRest⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨recv, ok, _, hNone⟩
    cases hNone) hr hne
  obtain ⟨recv, ok, rfl, ht⟩ := hf
  obtain rfl := Option.some.inj ht
  exact ⟨recv, ok, he, ⟨⟨_, _, _, _, _, _, _, he⟩, hCount⟩, hRest⟩

/-- The next full-mask ballot and successor cursor of a consistent execution prefix. -/
theorem Next.ballot_at_nonempty {X : Execution} {g pos : Nat} {t s : TState} {input : Bool}
    {ordinal : Nat} {step : BitVec 32 → TState} {o : Option TState}
    (hn : Next K A L g t s (.vote (2 ^ 32 - 1) input step))
    (hr : Run K A L g t ((X.tr g).drop pos) o) (hne : (X.tr g).drop pos ≠ [])
    (hCount : ((X.tr g).take pos).countP isFullWarpVote = ordinal) :
    ∃ word, X.get (g, pos) = some ⟨s.pc, .vote (2 ^ 32 - 1) input word⟩ ∧
      X.MaskK voteClass (g, pos) (2 ^ 32 - 1) ordinal ∧
      Run K A L g (step word) ((X.tr g).drop (pos + 1)) o := by
  obtain ⟨e, u, he, hf, hRest⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨word, _, hNone⟩
    cases hNone) hr hne
  obtain ⟨word, rfl, ht⟩ := hf
  obtain rfl := Option.some.inj ht
  exact ⟨word, he, ⟨⟨_, _, he, rfl, rfl⟩, hCount⟩, hRest⟩

private theorem hasNoExitWhenSuffixEmpty {X : Execution} {g pos : Nat}
    (hEmpty : (X.tr g).drop pos = [])
    (hPrefix : ∀ j < pos, ∀ pc, X.get (g, j) ≠ some ⟨pc, .exit⟩)
    {j pc : Nat} (he : X.get (g, j) = some ⟨pc, .exit⟩) : False := by
  have hLen : (X.tr g).length ≤ pos := List.drop_eq_nil_iff.mp hEmpty
  exact hPrefix j (lt_of_lt_of_le (List.getElem?_eq_some_iff.mp he).1 hLen) pc he

/-- Once one lane has returned from a shuffle, every peer with the same prefix ordinal
and with no exit before its cursor has a remaining event. -/
theorem WarpOrdinals.shuffle_suffix_nonempty {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g : Nat} {pos : Nat → Nat} {shuffles votes : Nat} (hs : WarpOrdinals L X g pos shuffles votes)
    (hb : L.block % 32 = 0) (hg : g < L.threads) {src i pc : Nat} (hsrc : src < 32)
    {mode : ShflMode} {a r : Value} {b c : Nat} {ok : Bool}
    (he : X.get (warpLane L g src, i) = some ⟨pc, .shfl mode a b c r ok⟩)
    (hk : X.ShflK (warpLane L g src, i) shuffles) {lane : Nat} (hl : lane < 32)
    (hPrefix : ∀ j < pos lane, ∀ p, X.get (warpLane L g lane, j) ≠ some ⟨p, .exit⟩) :
    (X.tr (warpLane L g lane)).drop (pos lane) ≠ [] := by
  intro hEmpty
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hb hg hsrc).1) (Step.sameWarp_lane hb hg hl).1
  rcases Step.shfl_lane_of_ready hX he hk hWarp with ⟨j, hj⟩ | ⟨j, p, hj, _⟩
  · have hTake : (X.tr (warpLane L g lane)).take (pos lane) = X.tr (warpLane L g lane) :=
      List.take_of_length_le (List.drop_eq_nil_iff.mp hEmpty)
    have hCount := hs.shfl lane hl
    rw [hTake] at hCount
    have hNext : shuffles < (X.tr (warpLane L g lane)).countP Execution.isShfl :=
      Step.ShflK.lt_count hj
    omega
  · exact hasNoExitWhenSuffixEmpty hEmpty hPrefix hj

/-- A returned full-mask ballot gives the same peer progress as a returned shuffle. -/
theorem WarpOrdinals.ballot_suffix_nonempty {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g : Nat} {pos : Nat → Nat} {shuffles votes : Nat} (hs : WarpOrdinals L X g pos shuffles votes)
    (hb : L.block % 32 = 0) (hg : g < L.threads) {src i : Nat} (hsrc : src < 32)
    (hk : X.MaskK voteClass (warpLane L g src, i) (2 ^ 32 - 1) votes) {lane : Nat} (hl : lane < 32)
    (hPrefix : ∀ j < pos lane, ∀ p, X.get (warpLane L g lane, j) ≠ some ⟨p, .exit⟩) :
    (X.tr (warpLane L g lane)).drop (pos lane) ≠ [] := by
  intro hEmpty
  have hWarp := Step.sameWarp_trans
    (sameWarp_symm (Step.sameWarp_lane hb hg hsrc).1) (Step.sameWarp_lane hb hg hl).1
  have hBit : (2 ^ 32 - 1 : Nat).testBit (laneOf L (warpLane L g lane)) = true := by
    have hLane : laneOf L (warpLane L g lane) = lane := (Step.sameWarp_lane hb hg hl).2
    rw [hLane, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hl
  rcases Step.vote_lane_of_ready hX hk hWarp hBit with ⟨j, hj⟩ | ⟨j, p, hj⟩
  · have hTake : (X.tr (warpLane L g lane)).take (pos lane) = X.tr (warpLane L g lane) :=
      List.take_of_length_le (List.drop_eq_nil_iff.mp hEmpty)
    have hCount := hs.vote lane hl
    rw [hTake] at hCount
    have hNext := Step.MaskK.lt_count hj
    change votes < (X.tr (warpLane L g lane)).countP isFullWarpVote at hNext
    omega
  · exact hasNoExitWhenSuffixEmpty hEmpty hPrefix hj
end

/-- A particular observed event is still ahead of the issuing lane's cursor. Each peer
has reached its own cursor without exiting. -/
structure WarpFollowsEvent (L : Launch) (X : Execution) (g : Nat) (pos : Nat → Nat)
    (src index : Nat) (target : Event) : Prop where
  lane : src < 32
  get : X.get (warpLane L g src, index) = some target
  before : pos src ≤ index
  noExit : ∀ lane < 32, ∀ j < pos lane, ∀ pc,
    X.get (warpLane L g lane, j) ≠ some ⟨pc, .exit⟩

/-- The issuing lane has a readable suffix until the observed event is consumed. -/
theorem WarpFollowsEvent.nonempty {L : Launch} {X : Execution} {g src index : Nat}
    {pos : Nat → Nat} {e : Event} (h : WarpFollowsEvent L X g pos src index e) :
    (X.tr (warpLane L g src)).drop (pos src) ≠ [] := by
  intro hn
  exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp h.get).1
    ((List.drop_eq_nil_iff.mp hn).trans h.before)

/-- Successful continuing events keep the witness in the issuing lane's new suffix
if the next observed event differs from the witness. -/
theorem WarpFollowsEvent.after {L : Launch} {X : Execution} {g src index : Nat}
    {pos nextPos : Nat → Nat} {e : Event} (h : WarpFollowsEvent L X g pos src index e)
    (hPastSrc : nextPos src ≤ index)
    (hKeep : ∀ lane < 32, ∀ j < nextPos lane, pos lane ≤ j → ∀ pc,
      X.get (warpLane L g lane, j) ≠ some ⟨pc, .exit⟩) :
    WarpFollowsEvent L X g nextPos src index e := by
  refine ⟨h.lane, h.get, hPastSrc, ?_⟩
  intro lane hl j hj pc
  by_cases hEarlier : j < pos lane
  · exact h.noExit lane hl j hEarlier pc
  · exact hKeep lane hl j hj (Nat.le_of_not_gt hEarlier) pc

/-- If each lane has just performed a continuing event, no lane can have exited before
its successor position. -/
theorem noExitThroughContinuingEvent {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g pos : Nat} (hg : g < L.threads) {e : Event} (he : X.get (g, pos) = some e)
    (hEvent : e.kind ≠ .exit) {j : Nat} (hj : j < pos + 1) (pc : Nat) :
    X.get (g, j) ≠ some ⟨pc, .exit⟩ := by
  intro hExit
  have hLast := Execution.exit_last hX hg hExit
  have hLen : pos < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hEq : j = pos := by omega
  subst j
  exact hEvent (congrArg Event.kind (Option.some.inj (he.symm.trans hExit)))

variable {L : Launch} {K : Kernel} {A : List Assumption} {m : Mem0} {X : Execution}
    (hX : Consistent L K A m X) {g : Nat}
include hX

/-- Supply the peer suffix needed for a common shuffle from an observed event on one lane. -/
theorem WarpFollowsEvent.shuffleSuffix {pos : Nat → Nat} {shuffles votes : Nat}
    (hs : WarpOrdinals L X g pos shuffles votes) (hb : L.block % 32 = 0) (hg : g < L.threads)
    {src index : Nat} {target : Event} (h : WarpFollowsEvent L X g pos src index target)
    {t s : TState} {mode : ShflMode} {a : Value} {b c : Nat} {step : Value → Bool → TState}
    {o : Option TState} (hn : Next K A L (warpLane L g src) t s (.shfl mode a b c step))
    (hr : Run K A L (warpLane L g src) t ((X.tr (warpLane L g src)).drop (pos src)) o) :
    ∀ lane < 32, (X.tr (warpLane L g lane)).drop (pos lane) ≠ [] := by
  obtain ⟨_, _, he, hk, _⟩ := hn.shuffle_at_nonempty hr h.nonempty (hs.shfl _ h.lane)
  exact fun lane hl => hs.shuffle_suffix_nonempty hX hb hg h.lane he hk hl (h.noExit lane hl)

/-- Advance the witness over a continuing event observed at the same PC in each lane. -/
theorem WarpFollowsEvent.afterCommonEvent {pos : Nat → Nat} (hb : L.block % 32 = 0)
    (hg : g < L.threads) {src index pc : Nat} {target : Event}
    (h : WarpFollowsEvent L X g pos src index target) (hPc : pc < target.pc)
    (hEvent : ∀ lane < 32, ∃ e,
      X.get (warpLane L g lane, pos lane) = some e ∧ e.pc = pc ∧ e.kind ≠ .exit) :
    WarpFollowsEvent L X g (fun lane => pos lane + 1) src index target := by
  refine ⟨h.lane, h.get, ?_, ?_⟩
  · obtain ⟨e, hSrc, hAt, _⟩ := hEvent src h.lane
    cases Nat.eq_or_lt_of_le h.before with
    | inl he =>
      rw [he] at hSrc
      have hEq := congrArg Event.pc (Option.some.inj (hSrc.symm.trans h.get))
      exact (Nat.ne_of_lt hPc (hAt.symm.trans hEq)).elim
    | inr hlt => exact hlt
  · intro lane hl j hj p
    obtain ⟨_, he, _, hKind⟩ := hEvent lane hl
    exact noExitThroughContinuingEvent hX (Step.sameWarp_lane hb hg hl).1.1.2.1
      he hKind hj p

/-- Advance the witness over a common shuffle, whose PC is before the witnessed event. -/
theorem WarpFollowsEvent.afterShuffle {pos : Nat → Nat} (hb : L.block % 32 = 0) (hg : g < L.threads)
    {src index pc : Nat} {target : Event} (h : WarpFollowsEvent L X g pos src index target)
    (hPc : pc < target.pc) (mode : ShflMode) (a r : Nat → Value) (b c : Nat → Nat) (ok : Nat → Bool)
    (hEvent : ∀ lane < 32, X.get (warpLane L g lane, pos lane) =
      some ⟨pc, .shfl mode (a lane) (b lane) (c lane) (r lane) (ok lane)⟩) :
    WarpFollowsEvent L X g (fun lane => pos lane + 1) src index target := by
  apply h.afterCommonEvent hX hb hg hPc
  exact fun lane hl => ⟨_, hEvent lane hl, rfl, by intro he; cases he⟩

/-- Supply the peer suffix needed for a ballot from an observed event on one lane. -/
theorem WarpFollowsEvent.ballotSuffix {pos : Nat → Nat} {shuffles votes : Nat}
    (hs : WarpOrdinals L X g pos shuffles votes) (hb : L.block % 32 = 0) (hg : g < L.threads)
    {src index : Nat} {target : Event} (h : WarpFollowsEvent L X g pos src index target)
    {t s : TState} {input : Bool} {step : BitVec 32 → TState} {o : Option TState}
    (hn : Next K A L (warpLane L g src) t s (.vote (2 ^ 32 - 1) input step))
    (hr : Run K A L (warpLane L g src) t ((X.tr (warpLane L g src)).drop (pos src)) o) :
    ∀ lane < 32, (X.tr (warpLane L g lane)).drop (pos lane) ≠ [] := by
  obtain ⟨_, _, hk, _⟩ := hn.ballot_at_nonempty hr h.nonempty (hs.vote _ h.lane)
  exact fun lane hl => hs.ballot_suffix_nonempty hX hb hg h.lane hk hl (h.noExit lane hl)

end
end PTX

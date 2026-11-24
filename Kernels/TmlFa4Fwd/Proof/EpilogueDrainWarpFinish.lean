-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFinish
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem ballotOperand (hp : Pre p l m) {g i : Nat} {t : TState} {pred : Bool}
    {F : List (Nat × Value)} (ht : At t 3092 ((332, .pred pred) :: F))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ word, X.get (g, i) = some ⟨3092, .vote (2 ^ 32 - 1) pred word⟩ := by
  have hPC := ht.1
  have hout := (epilogue_out_all_eq_nil (l := l) (g := g) (.inl ⟨by omega, by omega⟩)).trans
    (drainBallotTemplate hp g t pred hPC ht.2.2.2.1 ht.2.2.2.2.1)
  have hn : Next kernel Assumptions.all l g t t
      (.vote (2 ^ 32 - 1) pred (fun word => next (setReg t 2446 (b32 word.toNat)))) :=
    ⟨.refl, hout⟩
  obtain ⟨e, _, he, ⟨word, hEq, _⟩, _⟩ := hn.continuing_at (by
    rintro e ⟨word, _, hbad⟩
    cases hbad) hr
  exact ⟨word, by rw [he, hEq, hPC]⟩

/-- Read a tail shuffle's source and index from the current lane, before its return is known. -/
private theorem indexOperand (hp : Pre p l m) (previous : Bool) {g i src index : Nat} {t : TState}
    (hIndex : index < 32) (hPC : t.pc = (if previous then 3097 else 3098)) (hf : t.fault = none)
    (hSrc : t.regs (if previous then 7233 else 7232) = some (b32 src))
    (hIdx : t.regs (if previous then 2447 else 1214) = some (b32 index))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ recv ok, X.get (g, i) = some
      ⟨if previous then 3097 else 3098, .shfl .idx (b32 src) index 31 recv ok⟩ ∧
      Run kernel Assumptions.all l g
        (next (setReg t (if previous then 2448 else 2449) recv)) ((X.tr g).drop (i + 1)) none := by
  have hlo : 2768 ≤ t.pc := by cases previous <;> simp [hPC]
  have hhi : t.pc ≤ 3100 := by cases previous <;> simp [hPC]
  have hn : Next kernel Assumptions.all l g t t (.shfl .idx (b32 src) index 31
      (fun value _ => next (setReg t (if previous then 2448 else 2449) value))) :=
    ⟨.refl, (epilogue_out_all_eq_nil (.inl ⟨hlo, hhi⟩)).trans
      (drainTailShuffle hp previous g t src index hIndex hPC hf hSrc hIdx)⟩
  obtain ⟨e, _, he, ⟨recv, ok, hEq, hState⟩, hTail⟩ := hn.continuing_at (by
    rintro e ⟨recv, ok, _, hbad⟩
    cases hbad) hr
  obtain rfl := Option.some.inj hState
  exact ⟨recv, ok, by rw [he, hEq, hPC], hTail⟩

/-- The common popcount determines whether the first IDX shuffle is present. Both source
operands can be read from the trace without presupposing either shuffle's return value. -/
private theorem tailIndexOperands (hp : Pre p l m) {g i n lanePrefix laneTiles : Nat} {t : TState}
    (hN : n < 32)
    (ht : At t 3095 [(1214, b32 n), (333, .pred (decide (n = 0))),
      (7233, b32 lanePrefix), (7232, b32 laneTiles), (1062, b32 13)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    (0 < n → ∃ recv ok, X.get (g, i) = some
      ⟨3097, .shfl .idx (b32 lanePrefix) (n - 1) 31 recv ok⟩) ∧
      ∃ recv ok, X.get (g, if n = 0 then i else i + 1) =
        some ⟨3098, .shfl .idx (b32 laneTiles) n 31 recv ok⟩ := by
  have hPC := ht.1
  have hf := ht.2.2.2.1
  have hLane := ht.2.2.2.2.1
  have hPred := ht.2.2.2.2.2.1
  have hPrefix := ht.2.2.2.2.2.2.1
  have hTiles := ht.2.2.2.2.2.2.2.1
  have hBranch := epilogueLocalStep (by omega) (by omega) (drainBallotBranch l g t _ hPC hf hPred)
  by_cases hZero : n = 0
  · refine ⟨by omega, ?_⟩
    have hStep : Tau kernel Assumptions.all l g t {t with pc := 3098} := by
      apply tauStep_iff.mp
      simpa only [hZero, decide_true, ite_true] using hBranch
    obtain ⟨recv, ok, he, _⟩ := indexOperand hp false (t := {t with pc := 3098}) hN rfl hf
      hTiles hLane (hRun.after_local (.single hStep))
    exact ⟨recv, ok, by rw [ite_eq_left hZero]; exact he⟩
  · have hNZ : 0 < n := by omega
    have hStep : Tau kernel Assumptions.all l g t (skip t) := by
      apply tauStep_iff.mp
      simpa only [hZero, decide_false, Bool.false_eq_true, ite_false] using hBranch
    have hpv : (skip t).pc = 3096 := by simp [skip, hPC]
    have hv : At (skip t) 3096 [(1214, b32 n)] := ⟨hpv, rfl, rfl, hf, hLane, trivial⟩
    obtain ⟨v, hvRun, hvAt⟩ := drainPreviousLane l g hNZ hN _ hv
    obtain ⟨hvAll, hvFrame, _, _⟩ := epilogueLinearRun (F := [2447]) (t := skip t) (n := 1)
      (by omega) (by omega) (by omega) (by
        intro _
        rw [hpv]
        exact ⟨_, Flow.code_3096, by simp [writesRegs]⟩) hv.2.1 hv.2.2.1 hvRun
    obtain ⟨recv, ok, he, hTail⟩ := indexOperand hp true
      (show n - 1 < 32 by omega) hvAt.1 hvAt.2.2.2.1
      ((hvFrame 7233 (by decide)).trans hPrefix) hvAt.2.2.2.2.1
      (hRun.after_local ((Relation.ReflTransGen.single hStep).trans (run_rtg hvAll)))
    have hu : (next (setReg v 2448 recv)).pc = 3098 := by
      change v.pc + 1 = 3098
      rw [hvAt.1]
    obtain ⟨recv', ok', he', _⟩ := indexOperand hp false hN hu hvAt.2.2.2.1
      (by simpa [next, setReg] using (hvFrame 7232 (by decide)).trans hTiles)
      (by simpa [next, setReg] using (hvFrame 1214 (by decide)).trans hLane) hTail
    exact ⟨fun _ => ⟨recv, ok, he⟩, recv', ok', by rw [ite_eq_right hZero]; exact he'⟩

private theorem chooseLaneWords {α : Type} {P : Nat → α → Prop}
    (fallback : α) (h : ∀ lane < 32, ∃ x, P lane x) :
    ∃ f : Nat → α, ∀ lane < 32, P lane (f lane) := by
  classical
  let f (lane : Nat) := if hl : lane < 32 then Classical.choose (h lane hl) else fallback
  exact ⟨f, fun lane hl => by simpa [f, hl] using Classical.choose_spec (h lane hl)⟩

private theorem sourceThread {l : Launch} {g lane source : Nat}
    (hBlock : l.block % 32 = 0) (hg : g < l.threads) (hl : lane < 32) :
    warpLane l g lane - laneOf l (warpLane l g lane) + source = warpLane l g source := by
  have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  rw [hLane]
  unfold warpLane
  omega

private theorem alignIndexed {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (hBlock : l.block % 32 = 0)
    {g pc idx shuffles votes : Nat} {pos : Nat → Nat} {words : Nat → Value}
    (hg : g < l.threads) (hi : idx < 32) (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hs : ∀ lane < 32, ∃ recv ok, X.get (warpLane l g lane, pos lane) =
      some ⟨pc, .shfl .idx (words lane) idx 31 recv ok⟩) :
    (∀ lane < 32, DrainShufflePeer l X (warpLane l g lane) (pos lane)
      pc (words lane) idx (words idx)) ∧
      WarpOrdinals l X g (fun lane => pos lane + 1) (shuffles + 1) votes := by
  have hh : ∀ lane < 32, ∃ r : Value × Bool,
      X.get (warpLane l g lane, pos lane) = some ⟨pc, .shfl .idx (words lane) idx 31 r.1 r.2⟩ := by
    intro lane hl
    obtain ⟨recv, ok, he⟩ := hs lane hl
    exact ⟨(recv, ok), he⟩
  obtain ⟨events, hEvent⟩ := chooseLaneWords (b32 0, false) hh
  obtain ⟨hk, hNext⟩ :=
    hOrd.shuffle (fun _ => pc) .idx words (fun lane => (events lane).1) (fun _ => idx)
      (fun _ => 31) (fun lane => (events lane).2) hEvent
  refine ⟨?_, hNext⟩
  intro lane hl recv ok _
  have hg' : warpLane l g idx < l.threads := (Step.sameWarp_lane hBlock hg hi).1.1.2.1
  have hSrc := sourceThread (source := idx) hBlock hg hl
  refine ⟨shuffles, pos idx, idx, (events idx).1, (events idx).2, hk lane hl, ?_, ?_, ?_⟩
  · rw [hSrc]
    exact hEvent idx hi
  · rw [hSrc]
    exact hk idx hi
  · rw [hSrc]
    exact ShflK.not_exited hX hg' (hk idx hi)

private theorem warpTerminalBallot (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hBlock : l.block % 32 = 0) {g shuffles votes n : Nat} {pos lanePrefix tiles : Nat → Nat}
    (hg : g < l.threads) (hn : n < 32) (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hLanes : ∀ lane < 32, ∃ t,
      At t 3092 [(332, .pred (decide (lane < n))), (7233, b32 (lanePrefix lane)),
        (7232, b32 (tiles lane)), (1062, b32 13)] ∧
      Run kernel Assumptions.all l (warpLane l g lane) t
        ((X.tr (warpLane l g lane)).drop (pos lane)) none) :
    WarpOrdinals l X g (fun lane => pos lane + 1) shuffles (votes + 1) ∧
    ∀ lane < 32,
      X.get (warpLane l g lane, pos lane) = some
        ⟨3092, .vote (2 ^ 32 - 1) (decide (lane < n)) (BitVec.ofNat 32 (2 ^ n - 1))⟩ ∧
      ∃ v, At v 3095 [(1214, b32 n), (333, .pred (decide (n = 0))),
          (7233, b32 (lanePrefix lane)), (7232, b32 (tiles lane)), (1062, b32 13)] ∧
        Run kernel Assumptions.all l (warpLane l g lane) v
          ((X.tr (warpLane l g lane)).drop (pos lane + 1)) none := by
  have hWords (lane : Nat) (hl : lane < 32) : ∃ word, X.get (warpLane l g lane, pos lane) =
      some ⟨3092, .vote (2 ^ 32 - 1) (decide (lane < n)) word⟩ := by
    obtain ⟨t, ht, hr⟩ := hLanes lane hl
    exact ballotOperand hp ht hr
  obtain ⟨word, hEvent⟩ := chooseLaneWords 0 hWords
  obtain ⟨hK, _, hOrd'⟩ := hOrd.ballot (fun _ => 3092) (fun lane => decide (lane < n)) word hEvent
  refine ⟨hOrd', ?_⟩
  intro lane hl
  obtain ⟨t, ht, hr⟩ := hLanes lane hl
  obtain ⟨v, val, he, hEq, hv, hRun⟩ := drainBallotTrace hp hX hn ht hr
    (fun _ _ => hK lane hl) (by
      intro peer hpeer
      rw [sourceThread (source := peer) hBlock hg hl]
      exact ⟨pos peer, word peer, hEvent peer hpeer, hK peer hpeer⟩)
  rw [hEq] at he
  exact ⟨he, v, hv, hRun⟩

private theorem dropOfHead {X : Execution} {g i : Nat} {e : Event}
    (h : X.get (g, i) = some e) : (X.tr g).drop i = e :: (X.tr g).drop (i + 1) := by
  cases hs : (X.tr g).drop i with
  | nil =>
    change (X.tr g)[i]? = some e at h
    rw [show (X.tr g)[i]? = ((X.tr g).drop i)[0]? by simp, hs] at h
    cases h
  | cons e' es =>
    obtain ⟨he, hRest⟩ := traceHeadOfDrop hs
    rw [h] at he
    obtain rfl := Option.some.inj he
    rw [hRest]

private theorem warpIndexedExit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hBlock : l.block % 32 = 0) {g shuffles votes n : Nat} {pos lanePrefix tiles : Nat → Nat}
    (hg : g < l.threads) (hn : n < 32) (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hLanes : ∀ lane < 32, ∃ t,
      At t 3095 [(1214, b32 n), (333, .pred (decide (n = 0))),
        (7233, b32 (lanePrefix lane)), (7232, b32 (tiles lane)), (1062, b32 13)] ∧
      Run kernel Assumptions.all l (warpLane l g lane) t
        ((X.tr (warpLane l g lane)).drop (pos lane)) none) :
    ∀ lane < 32, (X.tr (warpLane l g lane)).drop (pos lane) =
      (if n = 0 then [] else
        [⟨3097, .shfl .idx (b32 (lanePrefix lane)) (n - 1) 31 (b32 (lanePrefix (n - 1))) true⟩]) ++
        [⟨3098, .shfl .idx (b32 (tiles lane)) n 31 (b32 (tiles n)) true⟩, ⟨9205, .exit⟩] := by
  have hShape (lane : Nat) (hl : lane < 32) :=
    let ⟨t, ht, hr⟩ := hLanes lane hl
    tailIndexOperands hp hn ht hr
  have hPrev (hNZ : 0 < n) : ∀ lane < 32, ∃ recv ok,
      X.get (warpLane l g lane, pos lane) =
        some ⟨3097, .shfl .idx (b32 (lanePrefix lane)) (n - 1) 31 recv ok⟩ :=
    fun lane hl => (hShape lane hl).1 hNZ
  have hChosen : ∀ lane < 32, ∃ recv ok,
      X.get (warpLane l g lane, if n = 0 then pos lane else pos lane + 1) =
        some ⟨3098, .shfl .idx (b32 (tiles lane)) n 31 recv ok⟩ :=
    fun lane hl => (hShape lane hl).2
  have hPeers :
      (∀ lane < 32, 0 < n → DrainShufflePeer l X (warpLane l g lane) (pos lane)
        3097 (b32 (lanePrefix lane)) (n - 1) (b32 (lanePrefix (n - 1)))) ∧
      (∀ lane < 32, DrainShufflePeer l X (warpLane l g lane)
        (if n = 0 then pos lane else pos lane + 1)
        3098 (b32 (tiles lane)) n (b32 (tiles n))) := by
    by_cases hZero : n = 0
    · refine ⟨fun _ _ h => by omega, ?_⟩
      have hChosen' : ∀ lane < 32, ∃ recv ok, X.get (warpLane l g lane, pos lane) =
          some ⟨3098, .shfl .idx (b32 (tiles lane)) n 31 recv ok⟩ := by
        simpa only [hZero, ite_true] using hChosen
      simpa only [hZero, ite_true] using
        (alignIndexed hX hBlock hg hn (words := fun lane => b32 (tiles lane)) hOrd hChosen').1
    · obtain ⟨hP, hOrd'⟩ := alignIndexed hX hBlock hg (show n - 1 < 32 by omega)
        (words := fun lane => b32 (lanePrefix lane)) hOrd (hPrev (by omega))
      refine ⟨fun lane hl _ => hP lane hl, ?_⟩
      have hChosen' : ∀ lane < 32, ∃ recv ok, X.get (warpLane l g lane, pos lane + 1) =
          some ⟨3098, .shfl .idx (b32 (tiles lane)) n 31 recv ok⟩ := by
        simpa only [hZero, ite_false] using hChosen
      simpa only [hZero, ite_false] using
        (alignIndexed hX hBlock hg hn (words := fun lane => b32 (tiles lane)) hOrd' hChosen').1
  intro lane hl
  obtain ⟨t, ht, hr⟩ := hLanes lane hl
  exact drainIndexedExitTrace hp hX hn ht (hPeers.1 lane hl) (hPeers.2 lane hl) hr

/-- The events left in a lane after the terminal group selected lane `n`. -/
def drainTerminalEvents (n lane : Nat) (lanePrefix tiles : Nat → Nat) : List Event :=
  ⟨3092, .vote (2 ^ 32 - 1) (decide (lane < n)) (BitVec.ofNat 32 (2 ^ n - 1))⟩ ::
    ((if n = 0 then [] else
      [⟨3097, .shfl .idx (b32 (lanePrefix lane)) (n - 1) 31
        (b32 (lanePrefix (n - 1))) true⟩]) ++
      [⟨3098, .shfl .idx (b32 (tiles lane)) n 31 (b32 (tiles n)) true⟩, ⟨9205, .exit⟩])

/-- The terminal group test takes the same route in every lane. A nonempty group issues one
full-mask ballot, then one or two aligned indexed shuffles, before each lane exits. The only
lane-wise premises are its input state, terminal trace cursor and ballot arithmetic. -/
theorem drainWarpFinishObserved (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g shuffles votes first base count cta n : Nat} {pos lanePrefix tiles : Nat → Nat}
    (hg : g < l.threads) (hFirst : first ≤ p.batch) (hCount : count < 2 ^ 31) (hCTA : cta < 2 ^ 31)
    (hEnd : base + count * p.heads < 2 ^ 31) (hn : n < 32)
    (hOrd : WarpOrdinals l X g pos shuffles votes) (hBound : ∀ lane < 32, lanePrefix lane ≤ count)
    (hThreshold : first < p.batch → ∀ lane < 32, base + lanePrefix lane * p.heads ≤ cta ↔ lane < n)
    (hLanes : ∀ lane < 32, ∃ t,
      At t 3086 [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
        (7138, b32 p.heads), (7236, b32 (base + count * p.heads)), (7233, b32 (lanePrefix lane)),
        (1072, b32 cta), (7232, b32 (tiles lane)), (1062, b32 13)] ∧
      Run kernel Assumptions.all l (warpLane l g lane) t
        ((X.tr (warpLane l g lane)).drop (pos lane)) none) :
    (first = p.batch ∧ ∀ lane < 32,
      (X.tr (warpLane l g lane)).drop (pos lane) = [⟨9205, .exit⟩]) ∨
    (first < p.batch ∧ ∀ lane < 32,
      (X.tr (warpLane l g lane)).drop (pos lane) =
        drainTerminalEvents n lane lanePrefix tiles) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  by_cases hSkip : first = p.batch
  · refine .inl ⟨hSkip, ?_⟩
    intro lane hl
    obtain ⟨t, ht, hr⟩ := hLanes lane hl
    rcases drainGroupRoute hp hFirst (hBound lane hl) hCount hCTA hEnd ht hr with
      ⟨_, he⟩ | ⟨hLt, _⟩
    · exact he
    · omega
  have hLt : first < p.batch := by omega
  have hAtBallot (lane : Nat) (hl : lane < 32) : ∃ u,
      At u 3092 [(332, .pred (decide (lane < n))), (7233, b32 (lanePrefix lane)),
        (7232, b32 (tiles lane)), (1062, b32 13)] ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop (pos lane)) none := by
    obtain ⟨t, ht, hr⟩ := hLanes lane hl
    rcases drainGroupRoute hp hFirst (hBound lane hl) hCount hCTA hEnd ht hr with
      ⟨hEq, _⟩ | ⟨_, u, hu, hTail⟩
    · omega
    · exact ⟨u, by simpa only [hThreshold hLt lane hl] using hu, hTail⟩
  obtain ⟨hOrd', hBallot⟩ := warpTerminalBallot hp hX hBlock hg hn hOrd hAtBallot
  have hTail := warpIndexedExit hp hX hBlock hg hn hOrd'
    (fun lane hl => (hBallot lane hl).2)
  exact .inr ⟨hLt, fun lane hl =>
    (dropOfHead (hBallot lane hl).1).trans (congrArg (_ :: ·) (hTail lane hl))⟩


/-- The clipped group bypasses the scan and consumes only the exit event. Its previous
count and prefix registers need not contain contributions for the empty group. -/
theorem drainClippedGroupTrace {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {events : List Event}
    (ht : At t 3086 [(7235, b32 p.batch), (7147, b32 p.batch), (1062, b32 13)])
    (hRun : Run kernel Assumptions.all l g t events none) :
    events = [⟨9205, .exit⟩] := by
  have hPC := ht.1
  obtain ⟨u, hu, hf, hU, hFrame⟩ := drainGroupExit hp g t p.batch hPC ht.2.2.2.1
    (Nat.le_refl _) ht.2.2.2.2.1 ht.2.2.2.2.2.1
  obtain ⟨hu', _, _, _⟩ := epilogueLinearRun (F := [331]) (t := t) (n := 2)
    (by omega) (by omega) (by
      intro pc hlo hhi
      have hEq : pc = 3086 := by omega
      subst pc
      exact ⟨_, Flow.code_3086, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hPC]
      exact ⟨_, Flow.code_3087, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hu
  exact drainExitTrace (by simpa only [ite_true] using hU) hf
    ((hFrame 1062 (by decide)).trans ht.2.2.2.2.2.2.1) (hRun.after_local (run_rtg hu'))

/-- A terminal group uses its inclusive prefix counts to select the CTA's request.
The group bounds prove the ballot arithmetic, including repeated prefix values for empty
requests. A clipped group has only the exit suffix. -/
theorem drainWarpFinishGroup (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g shuffles votes first cta : Nat} {pos : Nat → Nat} (hg : g < l.threads) (hCTA : cta < l.grid)
    (hFirst : first ≤ p.batch) (hLow : tilePrefix p first * p.heads ≤ cta)
    (hHigh : first < p.batch → cta < tilePrefix p (min p.batch (first + 31)) * p.heads)
    (hOrd : WarpOrdinals l X g pos shuffles votes) :
    let tiles := groupLaneTiles p first
    let lanePrefix := fun lane => ∑ i ∈ Finset.range (lane + 1), tiles i
    let count := lanePrefix 31
    (∀ lane < 32, ∃ t,
      At t 3086 [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
        (7138, b32 p.heads), (7236, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
        (7233, b32 (lanePrefix lane)),
        (1072, b32 cta), (7232, b32 (tiles lane)), (1062, b32 13)] ∧
      Run kernel Assumptions.all l (warpLane l g lane) t
        ((X.tr (warpLane l g lane)).drop (pos lane)) none) →
    (first = p.batch ∧ ∀ lane < 32,
      (X.tr (warpLane l g lane)).drop (pos lane) = [⟨9205, .exit⟩]) ∨
    (∃ selected, first ≤ selected ∧ selected < first + 31 ∧ selected < p.batch ∧
      tilePrefix p selected * p.heads ≤ cta ∧ cta < tilePrefix p (selected + 1) * p.heads ∧
      ∀ lane < 32, (X.tr (warpLane l g lane)).drop (pos lane) =
        drainTerminalEvents (selected - first) lane lanePrefix tiles) := by
  dsimp only
  intro hLanes
  let tiles := groupLaneTiles p first
  let lanePrefix := fun lane => ∑ i ∈ Finset.range (lane + 1), tiles i
  let count := lanePrefix 31
  let base := tilePrefix p first * p.heads
  have hBound (lane : Nat) (hl : lane < 32) : lanePrefix lane ≤ count := by
    have h := prefixWindow_le_warp tiles 32 hl
    simpa only [prefixWindow_warp _ hl] using h
  have hCount : count < 2 ^ 31 := by
    have hl : (31 : Nat) < 32 := by decide
    simpa only [prefixWindow_warp _ hl] using hp.groupWindow_signed hFirst hl 32
  have hEndEq : base + count * p.heads = tilePrefix p (min p.batch (first + 31)) * p.heads := by
    have hSum := groupTiles_eq p hFirst (show (32 : Nat) ≤ 32 by decide)
    change tilePrefix p first + count = tilePrefix p (min p.batch (first + 31)) at hSum
    change tilePrefix p first * p.heads + count * p.heads =
      tilePrefix p (min p.batch (first + 31)) * p.heads
    rw [← Nat.add_mul, hSum]
  have hEnd : base + count * p.heads < 2 ^ 31 := by
    rw [hEndEq]
    exact hp.prefixWork_signed (Nat.min_le_left _ _)
  have hReady (lane : Nat) (hl : lane < 32) : ∃ t,
      At t 3086 [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
        (7138, b32 p.heads), (7236, b32 (base + count * p.heads)), (7233, b32 (lanePrefix lane)),
        (1072, b32 cta), (7232, b32 (tiles lane)), (1062, b32 13)] ∧
      Run kernel Assumptions.all l (warpLane l g lane) t
        ((X.tr (warpLane l g lane)).drop (pos lane)) none := by
    obtain ⟨t, ht, hr⟩ := hLanes lane hl
    exact ⟨t, by simpa only [hEndEq] using ht, hr⟩
  have hC := lt_trans hCTA hp.grid.2.2
  by_cases hClip : first = p.batch
  · rcases drainWarpFinishObserved hp hX hg hFirst hCount hC hEnd (n := 0)
      (by decide) hOrd hBound (fun h => by omega) hReady with h | ⟨h, _⟩
    · exact .inl h
    · omega
  have hFirst' : first < p.batch := by omega
  obtain ⟨selected, ⟨hS, hGroup, hBatch, hStart, hStop⟩, _⟩ :=
    groupContains_request p hLow (hHigh hFirst')
  have hn : selected - first < 32 := by omega
  have hThreshold (lane : Nat) (hl : lane < 32) :
      base + lanePrefix lane * p.heads ≤ cta ↔ lane < selected - first := by
    change tilePrefix p first * p.heads + lanePrefix lane * p.heads ≤ cta ↔ _
    rw [← Nat.add_mul, groupBallot_iff p hS hGroup hBatch hl hStart hStop]
    omega
  rcases drainWarpFinishObserved hp hX hg hFirst hCount hC hEnd hn hOrd hBound
    (fun _ => hThreshold) hReady with h | ⟨_, hTrace⟩
  · exact .inl h
  · exact .inr ⟨selected, hS, hGroup, hBatch, hStart, hStop, hTrace⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

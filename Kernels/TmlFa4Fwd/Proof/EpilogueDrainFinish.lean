-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueExitLoop
public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.EpilogueLocalRun
public import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem tailOut {l : Launch} {g : Nat} {t : TState} {e : Tmpl}
    (hlo : 3082 ≤ t.pc) (hhi : t.pc ≤ 3099) (h : out kernel [] l g t = .ev e) :
    out kernel Assumptions.all l g t = .ev e :=
  (epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)).trans h

theorem tailExitNext (l : Launch) (g : Nat) (t : TState)
    (hp : t.pc = 3099) (hf : t.fault = none) (hw : t.regs 1062 = some (b32 13)) :
    ∃ u, u.pc = 9205 ∧ Next kernel Assumptions.all l g t u .exit := by
  have hModel {s : TState} (hs : s.pc ∈ [3099, 3100, 7742, 7743, 7744, 9205]) :
      out kernel Assumptions.all l g s = out kernel [] l g s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    apply epilogue_out_all_eq_nil
    unfold EpiloguePc
    omega
  obtain ⟨u, hu, hpc, hout⟩ := finishSchedulerWith l g t hModel hp hf hw
  exact ⟨u, hpc, run_rtg hu, hout⟩

private theorem exitSuffix {l : Launch} {g : Nat} {t u : TState} {events : List Event}
    (hp : u.pc = 9205) (hn : Next kernel Assumptions.all l g t u .exit)
    {o : Option TState} (hr : Run kernel Assumptions.all l g t events o) (hMore : events ≠ []) :
    events = [⟨9205, .exit⟩] := by
  have hs : Stops kernel Assumptions.all l g u := ⟨_, hn.stop⟩
  cases hr with
  | nil => exact (hMore rfl).elim
  | step hlocal he _ =>
    have hEq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst u
    obtain ⟨a, ha, hFire⟩ := he
    rw [hn.stop] at ha
    obtain rfl := Out.ev.inj ha
    cases hFire.2
  | last hlocal he =>
    have hEq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst u
    obtain ⟨a, ha, hFire⟩ := he
    rw [hn.stop] at ha
    obtain rfl := Out.ev.inj ha
    rw [hFire.1, hp]

/-- After the exit branch is selected, its accepted terminal suffix is the common exit. -/
theorem drainExitTrace {l : Launch} {g : Nat} {t : TState} {events : List Event}
    (hp : t.pc = 3099) (hf : t.fault = none) (hw : t.regs 1062 = some (b32 13))
    (hr : Run kernel Assumptions.all l g t events none) :
    events = [⟨9205, .exit⟩] := by
  obtain ⟨u, hu, hn⟩ := tailExitNext l g t hp hf hw
  exact exitSuffix hu hn hr (fun h => by rw [h] at hr; cases hr)

/-- The exhausted egress branch can only record its terminal exit in a nonempty prefix. -/
theorem drainExitTraceOfNonempty {l : Launch} {g : Nat} {t : TState} {events : List Event}
    {o : Option TState} (hp : t.pc = 3099) (hf : t.fault = none)
    (hw : t.regs 1062 = some (b32 13)) (hr : Run kernel Assumptions.all l g t events o)
    (hMore : events ≠ []) : events = [⟨9205, .exit⟩] := by
  obtain ⟨u, hu, hn⟩ := tailExitNext l g t hp hf hw
  exact exitSuffix hu hn hr hMore

/-- The group exhaustion test runs in the complete model and either exits with no more
collectives, or exposes the first terminal ballot and retains both indexed-shuffle sources. -/
theorem drainGroupRoute {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first base count lanePrefix laneTiles cta : Nat} {t : TState}
    {events : List Event}
    (hFirst : first ≤ p.batch) (hPrefix : lanePrefix ≤ count) (hCount : count < 2 ^ 31)
    (hCTA : cta < 2 ^ 31) (hEnd : base + count * p.heads < 2 ^ 31)
    (ht : At t 3086 [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
       (7138, b32 p.heads), (7236, b32 (base + count * p.heads)), (7233, b32 lanePrefix),
       (1072, b32 cta), (7232, b32 laneTiles), (1062, b32 13)])
    (hr : Run kernel Assumptions.all l g t events none) :
    (first = p.batch ∧ events = [⟨9205, .exit⟩]) ∨
      (first < p.batch ∧ ∃ u,
        At u 3092 [(332, .pred (decide (base + lanePrefix * p.heads ≤ cta))),
          (7233, b32 lanePrefix), (7232, b32 laneTiles), (1062, b32 13)] ∧
        Run kernel Assumptions.all l g u events none) := by
  have get (r : Nat) (v : Value)
      (h : (r, v) ∈ [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
        (7138, b32 p.heads), (7236, b32 (base + count * p.heads)), (7233, b32 lanePrefix),
        (1072, b32 cta), (7232, b32 laneTiles), (1062, b32 13)]) : t.regs r = some v :=
    holds_mem ht.2.2.2.2 h
  obtain ⟨v, hRun, hFault, hPC, hFrame⟩ := drainGroupExit hp g t first ht.1 ht.2.2.2.1
    hFirst (get 7235 (b32 first) (by simp)) (get 7147 (b32 p.batch) (by simp))
  have hpc := ht.1
  obtain ⟨hRun', _, hSub, hAcc⟩ := epilogueLinearRun (F := [331]) (t := t) (n := 2)
    (by omega) (by omega) (by
      intro pc hlo hhi
      have heq : pc = 3086 := by omega
      subst pc
      exact ⟨_, Flow.code_3086, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hpc]
      exact ⟨_, Flow.code_3087, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hRun
  have hTail := hr.after_local (run_rtg hRun')
  have hWarp := (hFrame 1062 (by decide)).trans (get 1062 (b32 13) (by simp))
  by_cases hSkip : first = p.batch
  · exact .inl ⟨hSkip, drainExitTrace (by simpa [hSkip] using hPC) hFault hWarp hTail⟩
  · have hpv : v.pc = 3088 := by simpa [hSkip] using hPC
    have keep (r : Nat) (val : Value) (hne : r ≠ 331)
        (h : t.regs r = some val) : v.regs r = some val := (hFrame r hne).trans h
    have hAt : At v 3088
        [(7234, b32 count), (7138, b32 p.heads), (7236, b32 (base + count * p.heads)),
         (7233, b32 lanePrefix), (1072, b32 cta)] :=
      ⟨hpv, hSub, hAcc, hFault, keep 7234 _ (by decide) (get 7234 (b32 count) (by simp)),
        keep 7138 _ (by decide) (get 7138 (b32 p.heads) (by simp)),
        keep 7236 _ (by decide) (get 7236 (b32 (base + count * p.heads)) (by simp)),
        keep 7233 _ (by decide) (get 7233 (b32 lanePrefix) (by simp)),
        keep 1072 _ (by decide) (get 1072 (b32 cta) (by simp)), trivial⟩
    obtain ⟨u, hu, huAt⟩ := drainBallotArgs l g hPrefix hCount hp.heads_signed hCTA hEnd v hAt
    obtain ⟨hu', huFrame, _, _⟩ := epilogueLinearRun (F := [2443, 2444, 2445, 332])
      (t := v) (u := u) (n := 4) (by omega) (by omega) (by
        intro pc hlo hhi
        have hrs : pc = 3088 ∨ pc = 3089 ∨ pc = 3090 := by omega
        rcases hrs with rfl | rfl | rfl
        · exact ⟨_, Flow.code_3088, rfl, fun _ h => h, by simp [writesRegs]⟩
        · exact ⟨_, Flow.code_3089, rfl, fun _ h => h, by simp [writesRegs]⟩
        · exact ⟨_, Flow.code_3090, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
        intro _
        rw [show v.pc + 4 - 1 = 3091 by omega]
        exact ⟨_, Flow.code_3091, by simp [writesRegs]⟩) hSub hAcc hu
    exact .inr ⟨by omega, u, ⟨huAt.1, huAt.2.1, huAt.2.2.1, huAt.2.2.2.1,
      huAt.2.2.2.2.1,
      (huFrame 7233 (by decide)).trans
        (keep 7233 _ (by decide) (get 7233 (b32 lanePrefix) (by simp))),
      (huFrame 7232 (by decide)).trans
        (keep 7232 _ (by decide) (get 7232 (b32 laneTiles) (by simp))),
      (huFrame 1062 (by decide)).trans hWarp, trivial⟩, hTail.after_local (run_rtg hu')⟩
/-- The nonempty selected drain group reaches its terminal ballot by local steps. -/
theorem drainGroupToBallot {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first base count lanePrefix laneTiles cta : Nat} {t : TState}
    (hFirst : first < p.batch) (hPrefix : lanePrefix ≤ count) (hCount : count < 2 ^ 31)
    (hCTA : cta < 2 ^ 31) (hEnd : base + count * p.heads < 2 ^ 31)
    (ht : At t 3086 [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
       (7138, b32 p.heads), (7236, b32 (base + count * p.heads)), (7233, b32 lanePrefix),
       (1072, b32 cta), (7232, b32 laneTiles), (1062, b32 13)]) :
    ∃ u, At u 3092 [(332,.pred (decide (base + lanePrefix * p.heads ≤ cta))),
      (7233,b32 lanePrefix),(7232,b32 laneTiles),(1062,b32 13)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have get (r : Nat) (v : Value)
      (h : (r, v) ∈ [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
        (7138, b32 p.heads), (7236, b32 (base + count * p.heads)), (7233, b32 lanePrefix),
        (1072, b32 cta), (7232, b32 laneTiles), (1062, b32 13)]) : t.regs r = some v :=
    holds_mem ht.2.2.2.2 h
  obtain ⟨v, hRun, hFault, hPC, hFrame⟩ := drainGroupExit hp g t first ht.1 ht.2.2.2.1
    hFirst.le (get 7235 (b32 first) (by simp)) (get 7147 (b32 p.batch) (by simp))
  have hpc := ht.1
  obtain ⟨hRun', _, hSub, hAcc⟩ := epilogueLinearRun (F := [331]) (t := t) (n := 2)
    (by omega) (by omega) (by
      intro pc hlo hhi
      have heq : pc = 3086 := by omega
      subst pc
      exact ⟨_, Flow.code_3086, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hpc]
      exact ⟨_, Flow.code_3087, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hRun
  have hSkip : first ≠ p.batch := Nat.ne_of_lt hFirst
  have hWarp := (hFrame 1062 (by decide)).trans (get 1062 (b32 13) (by simp))
  have hpv : v.pc = 3088 := by simpa [hSkip] using hPC
  have keep (r : Nat) (val : Value) (hne : r ≠ 331)
      (h : t.regs r = some val) : v.regs r = some val := (hFrame r hne).trans h
  have hAt : At v 3088
      [(7234, b32 count), (7138, b32 p.heads), (7236, b32 (base + count * p.heads)),
       (7233, b32 lanePrefix), (1072, b32 cta)] :=
    ⟨hpv, hSub, hAcc, hFault, keep 7234 _ (by decide) (get 7234 (b32 count) (by simp)),
      keep 7138 _ (by decide) (get 7138 (b32 p.heads) (by simp)),
      keep 7236 _ (by decide) (get 7236 (b32 (base + count * p.heads)) (by simp)),
      keep 7233 _ (by decide) (get 7233 (b32 lanePrefix) (by simp)),
      keep 1072 _ (by decide) (get 1072 (b32 cta) (by simp)), trivial⟩
  obtain ⟨u, hu, huAt⟩ := drainBallotArgs l g hPrefix hCount hp.heads_signed hCTA hEnd v hAt
  obtain ⟨hu', huFrame, _, _⟩ := epilogueLinearRun (F := [2443, 2444, 2445, 332])
    (t := v) (u := u) (n := 4) (by omega) (by omega) (by
      intro pc hlo hhi
      have hrs : pc = 3088 ∨ pc = 3089 ∨ pc = 3090 := by omega
      rcases hrs with rfl | rfl | rfl
      · exact ⟨_, Flow.code_3088, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3089, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3090, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [show v.pc + 4 - 1 = 3091 by omega]
      exact ⟨_, Flow.code_3091, by simp [writesRegs]⟩) hSub hAcc hu
  exact ⟨u, ⟨huAt.1, huAt.2.1, huAt.2.2.1, huAt.2.2.2.1,
    huAt.2.2.2.2.1,
    (huFrame 7233 (by decide)).trans
      (keep 7233 _ (by decide) (get 7233 (b32 lanePrefix) (by simp))),
    (huFrame 7232 (by decide)).trans
      (keep 7232 _ (by decide) (get 7232 (b32 laneTiles) (by simp))),
    (huFrame 1062 (by decide)).trans hWarp, trivial⟩, (run_rtg hRun').trans (run_rtg hu')⟩


private theorem drainBallotBits {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i ordinal n : Nat}
    {pred : Bool} {word : BitVec 32}
    (he : X.get (g, i) = some ⟨3092, .vote (2 ^ 32 - 1) pred word⟩)
    (hOrdinal : X.MaskK voteClass (g, i) (2 ^ 32 - 1) ordinal)
    (hPeers : ∀ lane < 32, ∃ j val,
      let id := (g - laneOf l g + lane, j)
      X.get id = some ⟨3092, .vote (2 ^ 32 - 1) (decide (lane < n)) val⟩ ∧
        X.MaskK voteClass id (2 ^ 32 - 1) ordinal) :
    ∀ lane < 32, word.getLsbD lane = decide (lane < n) := by
  let part := fun lane => some (decide (lane < n))
  have hInst : MaskInstance l voteClass X g (2 ^ 32 - 1) ordinal .ballot part := by
    intro lane hLane
    refine ⟨fun _ => .inl ?_, ?_⟩
    · obtain ⟨j, val, hv, hj⟩ := hPeers lane hLane
      exact ⟨j, 3092, .vote (2 ^ 32 - 1) (decide (lane < n)) val, _, hv, rfl, hj, rfl⟩
    · intro h
      rw [Nat.testBit_two_pow_sub_one] at h
      simp [hLane] at h
  intro lane hLane
  exact (hX.vote g i ordinal 3092 (2 ^ 32 - 1) pred word he hOrdinal
    part hInst lane hLane).1 _ rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- In a terminal run the ballot is followed by the popcount and its zero test. The
matching peer events determine the selected lane index. -/
theorem drainBallotTrace (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i ordinal n lanePrefix laneTiles : Nat} {t : TState} {pred : Bool} (hN : n < 32)
    (ht : At t 3092 [(332, .pred pred), (7233, b32 lanePrefix), (7232, b32 laneTiles),
      (1062, b32 13)]) (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none)
    (hOrdinal : ∀ word, X.get (g, i) = some ⟨3092, .vote (2 ^ 32 - 1) pred word⟩ →
      X.MaskK voteClass (g, i) (2 ^ 32 - 1) ordinal)
    (hPeers : ∀ lane < 32, ∃ j val,
      let id := (g - laneOf l g + lane, j)
      X.get id = some ⟨3092, .vote (2 ^ 32 - 1) (decide (lane < n)) val⟩ ∧
        X.MaskK voteClass id (2 ^ 32 - 1) ordinal) :
    ∃ v word, X.get (g, i) = some ⟨3092, .vote (2 ^ 32 - 1) pred word⟩ ∧
      word = BitVec.ofNat 32 (2 ^ n - 1) ∧
      At v 3095 [(1214, b32 n), (333, .pred (decide (n = 0))),
        (7233, b32 lanePrefix), (7232, b32 laneTiles), (1062, b32 13)] ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (i + 1)) none := by
  have hOut := drainBallotTemplate hp g t pred ht.1 ht.2.2.2.1 ht.2.2.2.2.1
  cases hSuffix : (X.tr g).drop i with
  | nil => rw [hSuffix] at hRun; cases hRun
  | cons e es =>
    rw [hSuffix] at hRun
    have hn : Next kernel Assumptions.all l g t t
        (.vote (2 ^ 32 - 1) pred (fun word => next (setReg t 2446 (b32 word.toNat)))) :=
      ⟨.refl, tailOut (by have := ht.1; omega) (by have := ht.1; omega) hOut⟩
    obtain ⟨u, ⟨word, hev, hState⟩, hTail⟩ := hn.continuing_event (by
      rintro ⟨_, _, hbad⟩; cases hbad) hRun
    obtain rfl := Option.some.inj hState
    have hObs := traceHeadOfDrop hSuffix
    rw [hev, ht.1] at hObs
    have hBits := drainBallotBits hX hObs.1 (hOrdinal word hObs.1) hPeers
    have hM : word = BitVec.ofNat 32 (2 ^ n - 1) := by
      apply BitVec.eq_of_getLsbD_eq
      intro lane hl
      rw [hBits lane hl, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
      simp [hl]
    have hPow : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hN
    have hWord : word.toNat = 2 ^ n - 1 := by
      rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hZero : word.toNat = 0 ↔ n = 0 := by
      rw [hWord]
      constructor
      · intro h
        by_contra hn
        have hp : 2 ^ 0 < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
        change 1 < 2 ^ n at hp
        omega
      · rintro rfl
        decide
    have hU : At (next (setReg t 2446 (b32 word.toNat))) 3093 [(2446, b32 word.toNat)] :=
      (ht.set (r := 2446) (v := b32 word.toNat) (by simp)).mono
        (by simp [next, setReg])
    obtain ⟨v, hV, hv⟩ := drainBallotCount l g word (by omega) hBits _ hU
    obtain ⟨hV', hFrame, _, _⟩ := epilogueLinearRun (F := [1214, 333]) (t := next (setReg t 2446 _))
      (n := 2) (by have := hU.1; omega) (by have := hU.1; omega) (by
        intro pc hlo hhi
        have hpc : pc = 3093 := by have := hU.1; omega
        subst pc
        exact ⟨_, Flow.code_3093, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
        intro _
        rw [hU.1]
        exact ⟨_, Flow.code_3094, by simp [writesRegs]⟩) hU.2.1 hU.2.2.1 hV
    refine ⟨v, word, hObs.1, hM, ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1,
      ?_, ?_, ?_, ?_, trivial⟩, ?_⟩
    · simpa only [hZero] using hv.2.2.2.2.2.1
    · rw [hFrame 7233 (by decide)]
      exact ht.2.2.2.2.2.1
    · rw [hFrame 7232 (by decide)]
      exact ht.2.2.2.2.2.2.1
    · rw [hFrame 1062 (by decide)]
      exact ht.2.2.2.2.2.2.2.1
    · rw [hObs.2]
      exact hTail.after_local (run_rtg hV')

/-- The actual terminal ballot supplies the request and takes two local steps. -/
theorem drainBallotLocal {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i ordinal n lanePrefix laneTiles : Nat} {t : TState} {pred : Bool}
    {word : BitVec 32} (hN : n < 32)
    (ht : At t 3092 [(332, .pred pred), (7233, b32 lanePrefix), (7232, b32 laneTiles),
      (1062, b32 13)])
    (he : X.get (g,i) = some ⟨3092,.vote (2 ^ 32 - 1) pred word⟩)
    (hOrdinal :
      X.MaskK voteClass (g, i) (2 ^ 32 - 1) ordinal)
    (hPeers : ∀ lane < 32, ∃ j val,
      let id := (g - laneOf l g + lane, j)
      X.get id = some ⟨3092, .vote (2 ^ 32 - 1) (decide (lane < n)) val⟩ ∧
        X.MaskK voteClass id (2 ^ 32 - 1) ordinal) :
    ∃ v, At v 3095 [(1214,b32 n),(333,.pred (decide (n = 0))),
        (7233,b32 lanePrefix),(7232,b32 laneTiles),(1062,b32 13)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g)
        (next (setReg t 2446 (b32 word.toNat))) v := by
  have hBits := drainBallotBits hX he hOrdinal hPeers
  have hM : word = BitVec.ofNat 32 (2 ^ n - 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro lane hl
    rw [hBits lane hl, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp [hl]
  have hPow : 2 ^ n < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hN
  have hWord : word.toNat = 2 ^ n - 1 := by
    rw [hM, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hZero : word.toNat = 0 ↔ n = 0 := by
    rw [hWord]
    constructor
    · intro h
      by_contra hn
      have hp : 2 ^ 0 < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
      change 1 < 2 ^ n at hp
      omega
    · rintro rfl
      decide
  have hU : At (next (setReg t 2446 (b32 word.toNat))) 3093 [(2446, b32 word.toNat)] :=
    (ht.set (r := 2446) (v := b32 word.toNat) (by simp)).mono
      (by simp [next, setReg])
  obtain ⟨v, hV, hv⟩ := drainBallotCount l g word (by omega) hBits _ hU
  obtain ⟨hV', hFrame, _, _⟩ := epilogueLinearRun (F := [1214, 333]) (t := next (setReg t 2446 _))
    (n := 2) (by have := hU.1; omega) (by have := hU.1; omega) (by
      intro pc hlo hhi
      have hpc : pc = 3093 := by have := hU.1; omega
      subst pc
      exact ⟨_, Flow.code_3093, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hU.1]
      exact ⟨_, Flow.code_3094, by simp [writesRegs]⟩) hU.2.1 hU.2.2.1 hV
  refine ⟨v, ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1,
    ?_, ?_, ?_, ?_, trivial⟩, run_rtg hV'⟩
  · simpa only [hZero] using hv.2.2.2.2.2.1
  · rw [hFrame 7233 (by decide)]
    exact ht.2.2.2.2.2.1
  · rw [hFrame 7232 (by decide)]
    exact ht.2.2.2.2.2.2.1
  · rw [hFrame 1062 (by decide)]
    exact ht.2.2.2.2.2.2.2.1

/-- A matching indexed shuffle supplies the expected word in the same warp instance.
The peer can use a different index operand. -/
def DrainShufflePeer (l : Launch) (X : Execution) (g i pc : Nat)
    (src : Value) (lane : Nat) (expected : Value) : Prop :=
  ∀ recv ok, X.get (g, i) = some ⟨pc, .shfl .idx src lane 31 recv ok⟩ →
    ∃ ordinal j index peerRecv peerOk,
      X.ShflK (g, i) ordinal ∧
      X.get (g - laneOf l g + lane, j) = some ⟨pc, .shfl .idx expected index 31 peerRecv peerOk⟩ ∧
      X.ShflK (g - laneOf l g + lane, j) ordinal ∧
      ¬ ShflExited X (g - laneOf l g + lane) ordinal

private theorem drainIdxTrace (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (previous : Bool) {g i value lane expected : Nat} {t : TState} (hLane : lane < 32)
    (hPC : t.pc = (if previous then 3097 else 3098)) (hf : t.fault = none)
    (hValue : t.regs (if previous then 7233 else 7232) = some (b32 value))
    (hIndex : t.regs (if previous then 2447 else 1214) = some (b32 lane))
    (hPeer : DrainShufflePeer l X g i (if previous then 3097 else 3098)
      (b32 value) lane (b32 expected))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    let event : Event :=
      ⟨if previous then 3097 else 3098, .shfl .idx (b32 value) lane 31 (b32 expected) true⟩
    (X.tr g).drop i = event :: (X.tr g).drop (i + 1) ∧
      Run kernel Assumptions.all l g
        (next (setReg t (if previous then 2448 else 2449) (b32 expected)))
        ((X.tr g).drop (i + 1)) none := by
  dsimp only
  have hout := drainTailShuffle hp previous g t value lane hLane hPC hf hValue hIndex
  have hlo : 3082 ≤ t.pc := by cases previous <;> simp [hPC]
  have hhi : t.pc ≤ 3099 := by cases previous <;> simp [hPC]
  have hn : Next kernel Assumptions.all l g t t (.shfl .idx (b32 value) lane 31
      (fun v _ => next (setReg t (if previous then 2448 else 2449) v))) :=
    ⟨.refl, tailOut hlo hhi hout⟩
  cases hSuffix : (X.tr g).drop i with
  | nil => rw [hSuffix] at hRun; cases hRun
  | cons e es =>
    rw [hSuffix] at hRun
    obtain ⟨u, ⟨recv, ok, hev, hState⟩, hr⟩ := hn.continuing_event (by
      rintro ⟨_, _, _, hbad⟩; cases hbad) hRun
    have hObs := traceHeadOfDrop hSuffix
    rw [hev, hPC] at hObs
    obtain ⟨ordinal, j, index, peerRecv, peerOk, hk, hPeer', hj, hLive⟩ := hPeer recv ok hObs.1
    obtain ⟨hRecv, hOk⟩ := selectedIndexValue hX hLane hObs.1 hk hPeer' hj hLive
    cases hRecv
    cases hOk
    obtain rfl := Option.some.inj hState
    rw [hObs.2]
    exact ⟨by rw [hev, hPC], hr⟩

private theorem drainSelectedAndExit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i laneTiles n selected : Nat} {t : TState} (hN : n < 32) (hPC : t.pc = 3098)
    (hf : t.fault = none) (hTile : t.regs 7232 = some (b32 laneTiles))
    (hLane : t.regs 1214 = some (b32 n)) (hWarp : t.regs 1062 = some (b32 13))
    (hPeer : DrainShufflePeer l X g i 3098 (b32 laneTiles) n (b32 selected))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    (X.tr g).drop i = [⟨3098, .shfl .idx (b32 laneTiles) n 31 (b32 selected) true⟩,
      ⟨9205, .exit⟩] := by
  obtain ⟨hSuffix, hExit⟩ := drainIdxTrace hp hX false hN hPC hf hTile hLane hPeer hRun
  have hu : (next (setReg t 2449 (b32 selected))).pc = 3099 := by
    change t.pc + 1 = 3099
    rw [hPC]
  have hEnd := drainExitTrace hu hf (by simpa [next, setReg] using hWarp) hExit
  rw [hSuffix, hEnd]
  rfl

/-- The actual tail takes the zero-mask bypass or performs the previous-lane shuffle.
Both paths then perform the selected-lane shuffle and reach the common exit. -/
theorem drainIndexedExitTrace (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i n lanePrefix laneTiles preceding selected : Nat} {t : TState} (hN : n < 32)
    (ht : At t 3095 [(1214, b32 n), (333, .pred (decide (n = 0))),
      (7233, b32 lanePrefix), (7232, b32 laneTiles), (1062, b32 13)])
    (hPrevious : 0 < n → DrainShufflePeer l X g i 3097 (b32 lanePrefix) (n - 1) (b32 preceding))
    (hSelected : DrainShufflePeer l X g (if n = 0 then i else i + 1) 3098
      (b32 laneTiles) n (b32 selected))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    (X.tr g).drop i =
      (if n = 0 then [] else
        [⟨3097, .shfl .idx (b32 lanePrefix) (n - 1) 31 (b32 preceding) true⟩]) ++
        [⟨3098, .shfl .idx (b32 laneTiles) n 31 (b32 selected) true⟩, ⟨9205, .exit⟩] := by
  have hPC := ht.1
  have hf := ht.2.2.2.1
  have hLane := ht.2.2.2.2.1
  have hPred := ht.2.2.2.2.2.1
  have hPrefix := ht.2.2.2.2.2.2.1
  have hTiles := ht.2.2.2.2.2.2.2.1
  have hWarp := ht.2.2.2.2.2.2.2.2.1
  have hBranch := epilogueLocalStep (by omega) (by omega) (drainBallotBranch l g t _ hPC hf hPred)
  by_cases hZero : n = 0
  · simp only [hZero, ite_true, List.nil_append] at hSelected ⊢
    have hStep : Tau kernel Assumptions.all l g t {t with pc := 3098} := by
      apply tauStep_iff.mp
      simpa only [hZero, decide_true, ite_true] using hBranch
    exact drainSelectedAndExit hp hX (t := {t with pc := 3098}) (by omega) rfl hf hTiles
      (hZero ▸ hLane) hWarp hSelected (hRun.after_local (.single hStep))
  · have hStep : Tau kernel Assumptions.all l g t (skip t) := by
      apply tauStep_iff.mp
      simpa only [hZero, decide_false, Bool.false_eq_true, ite_false] using hBranch
    have hpv : (skip t).pc = 3096 := by simp [skip, hPC]
    have hv : At (skip t) 3096 [(1214, b32 n)] := ⟨hpv, rfl, rfl, hf, hLane, trivial⟩
    obtain ⟨v, hvRun, hvAt⟩ := drainPreviousLane l g (by omega) hN _ hv
    obtain ⟨hvAll, hvFrame, _, _⟩ := epilogueLinearRun (F := [2447]) (t := skip t) (n := 1)
      (by omega) (by omega) (by omega) (by
        intro _
        rw [hpv]
        exact ⟨_, Flow.code_3096, by simp [writesRegs]⟩) hv.2.1 hv.2.2.1 hvRun
    obtain ⟨hSuffix, hTail⟩ := drainIdxTrace hp hX true
      (show n - 1 < 32 by omega) hvAt.1 hvAt.2.2.2.1
      ((hvFrame 7233 (by decide)).trans hPrefix) hvAt.2.2.2.2.1 (hPrevious (by omega))
      (hRun.after_local ((Relation.ReflTransGen.single hStep).trans (run_rtg hvAll)))
    have hu : (next (setReg v 2448 (b32 preceding))).pc = 3098 := by
      change v.pc + 1 = 3098
      rw [hvAt.1]
    have hSecond := drainSelectedAndExit hp hX hN hu hvAt.2.2.2.1
      (by simpa [next, setReg] using (hvFrame 7232 (by decide)).trans hTiles)
      (by simpa [next, setReg] using (hvFrame 1214 (by decide)).trans hLane)
      (by simpa [next, setReg] using (hvFrame 1062 (by decide)).trans hWarp)
      (by simpa only [hZero, ite_false] using hSelected) hTail
    rw [hSuffix, hSecond]
    simp only [hZero, ite_false, ite_true, List.singleton_append]

/-- The repeated group's end test advances to the next search round or to the final group
test, with the accepted suffix unchanged because all four instructions are local. -/
theorem drainLaterRouteLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first count cta : Nat} {t : TState} (hc : cta < l.grid)
    (hCount : tilePrefix p first + count = tilePrefix p (min p.batch (first + 31)))
    (ht : At t 3082 [(7230, b32 (tilePrefix p first * p.heads)), (7234, b32 count),
      (7138, b32 p.heads), (1072, b32 cta)]) :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    ∃ u, At u (if limit ≤ cta then 3032 else 3086) [(7230, b32 limit), (7236, b32 limit)] ∧
      (∀ r ∉ [7236, 330, 7230], u.regs r = t.regs r) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  dsimp only
  obtain ⟨u, hu, hAt⟩ := drainLaterGroupLimit hp g hc hCount t ht
  have hpc := ht.1
  obtain ⟨hu', hFrame, _, _⟩ := epilogueLinearRun (F := [7236, 330, 7230]) (t := t) (n := 4)
    (by omega) (by omega) (by
      intro pc hlo hhi
      have hCases : pc = 3082 ∨ pc = 3083 ∨ pc = 3084 := by omega
      rcases hCases with rfl | rfl | rfl
      · exact ⟨_, Flow.code_3082, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3083, rfl, fun _ h => h, by simp [writesRegs]⟩
      · exact ⟨_, Flow.code_3084, rfl, fun _ h => h, by simp [writesRegs]⟩) (by
      intro _
      rw [hpc]
      exact ⟨_, Flow.code_3085, by simp [writesRegs]⟩) ht.2.1 ht.2.2.1 hu
  exact ⟨u, hAt, hFrame, run_rtg hu'⟩

theorem drainLaterRoute {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first count cta : Nat} {t : TState} {events : List Event} (hc : cta < l.grid)
    (hCount : tilePrefix p first + count = tilePrefix p (min p.batch (first + 31)))
    (ht : At t 3082 [(7230, b32 (tilePrefix p first * p.heads)), (7234, b32 count),
      (7138, b32 p.heads), (1072, b32 cta)])
    (hRun : Run kernel Assumptions.all l g t events none) :
    let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
    ∃ u, At u (if limit ≤ cta then 3032 else 3086) [(7230, b32 limit), (7236, b32 limit)] ∧
      (∀ r ∉ [7236, 330, 7230], u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u events none := by
  obtain ⟨u,hu,hSaved,hLocal⟩ := drainLaterRouteLocal hp hc hCount ht
  exact ⟨u,hu,hSaved,hRun.after_local hLocal⟩

/-- Starting at the final group's exhaustion test, an accepted warp-13 terminal suffix either
exits directly or contains the ballot and the indexed shuffles before the common exit. -/
theorem drainFinishObserved (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i ordinal first base count lanePrefix laneTiles cta n preceding selected : Nat} {t : TState}
    (hFirst : first ≤ p.batch) (hPrefix : lanePrefix ≤ count) (hCount : count < 2 ^ 31)
    (hCTA : cta < 2 ^ 31) (hEnd : base + count * p.heads < 2 ^ 31) (hN : n < 32)
    (ht : At t 3086 [(7235, b32 first), (7147, b32 p.batch), (7234, b32 count),
       (7138, b32 p.heads), (7236, b32 (base + count * p.heads)), (7233, b32 lanePrefix),
       (1072, b32 cta), (7232, b32 laneTiles), (1062, b32 13)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) none)
    (hOrdinal : ∀ word, X.get (g, i) = some
      ⟨3092, .vote (2 ^ 32 - 1) (decide (base + lanePrefix * p.heads ≤ cta)) word⟩ →
      X.MaskK voteClass (g, i) (2 ^ 32 - 1) ordinal)
    (hPeers : first < p.batch → ∀ lane < 32, ∃ j val,
      let id := (g - laneOf l g + lane, j)
      X.get id = some ⟨3092, .vote (2 ^ 32 - 1) (decide (lane < n)) val⟩ ∧
        X.MaskK voteClass id (2 ^ 32 - 1) ordinal)
    (hPrevious : first < p.batch → 0 < n → DrainShufflePeer l X g (i + 1) 3097
      (b32 lanePrefix) (n - 1) (b32 preceding))
    (hSelected : first < p.batch → DrainShufflePeer l X g (if n = 0 then i + 1 else i + 1 + 1)
      3098 (b32 laneTiles) n (b32 selected)) :
    (first = p.batch ∧ (X.tr g).drop i = [⟨9205, .exit⟩]) ∨
      (first < p.batch ∧ (X.tr g).drop i =
        ⟨3092, .vote (2 ^ 32 - 1) (decide (base + lanePrefix * p.heads ≤ cta))
          (BitVec.ofNat 32 (2 ^ n - 1))⟩ ::
        ((if n = 0 then [] else
          [⟨3097, .shfl .idx (b32 lanePrefix) (n - 1) 31 (b32 preceding) true⟩]) ++
          [⟨3098, .shfl .idx (b32 laneTiles) n 31 (b32 selected) true⟩, ⟨9205, .exit⟩])) := by
  rcases drainGroupRoute hp hFirst hPrefix hCount hCTA hEnd ht hRun with
    ⟨he, hExit⟩ | ⟨hl, u, hu, hSuffix⟩
  · exact .inl ⟨he, hExit⟩
  obtain ⟨v, word, hVote, rfl, hv, hr⟩ := drainBallotTrace hp hX hN hu hSuffix hOrdinal (hPeers hl)
  have hFinal := drainIndexedExitTrace hp hX hN hv (hPrevious hl) (hSelected hl) hr
  cases hs : (X.tr g).drop i with
  | nil => rw [hs] at hSuffix; cases hSuffix
  | cons e es =>
    obtain ⟨he, hRest⟩ := traceHeadOfDrop hs
    rw [hVote] at he
    obtain rfl := Option.some.inj he
    rw [hRest] at hFinal
    exact .inr ⟨hl, congrArg (_ :: ·) hFinal⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

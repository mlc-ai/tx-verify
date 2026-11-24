-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopLocal
public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Kernels.TmlFa4Fwd.Proof.MmaScanBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

noncomputable section

/-- The acquire polls in the softmax roles, with their continuation predicates. -/
def scorePollSites : List (Nat × Nat) :=
  [(3420, 9750), (3425, 9751), (3498, 9752), (4874, 9753), (5109, 9754), (5181, 9755),
   (6558, 9820), (6676, 9821), (7463, 9886), (7738, 9887)]

private def scoreCheck (pc : Nat) : Option (Nat × Nat) :=
  scorePollSites.find? (fun x => x.1 + 1 == pc)

private def scoreRetry (pc : Nat) : Option (Nat × Nat) :=
  scorePollSites.find? (fun x => x.1 + 2 == pc)

private def pcFloor (pc : Nat) : Nat :=
  ((scoreCheck pc).map Prod.fst).getD (((scoreRetry pc).map Prod.fst).getD pc)

private def success (s : TState) (r : Nat) : Bool :=
  match s.regs r with
  | some (.pred ok) => ok
  | _ => false

private def scoreSub (s : TState) : Nat :=
  if (scoreCheck s.pc).isNone && (scoreRetry s.pc).isNone &&
      (scoreCheck (s.pc + 1)).isNone then s.sub else 0

private def pcScore (s : TState) : Nat :=
  5 * pcFloor s.pc + scoreSub s + (((scoreCheck s.pc).map (success s ∘ Prod.snd)).getD false).toNat

private theorem pcFloor_le (pc : Nat) : pcFloor pc ≤ pc := by
  cases hc : scoreCheck pc with
  | some a =>
    obtain ⟨base, r⟩ := a
    have h : base + 1 = pc := by simpa only [beq_iff_eq] using List.find?_some hc
    simp only [pcFloor, hc, Option.map_some, Option.getD_some]
    omega
  | none =>
    cases hr : scoreRetry pc with
    | none => simp [pcFloor, hc, hr]
    | some a =>
      obtain ⟨base, r⟩ := a
      have h : base + 2 = pc := by simpa only [beq_iff_eq] using List.find?_some hr
      simp only [pcFloor, hc, hr, Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some]
      omega

private theorem pcScore_lo (s : TState) : 5 * pcFloor s.pc ≤ pcScore s := by
  unfold pcScore
  omega

private theorem pcScore_hi (s : TState) (hs : s.sub ≤ 3) : pcScore s ≤ 5 * s.pc + 4 := by
  have hFloor := pcFloor_le s.pc
  have hFlag : (((scoreCheck s.pc).map (success s ∘ Prod.snd)).getD false).toNat ≤ 1 := by
    cases ((scoreCheck s.pc).map (success s ∘ Prod.snd)).getD false <;> decide
  have hSub : scoreSub s ≤ 3 := by unfold scoreSub; split <;> omega
  unfold pcScore
  omega

/-- Contiguous regions with only forward control and canonical poll retries. -/
inductive ScoreWindow
  | biasedBody
  | plainBody
  | selectPrelude
  | firstRound
  | firstRoundCounters
  | firstGeometryCounters
  | biasedPrelude
  | plainPrelude
  | drainPrelude
  | finalWait

def loopWindow : ScoreLoop → ScoreWindow
  | .biased => .biasedBody
  | .plain => .plainBody

structure WindowSite where
  head : Nat
  stop : Nat
  exits : List Nat
  keeps : List Nat

/-- Values read by later score visits and left untouched by either loop. -/
def loopResident : ScoreLoop → List Nat
  | .biased => [1062,2535,5127,1230,7132,1229,1359,1226,1225,1360,1361]
  | .plain => [1062,2535,5127,1230,7133,8692,1229,1359]

def windowSite : ScoreWindow → WindowSite
  | .biasedBody => ⟨5032, 6650, [], 7248 :: loopResident .biased⟩
  | .plainBody => ⟨6661, 7601, [], 7254 :: loopResident .plain⟩
  | .selectPrelude => ⟨3104, 3154, [], [1062, 1072, 7247]⟩
  | .firstRound => ⟨3212, 5008, [7733], [1062]⟩
  | .firstRoundCounters => ⟨3425, 5006, [], [1225, 1226, 1228, 1229]⟩
  | .firstGeometryCounters => ⟨3418, 3423, [], [1225, 1226, 1228]⟩
  | .biasedPrelude => ⟨5009, 5025, [6654], [1062, 1359]⟩
  | .plainPrelude => ⟨6654, 6657, [7605], [1062]⟩
  | .drainPrelude => ⟨7606, 7659, [], [1062, 7151]⟩
  | .finalWait => ⟨7720, 7742, [], [1062]⟩

def windowHead (loop : ScoreLoop) : Nat := (windowSite (loopWindow loop)).head
def windowEnd (loop : ScoreLoop) : Nat := (windowSite (loopWindow loop)).stop

private def coreWindowOp (site : WindowSite) (pc : Nat) (i : Instr) : Bool :=
  (site.head ≤ pcFloor pc) &&
    (0 :: site.keeps).all (fun r => !(scoreEventWrites i.op).contains r) &&
    match scoreCheck pc, scoreRetry pc with
    | some (b, d), _ =>
      i.guard == some (d, false) && nextPc i.op pc == b + 3 &&
        (match i.op with | .bra .. => true | _ => false) &&
        pcFloor (pc + 1) == b && pcFloor (b + 3) == b + 3 && b + 3 ≤ site.stop
    | none, some (b, _) =>
      i.guard.isNone && nextPc i.op pc == b &&
        (match i.op with | .bra .. => true | _ => false) &&
        pcFloor b == b && b ≤ pcFloor (pc + 1) && (scoreCheck b).isNone
    | none, none =>
      (site.head ≤ nextPc i.op pc &&
        (nextPc i.op pc ≤ site.stop || site.exits.contains (nextPc i.op pc))) &&
        match i.op with
        | .mbarWait dst .. => i.guard.isNone && scoreCheck (pc + 1) == some (pc, dst)
        | .brx .. => false
        | op => pc < pcFloor (pc + 1) && pc < pcFloor (nextPc op pc) &&
              (scoreCheck (pc + 1)).isNone && (op.isLocal || scoreEventOp op)

set_option maxRecDepth 100000 in
private theorem firstCountersCode :
    (((kernel.code.drop 3425).take (5006-3425)).zipIdx 3425).all
      (fun p => coreWindowOp (windowSite .firstRoundCounters) p.2 p.1) = true := by
  kernel_rfl

private theorem windowCode (win : ScoreWindow) {pc : Nat} {i : Instr}
    (hLo : (windowSite win).head ≤ pc) (hHi : pc < (windowSite win).stop)
    (hc : kernel.code[pc]? = some i) : coreWindowOp (windowSite win) pc i = true := by
  let lo := (windowSite win).head
  let hi := (windowSite win).stop
  have hAll : (((kernel.code.drop lo).take (hi - lo)).zipIdx lo).all
      (fun p => coreWindowOp (windowSite win) p.2 p.1) = true := by
    cases win
    case firstRoundCounters => exact firstCountersCode
    all_goals set_option maxRecDepth 100000 in kernel_rfl
  have hMem : (i, pc) ∈ ((kernel.code.drop lo).take (hi - lo)).zipIdx lo := by
    apply List.mem_of_getElem? (i := pc - lo)
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by
      exact Nat.sub_lt_sub_right hLo hHi), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
    rfl
  exact List.all_eq_true.mp hAll _ hMem

private theorem scoreWrites_contains {op : Op} {r : Nat}
    (h : r ∉ scoreEventWrites op) : r ∉ writesRegs op := by
  cases op <;> first | exact h | simp [writesRegs]

private def segmentOk (pc : Nat) : Bool :=
  match cuteExp2.matchAt kernel pc with
  | none => false
  | some m =>
    [ScoreWindow.biasedBody, .plainBody, .selectPrelude, .firstRound, .firstRoundCounters,
      .firstGeometryCounters, .biasedPrelude, .plainPrelude, .drainPrelude, .finalWait].all
      fun win =>
        let site := windowSite win
        !(decide (site.head ≤ pc) && decide (pc < site.stop)) ||
          (pc < pcFloor m.stop && m.stop ≤ site.stop &&
            site.keeps.all (fun r => !(scoreSegmentWrites m).contains r))

private theorem segmentFrameInWindow (win : ScoreWindow) {s u : TState} {m : SegMatch CuteSlot}
    (hlo : (windowSite win).head ≤ s.pc) (hhi : s.pc < (windowSite win).stop)
    (hSite : s.pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel s.pc = some m)
    (hu : Assumptions.execSwExp2 m s = .ok u) :
    s.pc < pcFloor u.pc ∧ u.pc ≤ (windowSite win).stop ∧ u.sub = 0 ∧
      u.fault = s.fault ∧ ∀ r ∈ (windowSite win).keeps, u.regs r = s.regs r := by
  have hAll : Assumptions.swExp2Sites.all segmentOk = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hOk := List.all_eq_true.mp hAll _ hSite
  unfold segmentOk at hOk
  rw [hm] at hOk
  have hWin := List.all_eq_true.mp hOk win (by cases win <;> simp)
  simp only [hlo, hhi, decide_true, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, decide_eq_true_eq] at hWin
  obtain ⟨hP, hS, hF, hR⟩ := scoreSegmentFrame hu
  exact ⟨hP.symm ▸ hWin.1.1, hP.symm ▸ hWin.1.2, hS, hF, fun r hr =>
    hR _ (by simpa using List.all_eq_true.mp hWin.2 r hr)⟩

theorem tauScoreSource {l : Launch} {g : Nat} {s u : TState}
    (ht : Tau kernel Assumptions.all l g s u) :
    ∃ i, kernel.code[s.pc]? = some i ∧ s.fault = none ∧
      (u = skip s ∧ guardHolds s i.guard = .ok false ∨
        guardHolds s i.guard = .ok true ∧ i.op.isLocal = true ∧
        execLocalA Assumptions.all l g s i.op = .ok u) := by
  unfold Tau out at ht
  cases hf : s.fault with
  | some f => simp [hf] at ht
  | none =>
    simp only [hf] at ht
    cases hc : kernel.code[s.pc]? with
    | none => simp only [hc, reduceCtorEq] at ht
    | some i =>
      simp only [hc] at ht
      refine ⟨i, rfl, rfl, ?_⟩
      cases hG : guardHolds s i.guard with
      | error f => simp only [hG, reduceCtorEq] at ht
      | ok guard =>
        cases guard
        · simp only [hG, Out.tau.injEq] at ht
          exact .inl ⟨ht.symm, rfl⟩
        · simp only [hG] at ht
          by_cases hLoc : i.op.isLocal = true
          · simp only [hLoc, ite_true] at ht
            cases hExec : execLocalA Assumptions.all l g s i.op with
            | error f => simp only [hExec, reduceCtorEq] at ht
            | ok v =>
              simp only [hExec, Out.tau.injEq] at ht
              subst v
              exact .inr ⟨rfl, hLoc, rfl⟩
          · simp only [hLoc, ite_false, reduceCtorEq] at ht

private theorem windowBounds_le (loop : ScoreLoop) :
    windowHead loop < windowEnd loop := by cases loop <;> decide

private theorem localBranchKept {l : Launch} {g target : Nat} {uni : Bool} {s u : TState}
    (hExec : execLocalA Assumptions.all l g s (.bra target uni) = .ok u)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) :
    u.pc = target ∧ u.sub = s.sub ∧ u.fault = s.fault ∧ u.regs = s.regs := by
  have hLocal := (scoreExecLocal hExec).resolve_right
    (fun ⟨_, hm, _, _⟩ => hOff hm)
  exact ⟨hLocal.pc.resolve_right id, hLocal.sub, hLocal.fault,
    funext fun r => hLocal.regs r (by simp [writesRegs])⟩

private theorem pollCheckOff {pc : Nat} {b d : Nat} (h : scoreCheck pc = some (b, d)) :
    pc ∉ Assumptions.swExp2Sites := by
  have hP : (b, d) ∈ scorePollSites := List.mem_of_find?_eq_some h
  have hc : b + 1 = pc := by simpa only [beq_iff_eq] using List.find?_some h
  subst pc
  simpa using List.all_eq_true.mp (show scorePollSites.all
    (fun x => !(Assumptions.swExp2Sites.contains (x.1 + 1))) = true by decide) _ hP

private theorem pollRetryOff {pc : Nat} {b d : Nat} (h : scoreRetry pc = some (b, d)) :
    pc ∉ Assumptions.swExp2Sites := by
  have hP : (b, d) ∈ scorePollSites := List.mem_of_find?_eq_some h
  have hc : b + 2 = pc := by simpa only [beq_iff_eq] using List.find?_some h
  subst pc
  simpa using List.all_eq_true.mp (show scorePollSites.all
    (fun x => !(Assumptions.swExp2Sites.contains (x.1 + 2))) = true by decide) _ hP

private theorem scoreForward {s u : TState} (hs : s.sub ≤ 3) (h : s.pc < pcFloor u.pc) :
    pcScore s + 1 ≤ pcScore u := by
  have hLo := pcScore_lo u
  have hHi := pcScore_hi s hs
  omega

private theorem windowTau (win : ScoreWindow) {l : Launch} {g : Nat} {s u : TState}
    (hLo : (windowSite win).head ≤ s.pc) (hHi : s.pc < (windowSite win).stop)
    (hs : s.sub ≤ 3)
    (ht : Tau kernel Assumptions.all l g s u) :
    (windowSite win).head ≤ u.pc ∧ (u.pc ≤ (windowSite win).stop ∨ u.pc ∈ (windowSite win).exits) ∧
      u.sub ≤ 3 ∧ u.fault = none ∧
      pcScore s ≤ pcScore u ∧
        (∀ r ∈ (windowSite win).keeps, u.regs r = s.regs r) := by
  obtain ⟨i, hc, hF, hTau⟩ := tauScoreSource ht
  have hCode := windowCode win hLo hHi hc
  simp only [coreWindowOp, Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hCode
  obtain ⟨⟨hFloor, hKeep⟩, hCode⟩ := hCode
  have hRegKeep r (hr : r ∈ (windowSite win).keeps) : r ∉ scoreEventWrites i.op := by
    simpa using List.all_eq_true.mp hKeep r (List.mem_cons_of_mem 0 hr)
  have forwards (hP : s.pc < pcFloor u.pc)
      (hEnd : u.pc ≤ (windowSite win).stop ∨ u.pc ∈ (windowSite win).exits)
      (hSub : u.sub ≤ 3) (hFault : u.fault = s.fault)
      (hReg : (∀ r ∈ (windowSite win).keeps, u.regs r = s.regs r)) :
      (windowSite win).head ≤ u.pc ∧
        (u.pc ≤ (windowSite win).stop ∨ u.pc ∈ (windowSite win).exits) ∧
        u.sub ≤ 3 ∧ u.fault = none ∧
        pcScore s ≤ pcScore u ∧
          (∀ r ∈ (windowSite win).keeps, u.regs r = s.regs r) :=
    ⟨hLo.trans (hP.le.trans (pcFloor_le _)), hEnd, hSub, hFault.trans hF,
      (Nat.le_succ _).trans (scoreForward hs hP), hReg⟩
  cases hC : scoreCheck s.pc with
  | some row =>
    obtain ⟨base, dst⟩ := row
    simp only [hC, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hCode
    obtain ⟨⟨⟨⟨⟨hG, hD⟩, hBra⟩, hNext⟩, hTarget⟩, hExit⟩ := hCode
    have hBase : base + 1 = s.pc := by simpa only [beq_iff_eq] using List.find?_some hC
    have hStart : pcScore s = 5 * base + (success s dst).toNat := by
      simp [pcScore, pcFloor, scoreSub, hC]
    rcases hTau with ⟨rfl, hg⟩ | ⟨hg, _, he⟩
    · have hp : success s dst = false := by
        rw [hG] at hg
        by_cases hReg : s.regs dst = some (.pred true)
        · simp [guardHolds, readReg, hReg, bind, Except.bind, pure, Except.pure] at hg
        · unfold success
          split <;> simp_all
      have hScore := pcScore_lo (skip s)
      change 5 * pcFloor (s.pc + 1) ≤ _ at hScore
      rw [hNext] at hScore
      exact ⟨by simp [skip]; omega,  .inl (by simp [skip]; omega), Nat.zero_le _, hF,
        by simpa only [hStart, hp, Bool.toNat_false, Nat.add_zero] using hScore, fun _ _ => rfl⟩
    · cases hop : i.op <;> simp only [hop, reduceCtorEq] at hBra
      rename_i target uni
      have hU := localBranchKept (hop ▸ he) (pollCheckOff hC)
      have hEq : u.pc = base + 3 := hU.1.trans (by simpa only [hop, nextPc] using hD)
      have hB := pcScore_lo u
      rw [hEq, hTarget] at hB
      have hFlag : (success s dst).toNat ≤ 1 := by cases success s dst <;> decide
      exact ⟨by omega,  .inl (hEq ▸ hExit), hU.2.1.symm ▸ hs, hU.2.2.1.trans hF,
        by rw [hStart]; omega, fun r _ => congrFun hU.2.2.2 r⟩
  | none =>
    cases hR : scoreRetry s.pc with
    | some row =>
      obtain ⟨base, dst⟩ := row
      simp only [hC, hR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hCode
      obtain ⟨⟨⟨⟨⟨hG, hD⟩, hBra⟩, hTarget⟩, hNext⟩, _⟩ := hCode
      have hBase : base + 2 = s.pc := by simpa only [beq_iff_eq] using List.find?_some hR
      have hStart : pcScore s = 5 * base := by
        simp [pcScore, pcFloor, scoreSub, hC, hR]
      rcases hTau with ⟨rfl, hg⟩ | ⟨hg, _, he⟩
      · have hScore := pcScore_lo (skip s)
        change 5 * pcFloor (s.pc + 1) ≤ _ at hScore
        exact ⟨by simp [skip]; omega,  .inl (by simp [skip]; omega), Nat.zero_le _, hF,
          by rw [hStart]; omega, fun _ _ => rfl⟩
      · cases hop : i.op <;> simp only [hop, reduceCtorEq] at hBra
        rename_i target uni
        have hU := localBranchKept (hop ▸ he) (pollRetryOff hR)
        have hEq : u.pc = base := hU.1.trans (by simpa only [hop, nextPc] using hD)
        have hB := pcScore_lo u
        rw [hEq, hTarget] at hB
        exact ⟨by rw [pcFloor, hC, hR] at hFloor; exact hEq ▸ hFloor,
           .inl (by omega), hU.2.1.symm ▸ hs, hU.2.2.1.trans hF, hStart.symm ▸ hB,
          fun r _ => congrFun hU.2.2.2 r⟩
    | none =>
      simp only [hC, hR, Bool.and_eq_true, decide_eq_true_eq] at hCode
      have hStep : s.pc + 1 ≤ (windowSite win).stop := by omega
      by_cases hWait : ∃ p b off par acq sc, i.op = .mbarWait p b off par acq sc
      · obtain ⟨p, b, off, par, acq, sc, hop⟩ := hWait
        simp only [hop, Bool.and_eq_true] at hCode
        have hG : i.guard = none := Option.isNone_iff_eq_none.mp hCode.2.1
        rcases hTau with ⟨rfl, hg⟩ | ⟨_, hl, _⟩
        · rw [hG] at hg
          cases hg
        · rw [hop] at hl
          cases hl
      · have hOrd : s.pc < pcFloor (s.pc + 1) ∧ s.pc < pcFloor (nextPc i.op s.pc) := by
          cases hop : i.op <;> simp only [hop, Bool.and_eq_true, decide_eq_true_eq] at hCode ⊢
          all_goals first
            | exact hCode.2.1.1
            | exact (hWait ⟨_, _, _, _, _, _, hop⟩).elim
            | simp at hCode
        rcases hTau with ⟨rfl, hg⟩ | ⟨_, _, he⟩
        · exact forwards hOrd.1 (.inl hStep) (Nat.zero_le _) rfl (fun _ _ => rfl)
        · rcases scoreExecLocal he with hLocal | ⟨m, hSite, hm, hu⟩
          · have hP : u.pc = nextPc i.op s.pc := by
              have hL := hLocal.pc
              cases hop : i.op <;> simp only [hop, BrxTarget, or_false] at hL ⊢
              all_goals try exact hL
              simp [hop] at hCode
            have hLand : nextPc i.op s.pc ≤ (windowSite win).stop ∨
                nextPc i.op s.pc ∈ (windowSite win).exits := by
              simpa only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem]
                using hCode.1.2
            exact forwards (hP.symm ▸ hOrd.2) (hP.symm ▸ hLand)
              (hLocal.sub.symm ▸ hs) hLocal.fault
              (fun r hr => hLocal.regs r (scoreWrites_contains (hRegKeep r hr)))
          · obtain ⟨hp, hb, hSub, hFault, hReg⟩ :=
              segmentFrameInWindow win hLo hHi hSite hm hu
            exact forwards hp (.inl hb) (hSub ▸ Nat.zero_le _) hFault hReg

/-- Partial scratch belongs to the current nonlocal instruction. A local instruction
or a state without decoded code must start with the scratch state clear. -/
def ScoreScratchState (s : TState) : Prop :=
  match kernel.code[s.pc]? with
  | some i => if i.op.isLocal then ScoreScratchClear s else ScoreScratchReady i.op s
  | none => ScoreScratchClear s

theorem scratchStateOfClear {s : TState} (hs : ScoreScratchClear s) : ScoreScratchState s := by
  rcases hs with ⟨hSub,hAcc⟩
  unfold ScoreScratchState
  split
  · rename_i ins _
    split
    · exact ⟨hSub,hAcc⟩
    · cases ins.op <;> first
      | exact ⟨hSub,hAcc⟩
      | exact .inr hAcc
      | exact ⟨.inr hSub,hAcc⟩
  · exact ⟨hSub,hAcc⟩

theorem scratchClearOfLocal {s : TState} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hl : ins.op.isLocal = true)
    (hs : ScoreScratchState s) : ScoreScratchClear s := by
  simpa only [ScoreScratchState, hc, hl, ite_true] using hs

private theorem segmentScratch {m : SegMatch CuteSlot} {s u : TState}
    (h : Assumptions.execSwExp2 m s = .ok u) : ScoreScratchClear u := by
  unfold Assumptions.execSwExp2 at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · contradiction
    obtain rfl := Except.ok.inj h
    exact ⟨rfl,rfl⟩
  · contradiction

/-- A local softmax transition consumes no pending load or store scratch. -/
theorem scoreScratchTau {l : Launch} {g : Nat} {s u : TState}
    (h : Tau kernel Assumptions.all l g s u) (hs : ScoreScratchState s) :
    ScoreScratchState u := by
  obtain ⟨ins,hc,_,hExec⟩ := tauScoreSource h
  apply scratchStateOfClear
  rcases hExec with ⟨rfl,_⟩ | ⟨_,hl,he⟩
  · exact ⟨rfl,rfl⟩
  · rcases scoreExecLocal he with hLocal | ⟨_,_,_,hSegment⟩
    · obtain ⟨hSub,hAcc⟩ := scratchClearOfLocal hc hl hs
      exact ⟨hLocal.sub.trans hSub,hLocal.acc.trans hAcc⟩
    · exact segmentScratch hSegment

private theorem windowEvent (win : ScoreWindow) {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (hLo : (windowSite win).head ≤ s.pc) (hHi : s.pc < (windowSite win).stop)
    (hs : s.sub ≤ 3)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    (windowSite win).head ≤ u.pc ∧ u.pc ≤ (windowSite win).stop ∧ u.sub ≤ 3 ∧
      (u.fault.isNone ∨ u.pc = s.pc) ∧
      (pcScore s + (if e.counts then 1 else 0) ≤ pcScore u ∨ u.fault.isSome) ∧
      (∀ r ∈ (windowSite win).keeps, u.regs r = s.regs r) ∧
      (ScoreScratchState s → ScoreScratchState u) := by
  obtain ⟨i, hc, hLocal, hf⟩ := estep_event_source he
  have hFault : s.fault = none := by
    cases h : s.fault
    · rfl
    · obtain ⟨m, hm, hf⟩ := he
      simp only [out, h, Out.ev.injEq] at hm
      subst m
      cases hf.2
  have hCode := windowCode win hLo hHi hc
  simp only [coreWindowOp, Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hCode
  obtain ⟨⟨hFloor, hKeep⟩, hCode⟩ := hCode
  have hRegKeep r (hr : r ∈ 0 :: (windowSite win).keeps) : r ∉ scoreEventWrites i.op := by
    simpa using List.all_eq_true.mp hKeep r hr
  have hScratch (hOp : scoreEventOp i.op = true) (hS : ScoreScratchState s) :
      ScoreScratchState u := by
    have hReady : ScoreScratchReady i.op s := by
      simpa only [ScoreScratchState, hc, hLocal, Bool.false_eq_true, ite_false] using hS
    have hNext := scoreEventScratch hc hOp hs (hRegKeep 0 (by simp)) he hReady
    by_cases hEq : u.pc = s.pc
    · simpa only [hEq, ScoreScratchState, hc, hLocal, Bool.false_eq_true, ite_false, ite_true]
        using hNext
    · exact scratchStateOfClear (by simpa only [hEq, ite_false] using hNext)
  have hCheck : scoreCheck s.pc = none := by
    cases hh : scoreCheck s.pc with
    | none => rfl
    | some row =>
      obtain ⟨base, dst⟩ := row
      simp only [hh, Bool.and_eq_true] at hCode
      have hB := hCode.1.1.1.2
      cases hop : i.op <;> simp_all [Op.isLocal]
  have hRetry : scoreRetry s.pc = none := by
    cases hh : scoreRetry s.pc with
    | none => rfl
    | some row =>
      obtain ⟨base, dst⟩ := row
      simp only [hCheck, hh, Bool.and_eq_true] at hCode
      have hB := hCode.1.1.1.2
      cases hop : i.op <;> simp_all [Op.isLocal]
  simp only [hCheck, hRetry, Bool.and_eq_true, decide_eq_true_eq] at hCode
  by_cases hWait : ∃ p b off par acq sc, i.op = .mbarWait p b off par acq sc
  · obtain ⟨p, b, off, par, acq, sc, hop⟩ := hWait
    simp only [hop, Bool.and_eq_true, beq_iff_eq] at hCode
    have hClean := hScratch (by rw [hop]; rfl)
    rw [hop] at hf
    obtain ⟨loc, phase, ok, effective, rfl, rfl⟩ := fires_wait hf
    have hNext := hCode.2.2
    have hReg r (hr : r ∈ (windowSite win).keeps) : r ≠ p := by
      simpa [scoreEventWrites, Mma.mmaWrites, hop] using
        hRegKeep r (List.mem_cons_of_mem 0 hr)
    refine ⟨by change _ ≤ s.pc + 1; omega, by change s.pc + 1 ≤ _; omega, hs,
      .inl (by simp only [next, setReg, hFault, Option.isNone_none]), .inl ?_,
      (fun r hr => Function.update_of_ne (hReg r hr) _ _), hClean⟩
    cases ok <;>
      simp [pcScore, pcFloor, scoreSub, hCheck, hRetry, hNext, success, next, setReg, Event.counts]
  · have hOrd : (s.pc < pcFloor (s.pc + 1) ∧ (scoreCheck (s.pc + 1)).isNone = true) ∧
        scoreEventOp i.op = true := by
      cases hop : i.op <;> simp only [hop, Bool.and_eq_true, decide_eq_true_eq] at hCode ⊢
      all_goals
        first
        | (have hh := hCode.2.2
           rw [← hop, hLocal, Bool.false_or] at hh
           exact ⟨⟨hCode.2.1.1.1, hCode.2.1.2⟩, hop ▸ hh⟩)
        | exact (hWait ⟨_, _, _, _, _, _, hop⟩).elim
        | simp at hCode
    have hProgress := (scoreEventStep hc hOrd.2 hs (hRegKeep 0 (by simp)) he).1
    have hReg r (hr : r ∈ (windowSite win).keeps) := (scoreEventStep hc hOrd.2 hs
      (hRegKeep r (List.mem_cons_of_mem 0 hr)) he).2
    have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
    rcases hProgress.pc with ⟨hPc, hF⟩ | ⟨hPc, hSame | hF⟩
    · have hS := scoreForward hs (show s.pc < pcFloor u.pc by rw [hPc]; exact hOrd.1.1)
      exact ⟨by omega, by omega, hProgress.sub, .inl (by rw [hF, hFault]; rfl),
        .inl (by omega), hReg, hScratch hOrd.2⟩
    · have hNoNext : scoreCheck (s.pc + 1) = none := Option.isNone_iff_eq_none.mp hOrd.1.2
      have hR : pcScore s + 1 ≤ pcScore u := by
        simp [pcScore, scoreSub, hPc, hSame, hCheck, hRetry, hNoNext]
      exact ⟨by omega, by omega, hProgress.sub, .inr hPc, .inl (by omega), hReg, hScratch hOrd.2⟩
    · exact ⟨by omega, by omega, hProgress.sub, .inr hPc, .inr hF, hReg, hScratch hOrd.2⟩

/-- Returning instructions stay in the region or land at a decoded forward exit, and preserve
the named loop and scheduler registers. -/
theorem windowStepFrame (win : ScoreWindow) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : (windowSite win).head ≤ s.pc)
    (hHi : s.pc < (windowSite win).stop) (hSub : s.sub ≤ 3)
    (he : WStep kernel Assumptions.all l g s e u) :
    (windowSite win).head ≤ u.pc ∧
      (u.pc ≤ (windowSite win).stop ∨ u.pc ∈ (windowSite win).exits) ∧
      u.sub ≤ 3 ∧ (u.fault = none ∨ u.pc = s.pc) ∧
      ∀ r ∈ (windowSite win).keeps, u.regs r = s.regs r := by
  rcases he with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨hl, hh, hs, hf, _, hr⟩ := windowTau win hLo hHi hSub ht
    exact ⟨hl, hh, hs, .inl hf, hr⟩
  · obtain ⟨hl, hh, hs, hf, _, hr, _⟩ := windowEvent win hLo hHi hSub he
    exact ⟨hl, .inl hh, hs, hf.imp Option.isNone_iff_eq_none.mp id, hr⟩


/-- A returning step in an audited score window consumes scratch data at the instruction
boundary and can retain it only while the same instruction is still in flight. -/
theorem windowStepScratch (win : ScoreWindow) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : (windowSite win).head ≤ s.pc)
    (hHi : s.pc < (windowSite win).stop) (hSub : s.sub ≤ 3)
    (he : WStep kernel Assumptions.all l g s e u) (hS : ScoreScratchState s) :
    ScoreScratchState u := by
  rcases he with ⟨rfl,ht⟩ | ⟨_,rfl,he⟩
  · exact scoreScratchTau ht hS
  · exact (windowEvent win hLo hHi hSub he).2.2.2.2.2.2 hS


private def tailControl (loop : ScoreLoop) (pc : Nat) (i : Instr) : Bool :=
  i.op.isLocal && (loopResident loop).all (fun r => !(writesRegs i.op).contains r) &&
    !(Assumptions.swExp2Sites.contains pc) &&
    (match i.op with | .brx .. => false | _ => true) &&
    (nextPc i.op pc == pc + 1 || nextPc i.op pc == (scoreLoopSite loop).head)

private theorem tailLocalCode (loop : ScoreLoop) {s : TState} {i : Instr}
    (hLo : (scoreLoopSite loop).increment ≤ s.pc)
    (hHi : s.pc < (scoreLoopSite loop).increment + 4)
    (hc : kernel.code[s.pc]? = some i) : tailControl loop s.pc i = true := by
  let lo := (scoreLoopSite loop).increment
  have hAll : (((kernel.code.drop lo).take 4).zipIdx lo).all
      (fun p => tailControl loop p.2 p.1) = true := by
    cases loop <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, s.pc)
  apply List.mem_of_getElem? (i := s.pc - lo)
  have hL : lo ≤ s.pc := hLo
  have hH : s.pc < lo + 4 := hHi
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hL, hc]
  rfl

/-- A returning step in a repeated score loop preserves the warp number. It stays
inside the body and test or exits at the forward fallthrough. -/
theorem scoreLoopStepWithResidents (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : (scoreLoopSite loop).head ≤ s.pc)
    (hHi : s.pc < (scoreLoopSite loop).increment + 4)
    (hs : s.sub ≤ 3) (he : WStep kernel Assumptions.all l g s e u) :
    (scoreLoopSite loop).head ≤ u.pc ∧ u.pc ≤ (scoreLoopSite loop).increment + 4 ∧
      u.sub ≤ 3 ∧ (u.fault = none ∨ u.pc = s.pc) ∧ (∀ r ∈ loopResident loop, u.regs r = s.regs r)
        := by
  by_cases hb : s.pc < (scoreLoopSite loop).increment
  · have hHead : (windowSite (loopWindow loop)).head = (scoreLoopSite loop).head := by
      cases loop <;> rfl
    have hStop : (windowSite (loopWindow loop)).stop = (scoreLoopSite loop).increment := by
      cases loop <;> rfl
    have hExit : (windowSite (loopWindow loop)).exits = [] := by cases loop <;> rfl
    have hKeep (r : Nat) (hr : r ∈ loopResident loop) :
        r ∈ (windowSite (loopWindow loop)).keeps := by
      cases loop <;> exact List.mem_cons_of_mem _ hr
    obtain ⟨hl, hh, hu, hf, hr⟩ :=
      windowStepFrame (loopWindow loop) (hHead.symm ▸ hLo) (hStop.symm ▸ hb) hs he
    simp only [hExit, List.not_mem_nil, or_false, hStop] at hh
    exact ⟨hHead ▸ hl, by omega, hu, hf, fun r hr' => hr r (hKeep r hr')⟩
  · have hNext (hPc : u.pc = s.pc + 1 ∨ u.pc = (scoreLoopSite loop).head)
        (hSub : u.sub ≤ 3) (hf : u.fault = none)
        (hReg : ∀ r ∈ loopResident loop, u.regs r = s.regs r) :
        (scoreLoopSite loop).head ≤ u.pc ∧ u.pc ≤ (scoreLoopSite loop).increment + 4 ∧
          u.sub ≤ 3 ∧ (u.fault = none ∨ u.pc = s.pc) ∧ (∀ r ∈ loopResident loop, u.regs r =
            s.regs r) := by
      rcases hPc with hp | hp <;> exact ⟨by omega, by omega, hSub, .inl hf, hReg⟩
    rcases he with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
    · obtain ⟨i, hc, hf, hExec⟩ := tauScoreSource ht
      have hCode := tailLocalCode loop (by omega) hHi hc
      simp only [tailControl, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, Bool.or_eq_true, beq_iff_eq] at hCode
      rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hex⟩
      · exact hNext (.inl rfl) (Nat.zero_le _) hf (fun _ _ => rfl)
      · have hFrame := (scoreExecLocal hex).resolve_right
          (fun ⟨_, hm, _, _⟩ => hCode.1.1.2 hm)
        have hBranch : ¬ BrxTarget i.op u.pc := by
          cases hOp : i.op <;> simp only [BrxTarget, not_false_eq_true]
          simp [hOp] at hCode
        have hPc := hFrame.pc.resolve_right hBranch
        exact hNext (hPc ▸ hCode.2) (hFrame.sub.symm ▸ hs) (hFrame.fault.trans hf)
          (fun r hr => hFrame.regs r (by
            simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not]
              using List.all_eq_true.mp hCode.1.1.1.2 r hr))
    · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
      have hCode := tailLocalCode loop (by omega) hHi hc
      simp only [tailControl, hl, Bool.false_and, Bool.false_eq_true] at hCode
theorem scoreLoopStepFrame (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : (scoreLoopSite loop).head ≤ s.pc)
    (hHi : s.pc < (scoreLoopSite loop).increment + 4)
    (hs : s.sub ≤ 3) (he : WStep kernel Assumptions.all l g s e u) :
    (scoreLoopSite loop).head ≤ u.pc ∧ u.pc ≤ (scoreLoopSite loop).increment + 4 ∧
      u.sub ≤ 3 ∧ (u.fault = none ∨ u.pc = s.pc) ∧ u.regs 1062 = s.regs 1062 := by
  obtain ⟨hl,hh,hs,hf,hr⟩ := scoreLoopStepWithResidents loop hLo hHi hs he
  exact ⟨hl,hh,hs,hf,hr 1062 (by cases loop <;> decide)⟩

/-- Bound one actual score-window traversal, including a terminal fault,
without charging retries. -/
theorem windowPrefix {l : Launch} {g : Nat} (win : ScoreWindow) {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hlo : (windowSite win).head ≤ s.pc) (hs : s.sub ≤ 3) :
    Mma.countedUntil (windowSite win).stop vs ≤
      5 * ((windowSite win).stop - (windowSite win).head) + 2 := by
  suffices hMetric : Mma.countedUntil (windowSite win).stop vs ≤
      5 * (windowSite win).stop + 2 - pcScore s by
    by_cases hh : s.pc < (windowSite win).stop
    · cases hf : s.fault
      · have hFloor : (windowSite win).head ≤ pcFloor s.pc := by
          have hLen : s.pc < kernel.code.length := by
            have hBound : (windowSite win).stop ≤ kernel.code.length := by
              cases win <;> set_option maxRecDepth 100000 in decide +kernel
            exact hh.trans_le hBound
          have hc := windowCode win hlo hh (List.getElem?_eq_getElem (l := kernel.code) hLen)
          simp only [coreWindowOp, Bool.and_eq_true, decide_eq_true_eq] at hc
          exact hc.1.1
        have hLow := pcScore_lo s
        omega
      · exact (Mma.countFaultedScan (by simp [hf]) hw).trans (by omega)
    · cases hw <;> simp [Mma.countedUntil, hh, visit_pc]
  induction hw with
  | stop => simp [Mma.countedUntil]
  | @tau s u es vs ht hw ih =>
    by_cases hHi : s.pc < (windowSite win).stop
    · obtain ⟨hLo, _, hSub, _, hR, _⟩ := windowTau win hlo hHi hs ht
      have hMon := Nat.sub_le_sub_left hR (5 * (windowSite win).stop + 2)
      simpa [Mma.countedUntil, hHi, visit_pc, visit_ev, List.filterMap_cons] using
        (ih hLo hSub).trans hMon
    · simp [Mma.countedUntil, hHi, visit_pc]
  | @ev s u e es vs he hw ih =>
    by_cases hHi : s.pc < (windowSite win).stop
    · obtain ⟨hLo, hu, hSub, hF, hR | hFault, _⟩ := windowEvent win hlo hHi hs he
      · have hSrc := pcScore_hi s hs
        have hCount := ih hLo hSub
        have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
        simp only [Mma.countedUntil, List.takeWhile_cons, visit_pc, hHi, decide_true,
          ite_true, List.filterMap_cons, visit_ev, List.countP_cons]
        change Mma.countedUntil (windowSite win).stop vs + (if e.counts then 1 else 0) ≤ _
        omega
      · have hCount := Mma.countFaultedScan (stop := (windowSite win).stop) hFault hw
        have hSrc := pcScore_hi s hs
        have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
        simp only [Mma.countedUntil, List.takeWhile_cons, visit_pc, hHi, decide_true,
          ite_true, List.filterMap_cons, visit_ev, List.countP_cons]
        change Mma.scanBodyCount (windowSite win).stop vs + (if e.counts then 1 else 0) ≤ _
        omega
    · simp [Mma.countedUntil, hHi, visit_pc]
  | @last s e he =>
    by_cases hHi : s.pc < (windowSite win).stop
    · have hSrc := pcScore_hi s hs
      have hCharge : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
      simp only [Mma.countedUntil, List.takeWhile_cons, visit_pc, hHi, decide_true,
        ite_true, List.takeWhile_nil, List.filterMap_cons, visit_ev, List.countP_cons,
        List.filterMap_nil, List.countP_nil, Nat.zero_add]
      omega
    · simp [Mma.countedUntil, hHi, visit_pc]

/-- Either the walk ends in the score window or reaches the counter increment with the
original counter value and a continuation of the same walk. -/
theorem cutScoreWindow {l : Launch} {g cutoff : Nat} (loop : ScoreLoop) {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : s.pc = (scoreLoopSite loop).head) (hs : s.sub ≤ 3)
    (hCut : (scoreLoopSite loop).increment ≤ cutoff) :
    Mma.countedUntil cutoff vs ≤ 5 * (windowEnd loop - windowHead loop) + 2 ∨
      ∃ u rest tail, u.pc = (scoreLoopSite loop).increment ∧ u.fault = none ∧
        u.sub ≤ 3 ∧ u.regs (scoreLoopSite loop).word = s.regs (scoreLoopSite loop).word ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        Mma.countedUntil cutoff vs ≤ 5 * (windowEnd loop - windowHead loop) + 2 +
          Mma.countedUntil cutoff tail := by
  have hH : (scoreLoopSite loop).head = windowHead loop := by cases loop <;> rfl
  have hE : (scoreLoopSite loop).increment = windowEnd loop := by cases loop <;> rfl
  have hLo : windowHead loop ≤ s.pc := by rw [hp, hH]
  have hHi : s.pc < windowEnd loop := by rw [hp, hH]; exact windowBounds_le loop
  have hBound := windowPrefix (loopWindow loop) hw hLo hs
  have hK : (scoreLoopSite loop).word ∈ (windowSite (loopWindow loop)).keeps := by
    cases loop <;> decide
  have hX : (windowSite (loopWindow loop)).exits = [] := by cases loop <;> rfl
  have hStep {t u : TState} {e : Option Event} (hl : windowHead loop ≤ t.pc)
      (hh : t.pc < windowEnd loop) (he : WStep kernel Assumptions.all l g t e u)
      (ht : t.sub ≤ 3 ∧ t.regs (scoreLoopSite loop).word = s.regs (scoreLoopSite loop).word) :
      (windowHead loop ≤ u.pc ∧ u.pc < windowEnd loop ∨
        u.pc ∈ [windowEnd loop] ∧ u.fault = none) ∧
      u.sub ≤ 3 ∧ u.regs (scoreLoopSite loop).word = s.regs (scoreLoopSite loop).word := by
    have hFinish (hl : windowHead loop ≤ u.pc) (hh : u.pc ≤ windowEnd loop)
        (hSub : u.sub ≤ 3) (hF : u.pc = windowEnd loop → u.fault = none)
        (hReg : u.regs (scoreLoopSite loop).word = t.regs (scoreLoopSite loop).word) :
        (windowHead loop ≤ u.pc ∧ u.pc < windowEnd loop ∨
          u.pc ∈ [windowEnd loop] ∧ u.fault = none) ∧
        u.sub ≤ 3 ∧ u.regs (scoreLoopSite loop).word = s.regs (scoreLoopSite loop).word := by
      refine ⟨?_, hSub, hReg.trans ht.2⟩
      rcases hh.lt_or_eq with hh | hEq
      · exact .inl ⟨hl, hh⟩
      · exact .inr ⟨by simp [hEq], hF hEq⟩
    rcases he with ⟨rfl, hT⟩ | ⟨e, rfl, hE⟩
    · obtain ⟨hL, hH, hS, hF, _, hReg⟩ := windowTau (loopWindow loop) hl hh ht.1 hT
      have hH' : u.pc ≤ windowEnd loop := by
        simpa only [windowEnd, hX, List.not_mem_nil, or_false] using hH
      exact hFinish hL hH' hS (fun _ => hF) (hReg _ hK)
    · obtain ⟨hL, hH, hS, hF, _, hReg, _⟩ := windowEvent (loopWindow loop) hl hh ht.1 hE
      exact hFinish hL hH hS (fun hP =>
        hF.elim Option.isNone_iff_eq_none.mp (fun hp => False.elim (by omega))) (hReg _ hK)
  rcases Mma.cutWalkInterval hw hLo hHi ⟨hs, rfl⟩ (hE ▸ hCut) hStep with
    h | ⟨u, rest, tail, hU, hF, ⟨hS, hWord⟩, hW, hCount⟩
  · exact .inl (h.trans hBound)
  · exact .inr ⟨u, rest, tail, by simpa only [hE, List.mem_singleton] using hU,
      hF, hS, hWord, hW, hCount.trans (Nat.add_le_add_right hBound _)⟩

theorem noLocalEvent {l : Launch} {g : Nat} {s u : TState} {e : Event} {i : Instr}
    (hc : kernel.code[s.pc]? = some i) (hl : i.op.isLocal = true)
    (he : EStep kernel Assumptions.all l g s e (some u)) : False := by
  obtain ⟨j, hj, hFalse, _⟩ := estep_event_source he
  rw [hc] at hj
  obtain rfl := Option.some.inj hj
  rw [hl] at hFalse
  contradiction

theorem tailMoveCode (loop : ScoreLoop) :
    let site := scoreLoopSite loop
    ∃ m, kernel.code[site.increment + 2]? = some ⟨none, .move m⟩ ∧
      (.move m : Op).isLocal = true ∧
      site.word ∉ writesRegs (.move m) ∧ site.pred ∉ writesRegs (.move m) := by
  cases loop
  · exact ⟨_, Flow.code_6652, rfl, by decide, by decide⟩
  · exact ⟨_, Flow.code_7603, rfl, by decide, by decide⟩

theorem tailBranchCode (loop : ScoreLoop) :
    let site := scoreLoopSite loop
    kernel.code[site.increment + 3]? = some ⟨some (site.pred, false), .bra site.head false⟩ := by
  cases loop
  · exact Flow.code_6653
  · exact Flow.code_7604

theorem tailMoveFrame (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    (hs : s.pc = (scoreLoopSite loop).increment + 2)
    (ht : Tau kernel Assumptions.all l g s u) :
    let site := scoreLoopSite loop
    u.pc = site.increment + 3 ∧ u.sub = s.sub ∧ u.fault = none ∧
      u.regs site.word = s.regs site.word ∧ u.regs site.pred = s.regs site.pred := by
  obtain ⟨m, hc, _, hR, hT⟩ := tailMoveCode loop
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hs]; cases loop <;> decide
  rw [← hs] at hc
  obtain ⟨i, hI, hF, hExec⟩ := tauScoreSource ht
  rw [hc] at hI
  obtain rfl := Option.some.inj hI
  rcases hExec with ⟨_, hG⟩ | ⟨_, _, hEx⟩
  · cases hG
  · have hL := (scoreExecLocal hEx).resolve_right (fun ⟨_, hS, _, _⟩ => hOff hS)
    have hP := hL.pc.resolve_right id
    exact ⟨by simpa only [nextPc, hs, Nat.add_assoc] using hP, hL.sub, hL.fault.trans hF,
      hL.regs _ hR, hL.regs _ hT⟩

theorem tailBranchFrame (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    {b : Bool} (hs : s.pc = (scoreLoopSite loop).increment + 3)
    (hR : s.regs (scoreLoopSite loop).pred = some (.pred b))
    (ht : Tau kernel Assumptions.all l g s u) :
    let site := scoreLoopSite loop
    u.pc = (if b then site.head else site.increment + 4) ∧ u.sub ≤ s.sub ∧ u.regs = s.regs := by
  dsimp only
  have hc := tailBranchCode loop
  dsimp only at hc
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hs]; cases loop <;> decide
  rw [← hs] at hc
  obtain ⟨i, hI, _, hExec⟩ := tauScoreSource ht
  rw [hc] at hI
  obtain rfl := Option.some.inj hI
  have hG : guardHolds s (some ((scoreLoopSite loop).pred, false)) = .ok b := by
    simp [guardHolds, readReg, hR, bind, Except.bind, pure, Except.pure]
  rcases hExec with ⟨rfl, hg⟩ | ⟨hg, _, he⟩
  · rw [hG] at hg
    obtain rfl := Except.ok.inj hg
    exact ⟨by simp [skip, hs], Nat.zero_le _, rfl⟩
  · rw [hG] at hg
    obtain rfl := Except.ok.inj hg
    obtain ⟨hPc, hSub, _, hRegs⟩ := localBranchKept he hOff
    exact ⟨hPc, hSub.le, hRegs⟩

private theorem cutScoreTail (loop : ScoreLoop) {l : Launch} {g : Nat} {s : TState}
    {b : Bool} {es : List Event} {vs : List Visit}
    (hp : s.pc = (scoreLoopSite loop).increment + 2)
    (hR : s.regs (scoreLoopSite loop).pred = some (.pred b))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    let site := scoreLoopSite loop
    let cutoff := site.increment + 4
    Mma.countedUntil cutoff vs ≤ 1 ∨
      ∃ u rest tail, u.pc = (if b then site.head else cutoff) ∧ u.sub ≤ s.sub ∧
        u.regs site.word = s.regs site.word ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        Mma.countedUntil cutoff vs ≤ Mma.countedUntil cutoff tail := by
  dsimp only
  cases hw with
  | stop => exact .inl (by simp [Mma.countedUntil])
  | ev h _ =>
    obtain ⟨m, hc, hl, _, _⟩ := tailMoveCode loop
    exact (noLocalEvent (hp.symm ▸ hc) hl h).elim
  | @last _ e h =>
    have hP : s.pc < (scoreLoopSite loop).increment + 4 := by omega
    left
    have h := List.countP_le_length (l := [e]) (p := Event.counts)
    simpa [Mma.countedUntil, hP, visit_pc, visit_ev, List.filterMap_cons] using h
  | @tau s t es vs ht hw =>
    obtain ⟨hPc, hSub, hFault, hWord, hPred⟩ := tailMoveFrame loop hp ht
    have hR' := hPred.trans hR
    have h1 : s.pc < (scoreLoopSite loop).increment + 4 := by omega
    have h2 : t.pc < (scoreLoopSite loop).increment + 4 := by omega
    cases hw with
    | stop => exact .inl (by simp [Mma.countedUntil, h1, visit_pc, visit_ev, List.filterMap_cons])
    | ev h _ =>
      have hc := tailBranchCode loop
      dsimp only at hc
      exact (noLocalEvent (hPc.symm ▸ hc) rfl h).elim
    | @last _ e h =>
      left
      have h := List.countP_le_length (l := [e]) (p := Event.counts)
      simpa [Mma.countedUntil, h1, h2, visit_pc, visit_ev, List.filterMap_cons] using h
    | tau hu hW =>
      obtain ⟨hEnd, hS, hU⟩ := tailBranchFrame loop hPc hR' hu
      refine .inr ⟨_, _, _, hEnd, hS.trans hSub.le, ?_, hW, ?_⟩
      · rw [hU]
        exact hWord
      · simp [Mma.countedUntil, h1, h2, visit_pc, visit_ev, List.filterMap_cons]

private theorem scoreLoopPrefixByDistance (loop : ScoreLoop) (distance : Nat) {l : Launch}
    {g w : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hDistance : scoreLoopDistance loop w = distance) (hw₀ : w < 2 ^ 32)
    (hs : s.pc = (scoreLoopSite loop).head) (hSub : s.sub ≤ 3)
    (hWord : s.regs (scoreLoopSite loop).word = some (b32 w))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    Mma.countedUntil ((scoreLoopSite loop).increment + 4) vs ≤ 8192 * distance := by
  let site := scoreLoopSite loop
  let cutoff := site.increment + 4
  have hBudget : 5 * (windowEnd loop - windowHead loop) + 2 + 1 ≤ 8192 := by
    cases loop <;> decide
  induction distance using Nat.strong_induction_on generalizing w s es vs with
  | h distance ih =>
    have hPos : 0 < distance := hDistance ▸ (scoreLoopDistance_pos loop hw₀).1
    have hTotal : 8192 ≤ 8192 * distance := Nat.le_mul_of_pos_right _ hPos
    rcases cutScoreWindow loop hw hs hSub (cutoff := cutoff)
      (by dsimp only [cutoff, site]; omega) with
      hShort | ⟨v, vEvents, vVisits, hv, hvF, hvS, hvR, hvWalk, hvCount⟩
    · exact hShort.trans ((by omega :
        5 * (windowEnd loop - windowHead loop) + 2 ≤ 8192).trans hTotal)
    · obtain ⟨t, hRun, ht, htS, htF, htWord, htPred⟩ :=
        scoreLoopTestActual (l := l) (g := g) loop hw₀ hvF hv (hvR.trans hWord)
      rcases Mma.advanceWalkLocals hRun hvWalk with hNo | ⟨afterTest, _, hShift, htWalk⟩
      · subst vEvents
        have hz := Mma.zeroCountNoEvents hvWalk cutoff
        rw [hz, Nat.add_zero] at hvCount
        exact hvCount.trans ((by omega :
          5 * (windowEnd loop - windowHead loop) + 2 ≤ 8192).trans hTotal)
      · have hPrefix := hvCount.trans
            (Nat.add_le_add_left (hShift cutoff) (5 * (windowEnd loop - windowHead loop) + 2))
        rcases cutScoreTail loop ht htPred htWalk with
          hTail | ⟨u, rest, tail, hu, huS, huR, huWalk, huCount⟩
        · exact hPrefix.trans ((Nat.add_le_add_left hTail _).trans (hBudget.trans hTotal))
        · have huPrefix := hPrefix.trans (Nat.add_le_add_left huCount _)
          by_cases hContinue : (w + 1) % 2 ^ 32 ≠ (scoreLoopSite loop).sentinel
          · have hw' : (w + 1) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
            have hDec := scoreLoopDistance_step loop hw₀ hContinue
            have huPc : u.pc = site.head := by
              simpa only [decide_eq_true_eq, ite_eq_left hContinue] using hu
            let n := scoreLoopDistance loop ((w + 1) % 2 ^ 32)
            have hN : n + 1 = distance := hDec.trans hDistance
            have hRest := ih n (by omega) (w := (w + 1) % 2 ^ 32) (s := u)
              rfl hw' huPc (huS.trans (htS.symm ▸ hvS)) (huR.trans htWord) huWalk
            have hScaled : 8192 * n + 8192 = 8192 * distance := by
              rw [← Nat.mul_succ]
              exact congrArg (8192 * ·) hN
            exact huPrefix.trans ((Nat.add_le_add_left hRest _).trans
              (by have := hBudget; omega))
          · have huPc : u.pc = cutoff := by
              simpa only [hContinue, decide_false, Bool.false_eq_true, ite_false] using hu
            have hZero : Mma.countedUntil cutoff tail = 0 := by
              cases huWalk <;> simp [Mma.countedUntil, huPc, visit_pc]
            rw [hZero, Nat.add_zero] at huPrefix
            exact huPrefix.trans ((by omega :
              5 * (windowEnd loop - windowHead loop) + 2 ≤ 8192).trans hTotal)

/-- Every finite realized prefix of either score loop has a uniform counted-event bound. -/
theorem scoreLoopPrefixUniform (loop : ScoreLoop) {l : Launch} {g w : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : s.pc = (scoreLoopSite loop).head) (hSub : s.sub ≤ 3)
    (hWord : s.regs (scoreLoopSite loop).word = some (b32 w)) (hw₀ : w < 2 ^ 32) :
    Mma.countedUntil ((scoreLoopSite loop).increment + 4) vs ≤ 8192 * 2 ^ 32 :=
  (scoreLoopPrefixByDistance loop _ rfl hw₀ hs hSub hWord hw).trans
    (Nat.mul_le_mul_left _ (scoreLoopDistance_pos loop hw₀).2)

end
end PTX.Kernels.TmlFa4Fwd.Softmax

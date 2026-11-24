-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopStep
public import Kernels.TmlFa4Fwd.Proof.MmaWideCounter
public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Lemmas.Flow.WarpUniform

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private def rankPoll (pc : Nat) : Option (Nat × Nat) :=
  match pc with
  | 2295 => some (2294, 9669)
  | 2298 => some (2297, 9670)
  | 2336 => some (2335, 9680)
  | 2353 => some (2352, 9681)
  | 2420 => some (2419, 9698)
  | 2451 => some (2450, 9708)
  | _ => none

private def rankRetry (pc : Nat) : Option Nat :=
  match pc with
  | 2296 => some 2294
  | 2299 => some 2297
  | 2337 => some 2335
  | 2354 => some 2352
  | 2421 => some 2419
  | 2452 => some 2450
  | _ => none

private def floorPc (pc : Nat) : Nat :=
  ((rankPoll pc).map Prod.fst).getD ((rankRetry pc).getD pc)

private def pollResult (s : TState) (reg : Nat) : Bool :=
  match s.regs reg with
  | some (.pred actual) => actual
  | _ => false

/-- A successful wait advances the progress rank before its branch.
The three positions reached by a failed wait have the same rank. -/
private def steadyProgress (s : TState) : Nat :=
  floorPc s.pc + (((rankPoll s.pc).map (fun probe => pollResult s probe.2)).getD false).toNat

private theorem floor_le_progress (s : TState) : floorPc s.pc ≤ steadyProgress s := by
  unfold steadyProgress
  omega

private theorem progress_le_pc (s : TState) : steadyProgress s ≤ s.pc := by
  unfold steadyProgress floorPc rankPoll rankRetry
  split <;> simp_all [Bool.toNat] <;> (try split) <;> (try simp only [Option.getD]) <;> omega

private theorem codeMember {pc : Nat} {ins : Instr} (hlo : 2291 ≤ pc) (hhi : pc < 2530)
    (hc : kernel.code[pc]? = some ins) :
    (ins, pc) ∈ ((kernel.code.drop 2291).take 239).zipIdx 2291 := by
  apply List.mem_of_getElem? (i := pc - 2291)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hlo, hc]
  rfl

private def rankCodeOk (ins : Instr) (pc : Nat) : Bool :=
  match ins.op with
  | .mbarWait dest .. => ins.guard.isNone && rankPoll (pc + 1) == some (pc, dest) &&
      rankPoll pc == none && rankRetry pc == none
  | _ => if (rankPoll pc).isSome || (rankRetry pc).isSome then ins.op.isLocal
    else (if ins.op.isLocal then pc ≤ floorPc (pc + 1) else pc < floorPc (pc + 1)) &&
      (pc ≤ floorPc (nextPc ins.op pc))

private theorem rankCode {pc : Nat} {ins : Instr} (hlo : 2291 ≤ pc) (hhi : pc < 2530)
    (hc : kernel.code[pc]? = some ins) : rankCodeOk ins pc = true := by
  have hall : (((kernel.code.drop 2291).take 239).zipIdx 2291).all
      (fun pair => rankCodeOk pair.1 pair.2) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact List.all_eq_true.mp hall (ins, pc) (codeMember hlo hhi hc)

private theorem progressAtPollHead {s : TState} (hPoll : rankPoll s.pc = none)
    (hRetry : rankRetry s.pc = none) : steadyProgress s = s.pc := by
  simp [steadyProgress, floorPc, hPoll, hRetry]

variable {l : Launch}

private theorem eventProgress {g : Nat} {s u : TState} {e : Event} (hlo : 2291 ≤ s.pc)
    (hhi : s.pc < 2530) (he : EStep kernel Assumptions.all l g s e (some u)) :
    steadyProgress s + (if e.counts then 1 else 0) ≤ steadyProgress u := by
  obtain ⟨ins, hc, hl, hf⟩ := estep_event_source he
  have hOk := rankCode hlo hhi hc
  cases hop : ins.op with
  | mbarWait dst base off par acq scope =>
    rw [hop] at hf
    obtain ⟨loc, parity, ok, scope', rfl, rfl⟩ := fires_wait hf
    have hShape : ins.guard = none ∧ rankPoll (s.pc + 1) = some (s.pc, dst) ∧
        rankPoll s.pc = none ∧ rankRetry s.pc = none := by
      simpa [rankCodeOk, hop, and_assoc] using hOk
    rw [progressAtPollHead hShape.2.2.1 hShape.2.2.2]
    cases ok <;> simp [steadyProgress, floorPc, next, hShape.2.1, pollResult, setReg, Event.counts]
  | _ =>
    have hAdvance := (steadyEventFrame hlo hhi he).1
    have hRank : s.pc < floorPc (s.pc + 1) := by
      simp [rankCodeOk, hop] at hOk
      split at hOk <;> simp_all
    have hStart := progress_le_pc s
    have hStop := floor_le_progress u
    rw [hAdvance] at hStop
    split <;> omega

set_option maxRecDepth 100000 in
private theorem pollBranchCode {pc base dst : Nat} (hp : rankPoll pc = some (base, dst)) :
    (∃ uni, kernel.code[pc]? = some ⟨some (dst, false), .bra (base + 3) uni⟩) ∧
      floorPc (pc + 1) = base ∧ floorPc (base + 3) = base + 3 := by
  unfold rankPoll at hp
  split at hp
  all_goals simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals obtain ⟨rfl, rfl⟩ := hp
  · exact ⟨⟨_, Flow.code_2295⟩, rfl, rfl⟩
  · exact ⟨⟨_, Flow.code_2298⟩, rfl, rfl⟩
  · exact ⟨⟨_, Flow.code_2336⟩, rfl, rfl⟩
  · exact ⟨⟨_, Flow.code_2353⟩, rfl, rfl⟩
  · exact ⟨⟨_, Flow.code_2420⟩, rfl, rfl⟩
  · exact ⟨⟨_, Flow.code_2451⟩, rfl, rfl⟩

set_option maxRecDepth 100000 in
private theorem retryBranchCode {pc base : Nat} (hp : rankRetry pc = some base) :
    (∃ uni, kernel.code[pc]? = some ⟨none, .bra base uni⟩) ∧
      floorPc base = base ∧ base ≤ floorPc (pc + 1) := by
  unfold rankRetry at hp
  split at hp
  all_goals simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst base
  · exact ⟨⟨_, Flow.code_2296⟩, rfl, by decide⟩
  · exact ⟨⟨_, Flow.code_2299⟩, rfl, by decide⟩
  · exact ⟨⟨_, Flow.code_2337⟩, rfl, by decide⟩
  · exact ⟨⟨_, Flow.code_2354⟩, rfl, by decide⟩
  · exact ⟨⟨_, Flow.code_2421⟩, rfl, by decide⟩
  · exact ⟨⟨_, Flow.code_2452⟩, rfl, by decide⟩

private theorem noSteadyBrx {pc target : Nat} {ins : Instr} (hlo : 2291 ≤ pc) (hhi : pc < 2530)
    (hc : kernel.code[pc]? = some ins) : ¬ BrxTarget ins.op target := by
  have hControl := steadyControl hlo (by omega) hc
  cases hop : ins.op <;> simp_all [BrxTarget]

private theorem tauProgress {g : Nat} {s u : TState} (hlo : 2291 ≤ s.pc) (hhi : s.pc < 2530)
    (ht : Tau kernel Assumptions.all l g s u) : steadyProgress s ≤ steadyProgress u := by
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rw [← out_eq_core (by omega) (by omega)]
    exact ht
  have hStop := floor_le_progress u
  cases hp : rankPoll s.pc with
  | some site =>
    obtain ⟨base, dest⟩ := site
    obtain ⟨⟨uni, hc⟩, hFall, hTarget⟩ := pollBranchCode hp
    have hRank : steadyProgress s = base + (pollResult s dest).toNat := by
      simp [steadyProgress, floorPc, hp]
    rw [hRank]
    have hTau := tau_core_frame hc ht'
    have hu : u.pc = s.pc + 1 ∨ u.pc = base + 3 := by
      rcases hTau with rfl | h
      · exact .inl rfl
      · exact .inr (h.pc.resolve_right id)
    cases hResult : pollResult s dest with
    | false =>
      rcases hu with h | h <;> rw [h] at hStop <;>
        simp only [hFall, hTarget] at hStop <;> simp only [Bool.toNat_false, Nat.add_zero] <;> omega
    | true =>
      have hReg : s.regs dest = some (.pred true) := by
        unfold pollResult at hResult
        split at hResult
        · simp_all
        · cases hResult
      have hGuard : guardHolds s (some (dest, false)) = .ok true := by
        simp [guardHolds, readReg, hReg, bind, Except.bind, pure, Except.pure]
      have hFault : s.fault = none := by
        cases hf : s.fault
        · rfl
        · simp [Tau, out, hf] at ht'
      have hU : u.pc = base + 3 := by
        unfold Tau at ht'
        simp [out, hFault, hc, hGuard, execLocalA, execLocalRule, execLocal,
          Op.isLocal, Op.rule, execBranch, pure, Except.pure] at ht'
        obtain rfl := ht'.symm
        rfl
      rw [hU, hTarget] at hStop
      simp only [Bool.toNat_true]
      omega
  | none =>
    cases hr : rankRetry s.pc with
    | some base =>
      obtain ⟨⟨uni, hc⟩, hTarget, hFall⟩ := retryBranchCode hr
      have hRank : steadyProgress s = base := by simp [steadyProgress, floorPc, hp, hr]
      rw [hRank]
      rcases tau_core_frame hc ht' with rfl | h
      · change floorPc (s.pc + 1) ≤ _ at hStop
        omega
      · have hPc : u.pc = base := h.pc.resolve_right id
        rw [hPc, hTarget] at hStop
        exact hStop
    | none =>
      rw [progressAtPollHead hp hr]
      obtain ⟨ins, hc⟩ := tau_core_has_code ht'
      have hCode := rankCode hlo hhi hc
      cases hop : ins.op with
      | mbarWait dest base off par acq scope =>
        have hUn : ins.guard = none := by
          simp [rankCodeOk, hop, hp, hr] at hCode
          exact hCode.1
        obtain ⟨guard, op⟩ := ins
        simp only at hop hUn
        subst guard op
        exact (tau_core_not_event hc rfl ht').elim
      | _ =>
        have hCode' : (s.pc ≤ floorPc (s.pc + 1)) ∧ s.pc ≤ floorPc (nextPc ins.op s.pc) := by
          cases hLoc : ins.op.isLocal <;> rw [hop] at hLoc ⊢
          · simp [rankCodeOk, hop, hp, hr, hLoc] at hCode
            have hFirst := hCode.1
            exact ⟨by omega, hCode.2⟩
          · simpa [rankCodeOk, hop, hp, hr, hLoc] using hCode
        rcases tau_core_frame hc ht' with rfl | h
        · change floorPc (s.pc + 1) ≤ _ at hStop
          exact hCode'.1.trans hStop
        · rcases h.pc with hPc | hBrx
          · rw [hPc] at hStop
            exact hCode'.2.trans hStop
          · exact (noSteadyBrx hlo hhi hc hBrx).elim

/-- The two steady ready gates are paid once per completed loop traversal. -/
def steadyReadySite : Fin 2 → Nat × Nat
  | 0 => (2294, 9669)
  | _ => (2352, 9681)

def steadyReadyAt (gate : Fin 2) (event : Event) : Bool :=
  match event.kind with
  | .wait _ _ true _ _ => event.pc == (steadyReadySite gate).1
  | _ => false

/-- In an unfinished traversal, a successful ready reply is counted even while
the lane has yet to take its exit branch. -/
@[no_expose] def steadyReadyCredit (gate : Fin 2) (s : TState) : Nat :=
  if (steadyReadySite gate).1 + 2 < s.pc then 1
  else if s.pc = (steadyReadySite gate).1 + 1 then
    (pollResult s (steadyReadySite gate).2).toNat
  else 0

private theorem beforeSteadyReadyJump (gate : Fin 2) {pc : Nat} {ins : Instr}
    (hLo : 2291 ≤ pc) (hHi : pc < (steadyReadySite gate).1)
    (hc : kernel.code[pc]? = some ins) : nextPc ins.op pc ≤ (steadyReadySite gate).1 := by
  let window := ((kernel.code.drop 2291).take 239).zipIdx 2291
  have hAll : window.all (fun (i, pos) =>
      decide ((pos < (steadyReadySite gate).1) → (nextPc i.op pos ≤ (steadyReadySite gate).1))) =
    true := by
    fin_cases gate <;> set_option maxRecDepth 100000 in kernel_rfl
  have hHead : (steadyReadySite gate).1 < 2530 := by fin_cases gate <;> decide
  exact of_decide_eq_true (List.all_eq_true.mp hAll (ins, pc)
    (codeMember hLo (hHi.trans hHead) hc)) hHi

private theorem steadyReadyCode (gate : Fin 2) :
    ∃ base parity off, kernel.code[(steadyReadySite gate).1]? = some
      ⟨none, .mbarWait (steadyReadySite gate).2 base off parity true .cta⟩ := by
  fin_cases gate
  · exact ⟨_, _, _, Flow.code_2294⟩
  · exact ⟨_, _, _, Flow.code_2352⟩

private theorem steadyReadyBranch (gate : Fin 2) :
    ∃ uni, kernel.code[(steadyReadySite gate).1 + 1]? = some
      ⟨some ((steadyReadySite gate).2, false), .bra ((steadyReadySite gate).1 + 3) uni⟩ := by
  fin_cases gate
  · exact ⟨_, Flow.code_2295⟩
  · exact ⟨_, Flow.code_2353⟩

private theorem steadyReadyRetry (gate : Fin 2) :
    ∃ uni, kernel.code[(steadyReadySite gate).1 + 2]? = some
      ⟨none, .bra (steadyReadySite gate).1 uni⟩ := by
  fin_cases gate
  · exact ⟨_, Flow.code_2296⟩
  · exact ⟨_, Flow.code_2354⟩

private theorem creditBeforeSteadyReady (gate : Fin 2) {s : TState}
    (h : s.pc ≤ (steadyReadySite gate).1) : steadyReadyCredit gate s = 0 := by
  simp only [steadyReadyCredit, ite_eq_right (by omega : ¬ (steadyReadySite gate).1 + 2 < s.pc),
    ite_eq_right (by omega : s.pc ≠ (steadyReadySite gate).1 + 1)]

theorem steadyReadyCreditEntry (gate : Fin 2) {s : TState} (h : s.pc = 2291) :
    steadyReadyCredit gate s = 0 :=
  creditBeforeSteadyReady gate (h.symm ▸ (by fin_cases gate <;> decide))

theorem steadyReadyCreditTest (gate : Fin 2) {s : TState} (h : s.pc = 2530) :
    steadyReadyCredit gate s = 1 := by
  have hPaid : (steadyReadySite gate).1 + 2 < s.pc := by rw [h]; fin_cases gate <;> decide
  unfold steadyReadyCredit
  exact ite_eq_left hPaid

theorem steadyReadyCreditTau (gate : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    (hLo : 2291 ≤ s.pc) (hHi : s.pc < 2530)
    (hSub : s.sub = 0) (hAcc : s.acc = [])
    (hTau : Tau kernel Assumptions.all l g s u) :
    steadyReadyCredit gate u = steadyReadyCredit gate s := by
  have hCore : Tau kernel [] l g s u := by
    unfold Tau at hTau ⊢
    rwa [← out_eq_core (by omega) (by omega)]
  let head := (steadyReadySite gate).1
  let result := (steadyReadySite gate).2
  have lower {t : TState} (ht : t.pc ≤ head) : steadyReadyCredit gate t = 0 :=
    creditBeforeSteadyReady gate ht
  by_cases hEarly : s.pc < head
  · obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    have hTaken := beforeSteadyReadyJump gate hLo hEarly hc
    have hu : u.pc ≤ head := by
      rcases tau_core_frame hc hCore with rfl | hf
      · change s.pc + 1 ≤ head
        omega
      · rcases hf.pc with h | h
        · exact h.trans_le hTaken
        · exact (noSteadyBrx hLo hHi hc h).elim
    exact (lower hu).trans (lower hEarly.le).symm
  by_cases hPaid : head + 2 < s.pc
  · have hNext := (steadyTauFrame hLo hHi hSub hAcc hTau).1
    have hPast : head+2 < u.pc := by
      rcases hNext with h | h
      · omega
      · fin_cases gate <;>
          simp [head, steadyReadySite, steadyPollBackedges] at hPaid h ⊢ <;> omega
    simp [steadyReadyCredit, head, hPaid, hPast]
  have hCases : s.pc = head ∨ s.pc = head + 1 ∨ s.pc = head + 2 := by omega
  rcases hCases with h | h | h
  · obtain ⟨_, _, _, hCode⟩ := steadyReadyCode gate
    dsimp only [head] at h
    rw [← h] at hCode
    exact (tau_core_not_event hCode rfl hCore).elim
  · cases hResult : pollResult s result
    · obtain ⟨uni, hCode⟩ := steadyReadyBranch gate
      dsimp only [head] at h
      rw [← h] at hCode
      have hGuard : guardHolds s (some (result, false)) ≠ .ok true := by
        intro hTrue
        cases hReg : s.regs result with
        | none => simp [guardHolds, readReg, hReg, bind, Except.bind] at hTrue
        | some v =>
          cases v <;> simp [guardHolds, readReg, hReg, bind, Except.bind, pure, Except.pure]
            at hTrue
          subst_vars
          simp [pollResult, hReg] at hResult
      have hf : s.fault = none := by
        cases hf : s.fault
        · rfl
        · simp [Tau, out, hf] at hCore
      have hNext : u.pc = head + 2 := by
        unfold Tau at hCore
        rw [out, hf, hCode] at hCore
        change (match guardHolds s (some (result, false)) with
          | .error f => Out.ev (.ub f)
          | .ok false => Out.tau (skip s)
          | .ok true =>
            if (Op.bra (head + 3) uni).isLocal then
              match execLocalA [] l g s (.bra (head + 3) uni) with
              | .ok t => Out.tau t
              | .error f => Out.ev (.ub f)
            else Out.ev (eventTmpl [] l g s (.bra (head + 3) uni))) = Out.tau u at hCore
        cases hGuard' : guardHolds s (some (result, false)) with
        | error f => simp [hGuard'] at hCore
        | ok b =>
          cases b
          · have hEq := Out.tau.inj (by simpa only [hGuard'] using hCore)
            rw [← hEq]
            change s.pc + 1 = head + 2
            omega
          · exact (hGuard hGuard').elim
      change pollResult s (steadyReadySite gate).2 = false at hResult
      simp [steadyReadyCredit,head,hNext,h,hResult]
    · have hRegs : s.regs result = some (.pred true) := by
        unfold pollResult at hResult
        cases hR : s.regs result with
        | none => simp [hR] at hResult
        | some v =>
          cases v <;> simp_all
      obtain ⟨uni, hCode⟩ := steadyReadyBranch gate
      dsimp only [head] at h
      rw [← h] at hCode
      have hf : s.fault = none := by
        cases hf : s.fault
        · rfl
        · simp [Tau, out, hf] at hCore
      have hNext : u.pc = head+3 := by
        have hGuard : guardHolds s (some (result,false)) = .ok true := by
          simp [guardHolds,readReg,hRegs,bind,Except.bind,pure,Except.pure]
        unfold Tau at hCore
        simp [out, hf, hCode, result, hGuard, execLocalA, execLocalRule, execLocal,
          Op.isLocal, Op.rule, execBranch, pure, Except.pure] at hCore
        obtain rfl := hCore.symm
        rfl
      change pollResult s (steadyReadySite gate).2 = true at hResult
      rw [steadyReadyCredit, hNext, ite_eq_left (by omega), steadyReadyCredit, h]
      simp [hResult]
  · obtain ⟨uni, hCode⟩ := steadyReadyRetry gate
    dsimp only [head] at h
    rw [← h] at hCode
    have hf : s.fault = none := by
      cases hf : s.fault
      · rfl
      · simp [Tau, out, hf] at hCore
    have hPc : u.pc = head := by
      unfold Tau at hCore
      simp [out, hf, hCode, guardHolds, execLocalA, execLocalRule, execLocal,
        Op.isLocal, Op.rule, execBranch, pure, Except.pure] at hCore
      obtain rfl := hCore.symm
      rfl
    rw [lower hPc.le]
    simp [steadyReadyCredit,h]

theorem steadyReadyCreditEvent (gate : Fin 2) {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 2291 ≤ s.pc) (hHi : s.pc < 2530)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    steadyReadyCredit gate u = steadyReadyCredit gate s + (steadyReadyAt gate e).toNat := by
  let head := (steadyReadySite gate).1
  have hNext := (steadyEventFrame hLo hHi he).1
  have hNo (hNe : s.pc ≠ head) : steadyReadyAt gate e = false := by
    obtain ⟨site, kind⟩ := e
    have hSource : site = s.pc := estep_source_pc he
    have hSite : (site == (steadyReadySite gate).1) = false :=
      beq_eq_false_iff_ne.mpr (hSource.symm ▸ hNe)
    cases kind <;> try rfl
    case wait m parity ok acquire sc => cases ok <;> simp [steadyReadyAt,hSite]
  by_cases hEarly : s.pc < head
  · rw [creditBeforeSteadyReady gate (by omega : u.pc ≤ head),
      creditBeforeSteadyReady gate hEarly.le, hNo hEarly.ne]
    rfl
  by_cases hPaid : head + 2 < s.pc
  · have hPast : head+2 < u.pc := by omega
    have hMark := hNo (by omega)
    simp [steadyReadyCredit, head, hPaid, hPast, hMark]
  obtain ⟨ins, hCode, hl, hFire⟩ := estep_event_source he
  have hCases : s.pc = head ∨ s.pc = head + 1 ∨ s.pc = head + 2 := by omega
  rcases hCases with h | h | h
  · obtain ⟨_, _, _, hc⟩ := steadyReadyCode gate
    dsimp only [head] at h
    rw [← h, hCode] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨loc, parity, ok, _, rfl, rfl⟩ := fires_wait hFire
    cases ok <;> simp [steadyReadyAt, steadyReadyCredit, h, next, pollResult, setReg]
  · obtain ⟨_, hc⟩ := steadyReadyBranch gate
    dsimp only [head] at h
    rw [← h, hCode] at hc
    obtain rfl := Option.some.inj hc
    cases hl
  · obtain ⟨_, hc⟩ := steadyReadyRetry gate
    dsimp only [head] at h
    rw [← h, hCode] at hc
    obtain rfl := Option.some.inj hc
    cases hl

/-- Count events before the trace first reaches the cutoff PC. -/
def countedUntil (cutoff : Nat) (visits : List Visit) : Nat :=
  ((visits.takeWhile fun v => v.pc < cutoff).filterMap Visit.ev).countP Event.counts

/-- Consuming known silent steps leaves the same event-bearing prefix or reaches its end. -/
theorem advanceWalkLocals {g n : Nat} {s u : TState} {es : List Event} {vs : List Visit}
    (hr : run kernel Assumptions.all l g n s = some u)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es = [] ∨ ∃ post, post.length + n = vs.length ∧
      (∀ cutoff, countedUntil cutoff vs ≤ countedUntil cutoff post) ∧
      Walk kernel Assumptions.all l g u es post := by
  induction n generalizing s es vs with
  | zero =>
    simp only [run, Option.some.injEq] at hr
    subst u
    exact .inr ⟨vs, by simp, fun _ => le_rfl, hw⟩
  | succ n ih =>
    simp only [run] at hr
    cases hs : tauStep kernel Assumptions.all l g s with
    | none => simp [hs] at hr
    | some t =>
      rw [hs, Option.bind_some] at hr
      have hTau := tauStep_iff.mp hs
      cases hw with
      | stop => exact .inl rfl
      | tau ht hWalk =>
        have hEq := Out.tau.inj (hTau.symm.trans ht)
        subst t
        obtain hz | ⟨post, hLen, hCut, hw'⟩ := ih hr hWalk
        · exact .inl hz
        · refine .inr ⟨post, by simp; omega, fun cutoff => ?_, hw'⟩
          by_cases hPC : s.pc < cutoff
          · simpa [countedUntil, hPC, visit_pc, visit_ev, List.filterMap_cons] using hCut cutoff
          · simp [countedUntil, hPC, visit_pc]
      | ev he _ => exact (not_tau_of_stops (stops_of_estep he) hTau).elim
      | last he => exact (not_tau_of_stops (stops_of_estep he) hTau).elim

/-- An event-free walk contributes no counted event before any cutoff. -/
theorem zeroCountNoEvents {g : Nat} {s : TState} {vs : List Visit}
    (h : Walk kernel Assumptions.all l g s [] vs) (cut : Nat) : countedUntil cut vs = 0 := by
  have hz : vs.filterMap Visit.ev = [] := h.events.symm
  unfold countedUntil
  have hSub : (vs.takeWhile fun v => v.pc < cut) <+: vs := List.takeWhile_prefix _
  have hPref : ((vs.takeWhile fun v => v.pc < cut).filterMap Visit.ev) <+: [] := by
    simpa only [hz] using hSub.filterMap (f := Visit.ev)
  rw [List.prefix_nil.mp hPref]
  rfl

private theorem zeroCountExit {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (h : Walk kernel Assumptions.all l g s es vs) (hc : 2534 ≤ s.pc) :
    countedUntil 2534 vs = 0 := by
  cases h <;> simp [countedUntil, visit_pc, Nat.not_lt.mpr hc]

private theorem steadyLoopCount {g : Nat} :
    ∀ fuel n {s : TState} {es : List Event} {vs : List Visit},
      vs.length = fuel → (2291 ≤ s.pc ∧ s.pc ≤ 2530) → 2 ≤ n → n ≤ 2 ^ 32 + 1 →
      At s s.pc [(7204, wideCounterWord n)] → Walk kernel Assumptions.all l g s es vs →
      countedUntil 2534 vs ≤ 256 * (n - 2) + (2531 - steadyProgress s) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro n s es vs hLength hSlice hn hN hAt hw
    obtain ⟨hLo, hHi⟩ := hSlice
    by_cases hEnd : s.pc = 2530
    · obtain ⟨u, hLocals, hU⟩ := stepWideCounter (l := l) (g := g) hn hN
        (by simpa only [hEnd] using hAt)
      rcases advanceWalkLocals hLocals hw with hz | ⟨post, hCount, hcut, hWalk⟩
      · subst es
        simp [zeroCountNoEvents hw]
      · by_cases hContinue : 2 < n
        · have hPC : u.pc = 2291 := by simpa only [ite_eq_left hContinue] using hU.1
          have hBound := ih post.length (by omega) (n - 1) rfl (by omega) (by omega) (by omega)
            (by simpa only [hPC, ite_eq_left hContinue] using hU) hWalk
          have hP : steadyProgress u = 2291 := by
            rw [progressAtPollHead (by rw [hPC]; rfl) (by rw [hPC]; rfl), hPC]
          have hP' : steadyProgress s = 2530 := by
            rw [progressAtPollHead (by rw [hEnd]; rfl) (by rw [hEnd]; rfl), hEnd]
          rw [hP] at hBound
          rw [hP']
          have := (hcut 2534).trans hBound
          omega
        · have hPC : u.pc = 2534 := by simpa only [ite_eq_right hContinue] using hU.1
          have hZ := zeroCountExit hWalk hPC.ge
          have hc := hcut 2534
          rw [hZ] at hc
          exact hc.trans (Nat.zero_le _)
    · have hLt : s.pc < 2530 := by omega
      cases hw with
      | stop => simp [countedUntil]
      | @tau s u es vs ht hw =>
        have hFrame := steadyTauFrame hLo hLt hAt.2.1 hAt.2.2.1 ht
        have hU : At u u.pc [(7204, wideCounterWord n)] := by
          refine ⟨rfl, hFrame.2.2.2.1.trans hAt.2.1, hFrame.2.2.2.2.1.trans hAt.2.2.1,
            hFrame.2.2.2.2.2.1.trans hAt.2.2.2.1, ?_, trivial⟩
          exact hFrame.2.2.2.2.2.2.trans hAt.2.2.2.2.1
        have hRank := tauProgress hLo hLt ht
        have hCount := ih vs.length (by simp only [List.length_cons] at hLength; omega) n rfl
          ⟨hFrame.2.1, hFrame.2.2.1⟩ hn hN hU hw
        have hMon := Nat.add_le_add_left (Nat.sub_le_sub_left hRank 2531) (256 * (n - 2))
        simpa [countedUntil, visit_pc, visit_ev, List.filterMap_cons, show s.pc < 2534 by omega]
          using hCount.trans hMon
      | @ev s u e es vs he hw =>
        have hFrame := steadyEventFrame hLo hLt he
        have hU : At u u.pc [(7204, wideCounterWord n)] := by
          refine ⟨rfl, hFrame.2.1.trans hAt.2.1, hFrame.2.2.1.trans hAt.2.2.1,
            hFrame.2.2.2.1.trans hAt.2.2.2.1, ?_, trivial⟩
          exact hFrame.2.2.2.2.trans hAt.2.2.2.2.1
        have hRank := eventProgress hLo hLt he
        have hMax := (progress_le_pc u).trans (show u.pc ≤ 2530 by omega)
        have hCount := ih vs.length (by simp only [List.length_cons] at hLength; omega) n rfl
          (by omega) hn hN hU hw
        rw [countedUntil, List.takeWhile_cons]
        rw [ite_eq_left (show decide ((visit kernel l g s (some e)).pc < 2534) = true from
          decide_eq_true (show s.pc < 2534 by omega))]
        simp only [List.filterMap_cons, visit_ev, List.countP_cons]
        change countedUntil 2534 vs + (if e.counts then 1 else 0) ≤ _
        omega
      | @last s e he =>
        have hPC := progress_le_pc s
        have hBound : 1 ≤ 256 * (n - 2) + (2531 - steadyProgress s) := by omega
        simpa [countedUntil, visit_pc, visit_ev, show s.pc < 2534 by omega] using
          (List.countP_le_length (p := Event.counts) (l := [e])).trans hBound

/-- From entry to the tail of the steady loop, every trace prefix has at most a 256-event
budget per remaining counter decrement, excluding failed waits. -/
theorem steadyLoopPrefixBound {g n : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (h : Walk kernel Assumptions.all l g s es vs) (hn : 2 ≤ n) (hN : n ≤ 2 ^ 32 + 1)
    (hs : At s 2291 [(7204, wideCounterWord n)]) :
    (((vs.takeWhile fun v => v.pc < 2534).filterMap Visit.ev).countP Event.counts) ≤
      256 * (n - 1) := by
  have hp : steadyProgress s = 2291 := by
    rw [progressAtPollHead (by rw [hs.1]; rfl) (by rw [hs.1]; rfl), hs.1]
  have hb := steadyLoopCount (l := l) (g := g) vs.length n rfl (by rw [hs.1]; decide) hn hN
      (by simpa only [hs.1] using hs) h
  rw [hp] at hb
  change countedUntil 2534 vs ≤ _
  omega

/-- A uniformly bounded number of counted events suffices for any 32-bit trip word at
the decoded steady-loop entry. -/
theorem steadyLoopPrefixUniform {g word : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (h : Walk kernel Assumptions.all l g s es vs) (hw : word < 2 ^ 32)
    (hs : At s 2291 [(7204, b32 word)]) :
    (((vs.takeWhile fun v => v.pc < 2534).filterMap Visit.ev).countP Event.counts) ≤
      256 * 2 ^ 32 := by
  obtain ⟨n, hn, hN, hWord⟩ := wideCounterWord_surjective hw
  rw [hWord] at hs
  have hBound := steadyLoopPrefixBound h hn hN hs
  omega

end
end PTX.Kernels.TmlFa4Fwd.Mma

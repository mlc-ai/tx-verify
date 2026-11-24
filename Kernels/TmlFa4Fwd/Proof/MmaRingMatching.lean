-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
public import Kernels.TmlFa4Fwd.Proof.MmaRingAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Loader Prologue

noncomputable section

def recurringRelease (i : Fin 3) : Fin 4 := ⟨i.val + 1, by omega⟩
def pairWait (i : Fin 3) := slotWait (recurringRelease i)
def pairCommit (i : Fin 3) := commitSite (releaseCommitSite (recurringRelease i))

private theorem carrierGeometry (i : Fin 3) :
    (ringCarrier i).calcPc + 1 = (pairWait i).pc ∧
    (ringCarrier i).waitBase = (pairWait i).base ∧
    (ringCarrier i).releasePc = (pairCommit i).pc ∧
    (ringCarrier i).base = (pairCommit i).base ∧ (pairCommit i).off = 56 := by
  fin_cases i <;> decide

private def pollPairBand (i : Fin 3) (pc : Nat) : Prop :=
  (pairWait i).pc ≤ pc ∧ pc ≤ (pairWait i).pc + 2

private instance (i : Fin 3) (pc : Nat) : Decidable (pollPairBand i pc) :=
  inferInstanceAs (Decidable ((pairWait i).pc ≤ pc ∧ pc ≤ (pairWait i).pc + 2))

private def pairedWords (l : Launch) (i : Fin 3) (s : TState) : Prop :=
  pollPairBand i s.pc → ∃ stage : Fin 3,
    s.regs (ringCarrier i).base = some (b32 (l.sharedBase + 8 * stage.val)) ∧
    s.regs (ringCarrier i).waitBase = some (b32 (l.sharedBase + (8 * stage.val + 32)))

private def pairCode (i : Fin 3) (pc : Nat) (ins : Instr) : Bool :=
  (!decide (pollPairBand i pc) ||
    (!(mmaWrites ins.op).contains (ringCarrier i).base &&
     !(mmaWrites ins.op).contains (ringCarrier i).waitBase)) &&
    (!decide (pollPairBand i (pc + 1)) ||
      decide (pollPairBand i pc) || pc == (ringCarrier i).calcPc) &&
    match ins.op with
    | .bra target _ => !decide (pollPairBand i target) || decide (pollPairBand i pc)
    | .brx .. => false
    | _ => true

private theorem checkedPairCode (i : Fin 3) {pc : Nat} {ins : Instr}
    (hl : 1907 ≤ pc) (hh : pc < 2768) (hc : kernel.code[pc]? = some ins) :
    pairCode i pc ins = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have hAll : code.all (fun ins => pairCode i ins.2 ins.1) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  apply List.all_eq_true.mp hAll (ins, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hl, hc]
  rfl

private theorem pairStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : Fin 3) {g : Nat} {s u : TState} {e : Option Event} (hLo : 1907 ≤ s.pc)
    (hHi : s.pc < 2768) (hF : RingAddressFrame l s) (hPair : pairedWords l i s)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    pairedWords l i u := by
  intro hBand
  have keep (hs : pollPairBand i s.pc) :
      ∃ stage : Fin 3,
        u.regs (ringCarrier i).base = some (b32 (l.sharedBase + 8 * stage.val)) ∧
        u.regs (ringCarrier i).waitBase = some (b32 (l.sharedBase + (8 * stage.val + 32))) := by
    obtain ⟨stage, hb, hw⟩ := hPair hs
    have regs {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
        (ringCarrier i).base ∉ mmaWrites ins.op ∧ (ringCarrier i).waitBase ∉ mmaWrites ins.op := by
      have h := checkedPairCode i hLo hHi hc
      simp only [pairCode, hs, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
      exact h.1.1
    exact ⟨stage, (mmaStepReg (by omega) hHi (fun _ hc => (regs hc).1) hStep).trans hb,
      (mmaStepReg (by omega) hHi (fun _ hc => (regs hc).2) hStep).trans hw⟩
  have fall {ins : Instr} (hc : kernel.code[s.pc]? = some ins) (hu : u.pc = s.pc + 1) :
      pollPairBand i s.pc ∨ s.pc = (ringCarrier i).calcPc := by
    have h := checkedPairCode i hLo hHi hc
    rw [hu] at hBand
    simp only [pairCode, Bool.and_eq_true, hBand, decide_true, Bool.not_true,
      Bool.false_or, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact h.1.2
  rcases hStep with ⟨_, hTau⟩ | ⟨ev, _, hEvent⟩
  · have ht : Tau kernel [] l g s u := by
      unfold Tau at hTau ⊢
      rwa [← out_eq_core (by omega) hHi]
    by_cases hCalc : s.pc = (ringCarrier i).calcPc
    · exact ringCarrierReadyStep hp i hCalc hF ht
    obtain ⟨ins, hc⟩ := tau_core_has_code ht
    have h := checkedPairCode i hLo hHi hc
    simp only [pairCode, Bool.and_eq_true] at h
    rcases tau_core_frame hc ht with rfl | hFrame
    · exact keep ((fall hc rfl).resolve_right hCalc)
    have hu := hFrame.pc
    cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hu
    case bra target uni =>
      rw [hu] at hBand
      apply keep
      simpa only [hop, hBand, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
        using h.2
    case brx => simp [hop] at h
    all_goals exact keep ((fall hc hu).resolve_right hCalc)
  · obtain ⟨ins, hc, hl, _⟩ := estep_event_source hEvent
    have hCalc : s.pc ≠ (ringCarrier i).calcPc := by
      intro h
      rw [h, ringCarrierCalcCode i] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hl
    have hE : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm, hOut, hF⟩ := hEvent
      exact ⟨tm, by rwa [← out_eq_core (by omega) hHi], hF⟩
    rcases (estep_return_pc hE (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact keep (h ▸ hBand)
    · exact keep ((fall hc h).resolve_right hCalc)


private def afterReadyBand (i : Fin 3) (pc : Nat) : Prop :=
  (pairWait i).pc + 3 ≤ pc ∧ pc ≤ (pairCommit i).pc

private instance (i : Fin 3) (pc : Nat) : Decidable (afterReadyBand i pc) :=
  inferInstanceAs (Decidable ((pairWait i).pc + 3 ≤ pc ∧ pc ≤ (pairCommit i).pc))

private def carryingReady (i : Fin 3) (s : TState) : Prop :=
  afterReadyBand i s.pc ∨
    s.pc = (pairWait i).pc + 1 ∧ s.regs (pairWait i).result = some (.pred true)

private def carrierCode (i : Fin 3) (pc : Nat) (ins : Instr) : Bool :=
  (!decide ((pairWait i).pc ≤ pc ∧ pc ≤ (pairCommit i).pc) ||
    !(mmaWrites ins.op).contains (ringCarrier i).base) &&
  (!decide (afterReadyBand i (pc + 1)) || decide (afterReadyBand i pc) ||
    (pc == (pairWait i).pc + 2 && ins.guard.isNone && match ins.op with
      | .bra .. => true
      | _ => false)) &&
  match ins.op with
  | .bra target _ => target != (pairWait i).pc + 1 &&
      (!decide (afterReadyBand i target) || decide (afterReadyBand i pc) ||
        pc == (pairWait i).pc + 1)
  | .brx .. => false
  | _ => true

private theorem checkedCarrier (i : Fin 3) {pc : Nat} {ins : Instr}
    (hLo : 1907 ≤ pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some ins) :
    carrierCode i pc ins = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have hAll : code.all (fun ins => carrierCode i ins.2 ins.1) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  apply List.all_eq_true.mp hAll (ins, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem pairWaitCode (i : Fin 3) :
    let w := pairWait i
    kernel.code[w.pc]? = some ⟨none, .mbarWait w.result w.base 0 (.reg w.phase) true .cta⟩ ∧
    kernel.code[w.pc + 1]? = some ⟨some (w.result, false), .bra (w.pc + 3) w.uniform⟩ := by
  fin_cases i
  · exact ⟨Flow.code_2294, Flow.code_2295⟩
  · exact ⟨Flow.code_2352, Flow.code_2353⟩
  · exact ⟨Flow.code_2545, Flow.code_2546⟩

private theorem carrierKeeps {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (i : Fin 3) (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hLives : (pairWait i).pc ≤ s.pc ∧ s.pc ≤ (pairCommit i).pc)
    (hStep : WStep kernel Assumptions.all l g s e u) :
    u.regs (ringCarrier i).base = s.regs (ringCarrier i).base := by
  apply mmaStepReg (by omega) hHi _ hStep
  intro ins hc
  have h := checkedCarrier i hLo hHi hc
  have hLive := decide_eq_true hLives
  simp only [carrierCode, hLive, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  exact h.1.1

private theorem carryingWindow (i : Fin 3) {s : TState} (h : carryingReady i s) :
    (pairWait i).pc ≤ s.pc ∧ s.pc ≤ (pairCommit i).pc := by
  have bounds : (pairWait i).pc + 3 ≤ (pairCommit i).pc := by fin_cases i <;> decide
  rcases h with ⟨hl, hh⟩ | ⟨hp, _⟩ <;> omega

private theorem carriesFromTau (i : Fin 3) {l : Launch} {g : Nat} {s u : TState}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768) (hTau : Tau kernel Assumptions.all l g s u)
    (hu : carryingReady i u) : carryingReady i s := by
  have ht : Tau kernel [] l g s u := by
    unfold Tau at hTau ⊢
    rwa [← out_eq_core (by omega) hHi]
  obtain ⟨ins, hc, hf, hSrc⟩ := Softmax.tauScoreSource hTau
  have hWait : s.pc ≠ (pairWait i).pc := by
    intro he
    have h := (pairWaitCode i).1
    rw [← he] at h
    exact tau_core_not_event h rfl ht
  have hCode := checkedCarrier i hLo hHi hc
  simp only [carrierCode, Bool.and_eq_true] at hCode
  have fall (hNext : u.pc = s.pc + 1)
      (hFall : (s.pc == (pairWait i).pc + 2 &&
        ins.guard.isNone && match ins.op with | .bra .. => true | _ => false) = false) :
      carryingReady i s := by
    rcases hu with hBand | ⟨hp, _⟩
    · rw [hNext] at hBand
      have h := hCode.1.2
      simp only [hBand, hFall, decide_true, Bool.not_true, Bool.false_or, Bool.or_false,
        decide_eq_true_eq] at h
      exact .inl h
    · exact (hWait (by omega)).elim
  rcases hSrc with ⟨rfl, hFalse⟩ | ⟨hGuard, _, hExec⟩
  · apply fall rfl
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.and_eq_true] at h
    have hn := Option.isNone_iff_eq_none.mp h.1.2
    simp [hn, guardHolds, pure, Except.pure] at hFalse
  · have hFrame : LocalFrame ins.op s u := by
      rcases Softmax.scoreExecLocal hExec with h | ⟨_, hv, _, _⟩
      · exact h
      · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hv
        omega
    have hNext := hFrame.pc
    cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
    case bra target uni =>
      have hInfo := hCode.2
      simp only [hop, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        bne_iff_ne, beq_iff_eq] at hInfo
      rcases hu with hBand | ⟨hPc, _⟩
      · rw [hNext] at hBand
        rcases hInfo.2 with (hOutside | hInside) | hBranch
        · simp [hBand] at hOutside
        · exact .inl hInside
        · right
          refine ⟨hBranch, ?_⟩
          rw [hBranch, (pairWaitCode i).2] at hc
          obtain rfl := Option.some.inj hc.symm
          simp only [guardHolds, readReg, bind, Except.bind, pure, Except.pure] at hGuard
          cases hh : s.regs (pairWait i).result with
          | none => simp [hh, throw, throwThe, MonadExceptOf.throw] at hGuard
          | some v =>
            cases v <;> simp_all [throw, throwThe, MonadExceptOf.throw]
      · exact (hInfo.1 (hNext.symm.trans hPc)).elim
    case brx => simp [hop] at hCode
    all_goals exact fall hNext (by simp [hop])


private theorem carriesFromEvent {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (i : Fin 3) {g : Nat} {s u : TState} {e : Event} (hLo : 1907 ≤ s.pc)
    (hHi : s.pc < 2768) (hPair : pairedWords l i s)
    (he : EStep kernel Assumptions.all l g s e (some u)) (hu : carryingReady i u) :
    (carryingReady i s ∧ u.regs (ringCarrier i).base = s.regs (ringCarrier i).base ∧
      readyAtSite (recurringRelease i) e = false) ∨
      ∃ (stage : Fin 3) (parity : Nat),
        e = ⟨(pairWait i).pc, .wait (initObject l (g / l.block) (readySlot stage))
          parity true true .cta⟩ ∧
        u.regs (ringCarrier i).base = some (b32 (l.sharedBase + 8 * stage.val)) := by
  let w := pairWait i
  obtain ⟨ins, hc, hl, hFire⟩ := estep_event_source he
  have he' : EStep kernel [] l g s e (some u) := by
    obtain ⟨tm, hout, hf⟩ := he
    exact ⟨tm, by rwa [← out_eq_core (by omega) hHi], hf⟩
  by_cases hWait : s.pc = w.pc
  · right
    change s.pc = (pairWait i).pc at hWait
    obtain ⟨stage, hb, hr⟩ := hPair ⟨hWait.ge, by rw [hWait]; omega⟩
    have hLoc : mbarLoc l g s w.base 0 =
        .ok (initObject l (g / l.block) (readySlot stage)) := by
      have hAt : s.regs w.base = some (b32 (l.sharedBase + (8 * stage.val + 32))) :=
        (carrierGeometry i).2.1 ▸ hr
      have hOff : initializedMbarOffset (8 * stage.val + 32 + 0) := by
        fin_cases stage <;> unfold initializedMbarOffset <;> decide
      simpa [readySlot_address, Nat.add_assoc] using decodedMbarOffset hp (g := g) hAt hOff
    obtain ⟨ins', hCode, _, hFire'⟩ := estep_event_source he'
    rw [hWait, (pairWaitCode i).1] at hCode
    obtain rfl := Option.some.inj hCode.symm
    change Fires s.pc (eventTmpl [] l g s
      (.mbarWait w.result w.base 0 (.reg w.phase) true .cta)) e (some u) at hFire'
    simp only [eventTmpl, tmaTmpl, widenMbarScope, List.any_nil, Bool.false_eq_true,
      ↓reduceIte, hLoc, bind, Except.bind, pure, Except.pure] at hFire'
    cases hQ : readBits l g s 32 (.reg w.phase) with
    | error f => simp [hQ, ofExec, Fires] at hFire'
    | ok q =>
      simp only [hQ, ofExec, Fires] at hFire'
      obtain ⟨ok, rfl, hNext⟩ := hFire'
      obtain rfl := Option.some.inj hNext
      have hReg := carrierKeeps i hLo hHi (by rw [hWait]; fin_cases i <;> decide)
        (.inr ⟨_, rfl, he⟩)
      have hPc : (next (setReg s w.result (.pred ok))).pc = w.pc + 1 :=
        congrArg (· + 1) hWait
      have hTrue : ok = true := by
        rcases hu with hBand | ⟨_, hPred⟩
        · have hL := hBand.1
          rw [hPc] at hL
          change w.pc + 3 ≤ w.pc + 1 at hL
          omega
        · simpa [next, setReg, w] using hPred
      exact ⟨stage, q.toNat % 2, by rw [hWait, hTrue], hReg.trans hb⟩
  · left
    have hBranch : s.pc ≠ w.pc + 1 := by
      intro h
      rw [h, (pairWaitCode i).2] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hl
    have hCode := checkedCarrier i hLo hHi hc
    simp only [carrierCode, Bool.and_eq_true] at hCode
    have hOld : carryingReady i s := by
      rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with hh | hh
      · rcases hu with hBand | ⟨hPc, _⟩
        · exact .inl (hh ▸ hBand)
        · exact (hBranch (hh.symm.trans hPc)).elim
      · rcases hu with hBand | ⟨hPc, _⟩
        · rw [hh] at hBand
          have hFall :
              (s.pc == w.pc + 2 && ins.guard.isNone && match ins.op with
                | .bra .. => true
                | _ => false) = false := by
            cases hOp : ins.op <;> simp only [hOp, Op.isLocal] at hl
            case bra => cases hl
            all_goals simp
          have h := hCode.1.2
          simp only [hBand, hFall, decide_true, Bool.not_true, Bool.false_or, Bool.or_false,
            decide_eq_true_eq, w] at h
          exact .inl h
        · change u.pc = w.pc + 1 at hPc
          exact (hWait (by omega)).elim
    have hReg := carrierKeeps i hLo hHi (carryingWindow i hOld) (.inr ⟨_, rfl, he⟩)
    have hPc : e.pc ≠ w.pc := (estep_source_pc he).trans_ne hWait
    refine ⟨hOld, hReg, ?_⟩
    cases e with
    | mk pc k =>
      cases k <;> try rfl
      case wait _ _ ok _ _ =>
        change pc ≠ (slotWait (recurringRelease i)).pc at hPc
        cases ok
        · rfl
        · exact beq_eq_false_iff_ne.mpr hPc


private def heldReady (l : Launch) (i : Fin 3) (g : Nat) (pre : List Event) (s : TState) :
    Prop :=
  carryingReady i s → ∃ (j : Nat) (stage : Fin 3) (parity : Nat),
    pre[j]? = some ⟨(pairWait i).pc, .wait (initObject l (g / l.block) (readySlot stage))
      parity true true .cta⟩ ∧
    pre.countP (readyAtSite (recurringRelease i)) =
      (pre.take j).countP (readyAtSite (recurringRelease i)) + 1 ∧
    s.regs (ringCarrier i).base = some (b32 (l.sharedBase + 8 * stage.val))

private theorem heldReadyEvent {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : Fin 3) {g : Nat} {s u : TState} {e : Event} {pre : List Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768) (hPair : pairedWords l i s)
    (hHeld : heldReady l i g pre s) (he : EStep kernel Assumptions.all l g s e (some u)) :
    heldReady l i g (pre ++ [e]) u := by
  intro hU
  rcases carriesFromEvent hp i hLo hHi hPair he hU with
    ⟨hOld, hReg, hMark⟩ | ⟨stage, parity, hEvent, hAddr⟩
  · obtain ⟨j, stage, parity, he', hCount, hAddr⟩ := hHeld hOld
    have hj := (List.getElem?_eq_some_iff.mp he').1
    refine ⟨j, stage, parity, ?_, ?_, hReg.trans hAddr⟩
    · rw [List.getElem?_append_left hj]
      exact he'
    · rw [List.take_append_of_le_length hj.le, List.countP_append, List.countP_singleton]
      simp [hMark, hCount]
  · refine ⟨pre.length, stage, parity, ?_, ?_, hAddr⟩
    · rw [List.getElem?_append_right le_rfl]
      simp [hEvent]
    · rw [List.take_append_length, List.countP_append, List.countP_singleton]
      simp [hEvent, readyAtSite, pairWait]

private theorem pairCommitCode (i : Fin 3) :
    let c := ringCarrier i
    kernel.code[c.releasePc]? = some ⟨none, .tcCommit .one c.base 56 none⟩ := by
  fin_cases i
  · exact Flow.code_2462
  · exact Flow.code_2523
  · exact Flow.code_2638

private theorem targetFromCarrier {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : Fin 3) {g : Nat} (hg : g < l.threads) {s : TState} {o : Option TState}
    {spec : TcCommit.Spec} {rank : Fin 16} {target : Loc} {stage : Fin 3}
    (hAddr : s.regs (ringCarrier i).base = some (b32 (l.sharedBase + 8 * stage.val)))
    (he : EStep kernel Assumptions.all l g s ⟨(pairCommit i).pc, .tc (.commit spec)⟩ o)
    (hTarget : TcCommit.target spec rank = some target) :
    target = initObject l (g / l.block) (emptySlot stage) := by
  have hPc : s.pc = (ringCarrier i).releasePc :=
    (estep_source_pc he).symm.trans (carrierGeometry i).2.2.1.symm
  obtain ⟨tmp, ho, hF⟩ := he
  rcases out_ev ho with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · have h := congrArg Event.kind hF.1
    cases h
  rw [hPc, pairCommitCode i] at hc
  obtain rfl := Option.some.inj hc.symm
  have hOff : initializedMbarOffset (8 * stage.val + 56) := by
    fin_cases stage <;> unfold initializedMbarOffset <;> decide
  have h := commitExactAddress hp hg hAddr hOff hF rfl hTarget
  simpa [emptySlot_address, Nat.add_assoc] using h

private theorem matchedReleaseInWalk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : Fin 3) {g : Nat} (hg : g < l.threads) {s : TState} {es pre : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hFrame : RingAddressFrame l s) (hPair : pairedWords l i s) (hHeld : heldReady l i g pre s)
    {index : Nat} {spec : TcCommit.Spec} {rank : Fin 16} {target : Loc}
    (he : es[index]? = some ⟨(pairCommit i).pc, .tc (.commit spec)⟩)
    (hTarget : TcCommit.target spec rank = some target) :
    let past := pre ++ es.take index
    ∃ (j : Nat) (stage : Fin 3) (parity : Nat),
      target = initObject l (g / l.block) (emptySlot stage) ∧
      past[j]? = some ⟨(pairWait i).pc, .wait (initObject l (g / l.block) (readySlot stage))
        parity true true .cta⟩ ∧
      past.countP (readyAtSite (recurringRelease i)) =
        (past.take j).countP (readyAtSite (recurringRelease i)) + 1 := by
  dsimp only
  have hWindow : (pairWait i).pc + 3 ≤ (pairCommit i).pc ∧ (pairCommit i).pc < 2768 := by
    fin_cases i <;> decide
  have here {t : TState} {o : Option TState} {done : List Event}
      (hs : heldReady l i g done t)
      (hStep : EStep kernel Assumptions.all l g t ⟨(pairCommit i).pc, .tc (.commit spec)⟩ o) :
      ∃ (j : Nat) (stage : Fin 3) (parity : Nat),
        target = initObject l (g / l.block) (emptySlot stage) ∧
        done[j]? = some ⟨(pairWait i).pc, .wait (initObject l (g / l.block) (readySlot stage))
          parity true true .cta⟩ ∧
        done.countP (readyAtSite (recurringRelease i)) =
          (done.take j).countP (readyAtSite (recurringRelease i)) + 1 := by
    have hCurrent := (estep_source_pc hStep).symm
    change t.pc = (pairCommit i).pc at hCurrent
    obtain ⟨j, stage, parity, hGet, hCount, hAddr⟩ :=
      hs (.inl ⟨hWindow.1.trans_eq hCurrent.symm, hCurrent.le⟩)
    exact ⟨j, stage, parity, targetFromCarrier hp i hg hAddr hStep hTarget, hGet, hCount⟩
  have leave {t : TState} {events : List Event} {visits : List Visit}
      (hP : t.pc = 3099 ∧ t.fault = none) (hr : RingAddressFrame l t)
      (hW : Walk kernel Assumptions.all l g t events visits)
      (hMem : ⟨(pairCommit i).pc, .tc (.commit spec)⟩ ∈ events) : False := by
    have h := mmaEpilogueExitEvents hP.1 hP.2 (.inl rfl) hr.2.1 hW _ hMem
    change (pairCommit i).pc = 9205 at h
    omega
  induction hw generalizing index pre with
  | stop => simp at he
  | @tau t u events visits ht hW ih =>
    have hs : WStep kernel Assumptions.all l g _ none _ := .inl ⟨rfl, ht⟩
    obtain ⟨hScope | hExit, hF⟩ := ringFrameStep hp hPc.1 hPc.2 hFrame hs
    · have hHeld' : heldReady l i g pre u := by
        intro hu
        have hs' := carriesFromTau i hPc.1 hPc.2 ht hu
        obtain ⟨j, stage, parity, hGet, hCount, hAddr⟩ := hHeld hs'
        exact ⟨j, stage, parity, hGet, hCount,
          (carrierKeeps i hPc.1 hPc.2 (carryingWindow i hs') hs).trans hAddr⟩
      exact ih hScope hF (pairStep hp i hPc.1 hPc.2 hFrame hPair hs) hHeld' he
    · exact (leave hExit hF hW (List.mem_of_getElem? he)).elim
  | @ev t u first rest next hE hW ih =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      simpa only [List.take_zero, List.append_nil] using here hHeld hE
    | succ index =>
      have ht : rest[index]? = some ⟨(pairCommit i).pc, .tc (.commit spec)⟩ := he
      have hs : WStep kernel Assumptions.all l g t (some first) u := .inr ⟨_, rfl, hE⟩
      obtain ⟨hScope | hExit, hF⟩ := ringFrameStep hp hPc.1 hPc.2 hFrame hs
      · have h := ih hScope hF (pairStep hp i hPc.1 hPc.2 hFrame hPair hs)
          (heldReadyEvent hp i hPc.1 hPc.2 hPair hHeld hE) ht
        simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using h
      · exact (leave hExit hF hW (List.mem_of_getElem? ht)).elim
  | last hE =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj he
      simpa only [List.take_zero, List.append_nil] using here hHeld hE
    | succ index => simp at he


/-- Every recurring release returns the physical slot observed by its own precise ready
occurrence. The occurrence agrees with the immediately preceding release election. -/
theorem recurringReleaseMatchesReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (i : Fin 3)
    {g index : Nat} {spec : TcCommit.Spec} {rank : Fin 16} {target : Loc}
    (he : X.get (g, index) = some ⟨(pairCommit i).pc, .tc (.commit spec)⟩)
    (hTarget : TcCommit.target spec rank = some target) :
    ∃ j < index, ∃ (stage : Fin 3) (parity : Nat),
      target = initObject l (g / l.block) (emptySlot stage) ∧
      X.get (g, j) = some ⟨(pairWait i).pc, .wait (initObject l (g / l.block) (readySlot stage))
        parity true true .cta⟩ ∧
      ((X.tr g).take j).countP (readyAtSite (recurringRelease i)) =
        ElectOrd.siteOrdinal (fun pc => pc == (slotElect (recurringRelease i)).pc) X g (index - 1) ∧
      Resumes kernel X (g, j) (g, index) := by
  have hg : g < l.threads := event_thread_lt hX he
  obtain ⟨s, visits, _, hIndex, _, ht, hw⟩ := releaseBody hp hX he
    (show 2145 ≤ (pairCommit i).pc by fin_cases i <;> decide)
    (show (pairCommit i).pc < 2768 by fin_cases i <;> decide)
  have hPaired : pairedWords l i s := by
    intro h
    rw [ht.1] at h
    exfalso
    exact (show ¬ pollPairBand i 1908 by fin_cases i <;> decide) h
  have hHeld : heldReady l i g ((X.tr g).take 6) s := by
    intro h
    have hl := (carryingWindow i h).1
    rw [ht.1] at hl
    exact ((show ¬ (pairWait i).pc ≤ 1908 by fin_cases i <;> decide) hl).elim
  have hGet : ((X.tr g).drop 6)[index - 6]? = some ⟨(pairCommit i).pc, .tc (.commit spec)⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  obtain ⟨j, stage, parity, hLoc, hPoll, hCount⟩ :=
    matchedReleaseInWalk hp i hg hw (by rw [ht.1]; decide)
      (ringFrameAtEntry ht) hPaired hHeld hGet hTarget
  have hTake : (X.tr g).take index =
      (X.tr g).take 6 ++ ((X.tr g).drop 6).take (index - 6) := by
    conv_lhs => rw [← Nat.add_sub_of_le hIndex, List.take_add]
  rw [← hTake] at hPoll hCount
  have hj := (List.getElem?_eq_some_iff.mp hPoll).1
  have hLen : j < index := by rw [List.length_take] at hj; omega
  rw [List.getElem?_take_of_lt hLen] at hPoll
  have hCount' : (((X.tr g).take index).take j) = (X.tr g).take j := by
    rw [List.take_take, Nat.min_eq_left hLen.le]
  rw [hCount'] at hCount
  obtain ⟨hRelease, inst, lead, hE⟩ := readyReleaseElection hp hX (recurringRelease i) he
  change X.Elect (g, index - 1) (slotElect (recurringRelease i)).pc (2 ^ 32 - 1) inst lead at hE
  have hBalance := releaseElectionBalance hp hX (recurringRelease i) hE
  have hEarlier : index - 1 + 1 = index := by omega
  have hElection : (X.tr g)[index - 1]? =
      some ⟨(slotElect (recurringRelease i)).pc, .elect (2 ^ 32 - 1) inst lead⟩ := hE
  have hPrefix : ((X.tr g).take index).countP (readyAtSite (recurringRelease i)) =
      ((X.tr g).take (index - 1)).countP (readyAtSite (recurringRelease i)) := by
    conv_lhs => rw [← hEarlier, List.take_add_one, hElection]
    simp [List.countP_append, readyAtSite]
  rw [hPrefix, hBalance] at hCount
  have hOrdinal : ((X.tr g).take j).countP (readyAtSite (recurringRelease i)) =
      ElectOrd.siteOrdinal (fun pc => pc == (slotElect (recurringRelease i)).pc) X g
        (index - 1) := by omega
  have hWait : X.get (g, j) = some ⟨(pairWait i).pc,
      .wait (initObject l (g / l.block) (readySlot stage)) parity true true .cta⟩ := hPoll
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hWait
  have hBefore : TraceBefore X (g, j) (g, index) :=
    ⟨rfl, hLen, (List.getElem?_eq_some_iff.mp he).1⟩
  refine ⟨j, hLen, stage, parity, hLoc, hWait, hOrdinal, hBefore, ?_⟩
  simp only [hWait, Option.map_some, Kind.resume]
  exact ⟨_, exit, _, parity, true, .cta, hWait, hSpin, hBefore⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxStartup
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.Next
public import Lemmas.Flow.TauFrame
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

private def bootRegs : List Nat := [1062, 2535, 7502, 7503, 7506]

private def bootLocalOp (op : Op) : Bool :=
  op.isLocal && (match op with
    | .brx .. => false
    | .bra q _ => decide (36 ≤ q ∧ q ≤ 172)
    | _ => true)

private def bootElectOp : WarpInstr → Bool
  | ⟨.elect, _, [_, some _], [], some _⟩ => true
  | _ => false

private def bootEventOp : Op → Bool
  | .mbarInit .. => true
  | .warp w => bootElectOp w
  | _ => false

private def bootOp (op : Op) : Bool :=
  (bootLocalOp op || bootEventOp op) &&
    bootRegs.all fun r => !(writesRegs op).contains r

set_option maxRecDepth 10000 in
private theorem bootTable : ((kernel.code.drop 36).take 136).all (bootOp ·.op) = true := by
  kernel_rfl

private theorem bootAt {pc : Nat} {ins : Instr} (hl : 36 ≤ pc) (hh : pc < 172)
    (hc : kernel.code[pc]? = some ins) : bootOp ins.op = true := by
  apply (List.all_eq_true.mp bootTable) ins
  apply List.mem_of_getElem? (i := pc - 36)
  rw [List.getElem?_take, ite_eq_left (show pc - 36 < 136 by omega), List.getElem?_drop]
  rw [show 36 + (pc - 36) = pc by omega]
  exact hc

private theorem bootWrites {op : Op} (h : bootOp op = true) {r : Nat} (hr : r ∈ bootRegs) :
    r ∉ writesRegs op := by
  have hf := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 r hr)
  simpa using hf

private theorem bootPc {op : Op} (h : bootOp op = true) {pc q : Nat}
    (hl : 36 ≤ pc) (hh : pc < 172) (hq : q = nextPc op pc ∨ BrxTarget op q) :
    36 ≤ q ∧ q ≤ 172 := by
  have hOp := (Bool.and_eq_true_iff.mp h).1
  cases op <;> simp only [nextPc, BrxTarget, or_false] at hq
  case bra target uni =>
    subst q
    exact of_decide_eq_true (by simpa [bootLocalOp, bootEventOp, Op.isLocal] using hOp)
  case brx => cases hOp
  all_goals subst q; omega

private def bootFrame (p : Params) (l : Launch) (t : TState) : Prop :=
  36 ≤ t.pc ∧ t.pc ≤ 172 ∧ t.fault = none ∧ t.sub = 0 ∧ t.acc = [] ∧
    Holds t.regs (dispatchInput p l 0)

private theorem bootHolds {p : Params} {l : Launch} {t u : TState}
    (h : Holds t.regs (dispatchInput p l 0)) (hr : ∀ r ∈ bootRegs, u.regs r = t.regs r) :
    Holds u.regs (dispatchInput p l 0) :=
  ⟨(hr 1062 (by decide)).trans h.1, (hr 2535 (by decide)).trans h.2.1,
    (hr 7502 (by decide)).trans h.2.2.1, (hr 7503 (by decide)).trans h.2.2.2.1,
    (hr 7506 (by decide)).trans h.2.2.2.2.1, trivial⟩

private theorem bootLocal {p : Params} {l : Launch} {g : Nat} {t u : TState}
    (h : bootFrame p l t) (ht : Tau kernel Assumptions.all l g t u) : bootFrame p l u := by
  obtain ⟨hl, hh, hf, hs, ha, hr⟩ := h
  have hCore : Tau kernel [] l g t u := by
    rw [Tau, StartupAgreement.out_eq (A := Assumptions.all) (.inl (by omega))] at ht
    exact ht
  have hLt : t.pc < 172 := by
    by_contra hNot
    have hEq : t.pc = 172 := by omega
    exact tau_core_not_event (hEq ▸ Flow.code_172) rfl hCore
  obtain ⟨ins, hc⟩ := tau_core_has_code hCore
  rcases tau_core_frame hc hCore with rfl | hF
  · have hPc : (skip t).pc = t.pc + 1 := rfl
    exact ⟨by omega, by omega, hf, rfl, rfl, hr⟩
  · obtain ⟨hL, hH⟩ := bootPc (bootAt hl hLt hc) hl hLt hF.pc
    exact ⟨hL, hH, hF.fault.trans hf, hF.sub.trans hs, hF.acc.trans ha,
      bootHolds hr fun r hR => hF.regs r (bootWrites (bootAt hl hLt hc) hR)⟩

private theorem bootLocalStar {p : Params} {l : Launch} {g : Nat} {t u : TState}
    (h : bootFrame p l t) (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    bootFrame p l u := by
  induction ht with
  | refl => exact h
  | tail _ hLast ih => exact bootLocal ih hLast

private theorem bootNonlocal {op : Op} (h : bootOp op = true) (hl : op.isLocal = false) :
    (∃ b off count, op = .mbarInit b off count) ∨
      ∃ ty d p mask, op = .warp ⟨.elect, ty, [d, some p], [], some mask⟩ := by
  have hLocal : bootLocalOp op = false := by unfold bootLocalOp; rw [hl]; rfl
  have hOp : bootEventOp op = true := by
    simpa only [hLocal, Bool.false_or] using (Bool.and_eq_true_iff.mp h).1
  clear h hl hLocal
  cases op <;> simp only [bootEventOp] at hOp
  case mbarInit => exact .inl ⟨_, _, _, rfl⟩
  case warp w =>
    unfold bootElectOp at hOp
    split at hOp
    · exact .inr ⟨_, _, _, _, rfl⟩
    · cases hOp
  all_goals cases hOp

variable {p : Params} {l : Launch}

private theorem bootEvent {g : Nat} {t u : TState} {e : Event} (h : bootFrame p l t)
    (hh : t.pc < 172) (he : EStep kernel Assumptions.all l g t e (some u)) : bootFrame p l u := by
  obtain ⟨hl, _, hf, hs, ha, hr⟩ := h
  obtain ⟨ins, hc, hLoc, hFire⟩ := PTX.EventFrame.estep_event_source he
  have hOp := bootAt hl hh hc
  rcases bootNonlocal hOp hLoc with ⟨_, _, _, hM⟩ | ⟨ty, dst, pred, mask, hE⟩
  · rw [hM] at hFire
    have hu := fires_next (show AdvancesOp (.mbarInit _ _ _) from trivial) hFire
    subst u
    have hPc : (next t).pc = t.pc + 1 := rfl
    exact ⟨by omega, by omega, hf, hs, ha, hr⟩
  · rw [hE] at hFire
    obtain ⟨_, _, leader, _, rfl⟩ := fires_elect hFire
    have hP (r : Nat) (hr : r ∈ bootRegs) : r ≠ pred := by
      rintro rfl
      apply bootWrites hOp hr
      rw [hE]
      cases dst <;> simp [writesRegs]
    have hD (r : Nat) (hr : r ∈ bootRegs) (d : Nat) (hd : dst = some d) : r ≠ d := by
      rintro rfl
      apply bootWrites hOp hr
      rw [hE, hd]
      simp [writesRegs]
    refine ⟨?_, ?_, ?_, ?_, ?_, bootHolds hr ?_⟩
    · cases dst <;> change 36 ≤ t.pc + 1 <;> omega
    · cases dst <;> change t.pc + 1 ≤ 172 <;> omega
    · cases dst <;> exact hf
    · cases dst <;> exact hs
    · cases dst <;> exact ha
    · intro r hR
      cases hDst : dst with
      | none => simp [next, setReg, hP r hR]
      | some d => simp [next, setReg, hP r hR, hD r hR d hDst]

private theorem bootBroadcastPrefix {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 0) (hLength : 3 ≤ (X.tr g).length) :
    ∃ t o, bootFrame p l t ∧ Run kernel Assumptions.all l g t ((X.tr g).drop 3) o ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take 3) (some t) := by
  have h0 : 0 < (X.tr g).length := by omega
  have h1 : 1 < (X.tr g).length := by omega
  have h2 : 2 < (X.tr g).length := by omega
  let e0 := (X.tr g)[0]
  let e1 := (X.tr g)[1]
  let e2 := (X.tr g)[2]
  have hTrace : X.tr g = e0 :: e1 :: e2 :: (X.tr g).drop 3 := by
    have ha := List.drop_eq_getElem_cons h0
    have hb := List.drop_eq_getElem_cons h1
    have hc := List.drop_eq_getElem_cons h2
    rw [hc] at hb
    rw [hb] at ha
    exact ha
  obtain ⟨t, o, hPc, hFault, hBase, hIndex, _, hAbi, hSub, hAcc, hRun, hPast⟩ :=
    broadcastPrefixRun hp hX g hg hTrace
  have hFacts : Holds t.regs (dispatchInput p l 0) := by
    rw [hw] at hIndex
    refine ⟨hIndex, hBase, ?_, ?_, ?_, trivial⟩
    all_goals exact holds_mem hAbi (by simp [abiFacts])
  refine ⟨t, o, ⟨by omega, by omega, hFault, hSub, hAcc, hFacts⟩, hRun, ?_⟩
  rwa [hTrace]

private theorem bootFenceNext {g : Nat} {t : TState} (ht : At t 172 (dispatchInput p l 0)) :
    Next kernel Assumptions.all l g t t (.fenceMbarInit (next t)) := by
  have hFenceOut : out kernel [] l g t = .ev (.fenceMbarInit (next t)) := by
    unfold out
    rw [ht.1, ht.2.2.2.1, Flow.code_172]
    rfl
  exact ⟨.refl, startupOut (.inl (by rw [ht.1]; decide)) hFenceOut⟩

private theorem bootCTANext {g : Nat} {t : TState} (ht : At t 172 (dispatchInput p l 0)) :
    Next kernel Assumptions.all l g (next t) (next t)
      (.bar 0 (next (next t)) none .sync) := by
  have hPc : (next t).pc = 173 := ht.next.1
  have hBarOut : out kernel [] l g (next t) = .ev (.bar 0 (next (next t)) none .sync) := by
    unfold out
    rw [hPc, ht.next.2.2.2.1, Flow.code_173]
    rfl
  exact ⟨.refl, startupOut (.inl (by rw [hPc]; decide)) hBarOut⟩

/-- The three common broadcasts are the only collective scan ordinals used before
the softmax scheduler. -/
def beforeFirstScan (X : Execution) (g n : Nat) : Prop :=
  ((X.tr g).take n).countP Execution.isShfl = 3 ∧
  ((X.tr g).take n).countP isFullWarpVote = 0

theorem beforeFirstScan_advance {X : Execution} {g n : Nat} {e : Event}
    (h : beforeFirstScan X g n) (he : X.get (g,n) = some e)
    (hShfl : Execution.isShfl e = false) (hVote : isFullWarpVote e = false) :
    beforeFirstScan X g (n+1) := by
  unfold beforeFirstScan
  rw [countP_take_succ_false he hShfl, countP_take_succ_false he hVote]
  exact h

theorem beforeFirstScan_three {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hLen : 3 ≤ (X.tr g).length) :
    beforeFirstScan X g 3 := by
  have takeEvent {n : Nat} {e : Event} (he : X.get (g,n) = some e) :
      (X.tr g).take (n+1) = (X.tr g).take n ++ [e] := by
    rw [List.take_add_one]
    change (X.tr g).take n ++ (X.get (g,n)).toList = _
    rw [he]
    rfl
  let e0 := (X.tr g)[0]'(by omega)
  let e1 := (X.tr g)[1]'(by omega)
  let e2 := (X.tr g)[2]'(by omega)
  have h0 : X.get (g,0) = some e0 := List.getElem?_eq_getElem (show 0 < (X.tr g).length by omega)
  have h1 : X.get (g,1) = some e1 := List.getElem?_eq_getElem (show 1 < (X.tr g).length by omega)
  have h2 : X.get (g,2) = some e2 := List.getElem?_eq_getElem (show 2 < (X.tr g).length by omega)
  unfold beforeFirstScan
  rw [takeEvent h2, takeEvent h1, takeEvent h0,
    firstSharedValue hp hX g hg h0, secondWarpValue hp hX g hg h1, thirdWarpValue hp hX g hg h2]
  exact ⟨rfl, rfl⟩

private theorem bootEventOrdinary {l : Launch} {g : Nat} {t u : TState} {e : Event}
    (hl : 36 ≤ t.pc) (hh : t.pc < 172)
    (he : EStep kernel Assumptions.all l g t e (some u)) :
    Execution.isShfl e = false ∧ isFullWarpVote e = false := by
  obtain ⟨ins, hc, hLoc, hf⟩ := PTX.EventFrame.estep_event_source he
  rcases bootNonlocal (bootAt hl hh hc) hLoc with ⟨base, off, count, hOp⟩ |
    ⟨ty, dst, pred, mask, hOp⟩
  · rw [hOp] at hf
    simp only [eventTmpl, tmaTmpl, bind, Except.bind] at hf
    repeat' split at hf
    all_goals first
      | have hKind : ∃ m n, e.kind = .mbInit m n := by
          exact ⟨_, _, congrArg Event.kind hf.1⟩
        obtain ⟨_, _, hKind⟩ := hKind
        cases e
        subst_vars
        exact ⟨rfl, rfl⟩
      | cases hf.2
  · rw [hOp] at hf
    obtain ⟨_, _, _, rfl, _⟩ := fires_elect hf
    exact ⟨rfl, rfl⟩

private theorem bootTakeEvent {l : Launch} {X : Execution} {g i : Nat} {t u v : TState}
    {e : Event} (hGet : X.get (g,i) = some e)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hStep : EStep kernel Assumptions.all l g u e (some v)) :
    Run kernel Assumptions.all l g {} ((X.tr g).take (i+1)) (some v) := by
  have hi : i < (X.tr g).length := len_of_get hGet
  rw [List.take_succ_eq_append_getElem hi, (List.getElem?_eq_some_iff.mp hGet).2]
  exact hPrefix.snoc hLocal hStep

private theorem bootFenceOfEvent {g : Nat} {X : Execution} {t : TState} {o : Option TState}
    {i j : Nat} {target : Event} (h : bootFrame p l t)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) o) (hIndex : i ≤ j)
    (he : X.get (g,j) = some target) (hLate : 173 < target.pc) (hCount : beforeFirstScan X g i)
    (hEarlier : EarlierEvents X g i 172)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some t)) :
    ∃ n s, i ≤ n ∧ n ≤ j ∧ beforeFirstScan X g n ∧ At s 172 (dispatchInput p l 0) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop n) o ∧ EarlierEvents X g n 172 ∧
      ∃ a, Run kernel Assumptions.all l g {} ((X.tr g).take n) (some a) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) a s := by
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  generalize hEs : (X.tr g).drop i = es at hRun
  induction hRun generalizing i with
  | nil =>
    have h := List.drop_eq_nil_iff.mp hEs
    omega
  | @step _ v u e tail o hLocal hEvent hTail ih =>
    have hv := bootLocalStar h hLocal
    by_cases hFence : v.pc = 172
    · exact ⟨i, v, le_rfl, hIndex, hCount,
        ⟨hFence, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.1, hv.2.2.2.2.2⟩,
        hEs.symm ▸ Run.step .refl hEvent hTail, hEarlier, _, hPrefix, hLocal⟩
    have hLt : v.pc < 172 := by have := hv.2.1; omega
    have hNext : i + 1 ≤ j := by
      by_contra! hj
      have hEq : i = j := by omega
      subst i
      have hGet : ((X.tr g).drop j).head? = some target := by
        rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero]
        exact he
      rw [hEs] at hGet
      obtain rfl := Option.some.inj hGet
      have hFrom := PTX.EventFrame.estep_source_pc hEvent
      omega
    have hDrop : (X.tr g).drop (i + 1) = tail := by
      rw [← List.drop_drop, hEs, List.drop_succ_cons, List.drop_zero]
    have hGet : X.get (g,i) = some e := by
      change (X.tr g)[i]? = _
      rw [← Nat.add_zero i, ← List.getElem?_drop, hEs, List.getElem?_cons_zero]
    obtain ⟨hShfl, hVote⟩ := bootEventOrdinary hv.1 hLt hEvent
    have hFrom := PTX.EventFrame.estep_source_pc hEvent
    have hEarlier' : EarlierEvents X g (i+1) 172 := by
      intro k hk other hOther
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hLt' | rfl
      · exact hEarlier k hLt' _ hOther
      · rw [Option.some.inj (hOther.symm.trans hGet), hFrom]
        exact hLt
    obtain ⟨n, s, hn, hj, hC, hs, hR, hE, hP⟩ := ih (bootEvent hv hLt hEvent) hNext
      (beforeFirstScan_advance hCount hGet hShfl hVote) hEarlier'
      (bootTakeEvent hGet hPrefix hLocal hEvent) hDrop
    exact ⟨n, s, by omega, hj, hC, hs, hR, hE, hP⟩
  | @last _ v e hLocal hEvent =>
    have hGet : ((X.tr g).drop i)[j-i]? = some target := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
      exact he
    rw [hEs] at hGet
    obtain rfl := List.mem_singleton.mp (List.mem_of_getElem? hGet)
    have hv := (bootLocalStar h hLocal).2.1
    have hFrom := PTX.EventFrame.estep_source_pc hEvent
    omega

/-- On a real warp-zero prefix, the initializer elections and CTA barrier preserve the
ABI arguments used by the scheduler. The cursor counts the actual initializer events. -/
theorem zeroDispatchPrefixOfEvent {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {target : Event}
    (he : X.get (g,j) = some target) (hLate : 173 < target.pc) (hZero : warpIndex l g = 0) :
    ∃ n u o, n ≤ j ∧ beforeFirstScan X g n ∧ At u 3101 (dispatchOutput p l g 0) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop n) o ∧ EarlierEvents X g n 174 ∧
      ∃ s, Run kernel Assumptions.all l g {} ((X.tr g).take n) (some s) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u := by
  have hg := event_thread_lt hX he
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hStart : 3 ≤ j := by
    by_contra! h
    interval_cases j
    · rw [firstSharedValue hp hX g hg he] at hLate
      exact (by decide : ¬ 173 < 25) hLate
    · rw [secondWarpValue hp hX g hg he] at hLate
      exact (by decide : ¬ 173 < 34) hLate
    · rw [thirdWarpValue hp hX g hg he] at hLate
      exact (by decide : ¬ 173 < 35) hLate
  obtain ⟨t, o, ht, hr, hPast⟩ := bootBroadcastPrefix hp hX (g := g) hg hZero (by omega)
  have hEarly : EarlierEvents X g 3 172 := by
    intro k hk e hGet
    interval_cases k
    · rw [firstSharedValue hp hX g hg hGet]
      change 25 < 172
      decide
    · rw [secondWarpValue hp hX g hg hGet]
      change 34 < 172
      decide
    · rw [thirdWarpValue hp hX g hg hGet]
      change 35 < 172
      decide
  obtain ⟨n, s, _, hn, hCount, hs, hRun, hEarlier, a, hBefore, hTau⟩ :=
    bootFenceOfEvent ht hr hStart he hLate (beforeFirstScan_three hp hX hg (by omega)) hEarly hPast
  have nonempty {n : Nat} (hn : n ≤ j) : (X.tr g).drop n ≠ [] := by
    intro h
    exact (Nat.not_le_of_lt hLen) ((List.drop_eq_nil_iff.mp h).trans hn)
  have inPast {n : Nat} {e : Event} (hn : n ≤ j) (hN : X.get (g,n) = some e)
      (hPc : e.pc ≤ 173) : n+1 ≤ j := by
    apply Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hn ?_)
    rintro rfl
    rw [hN] at he
    obtain rfl := Option.some.inj he
    omega
  obtain ⟨_, _, hF, ⟨rfl, hS⟩, hTail⟩ := (bootFenceNext hs).continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hRun (nonempty hn)
  obtain rfl := Option.some.inj hS
  have hNext := inPast hn hF (by simpa only [hs.1] using (by decide : 172 ≤ 173))
  obtain ⟨_, _, hB, ⟨rfl, hV⟩, hRest⟩ := (bootCTANext hs).continuing_at_nonempty (by
    rintro e ⟨_, hBad⟩
    cases hBad) hTail (nonempty hNext)
  obtain rfl := Option.some.inj hV
  have hPos : n+1+1 ≤ j := inPast hNext hB (by simpa only [hs.next.1] using Nat.le_refl 173)
  obtain ⟨u, hLocal, hu⟩ := dispatchRun hp g hg 0 _ hs.next.next
  have hCount := beforeFirstScan_advance (beforeFirstScan_advance hCount hF rfl rfl) hB rfl rfl
  have hFenceStep : EStep kernel Assumptions.all l g s ⟨s.pc, .fenceMbarInit⟩
      (some (next s)) := ⟨_, (bootFenceNext hs).stop, rfl, rfl⟩
  have hBarStep : EStep kernel Assumptions.all l g (next s) ⟨(next s).pc, .bar 0 none .sync⟩
      (some (next (next s))) := ⟨_, (bootCTANext hs).stop, rfl, rfl⟩
  have hBeforeRole : EarlierEvents X g (n+1+1) 174 :=
    (hEarlier.succ hF hs.1).succ hB hs.next.1
  exact ⟨_, u, o, hPos, hCount, hu, hRest.after_local_nonempty (run_rtg hLocal) (nonempty hPos),
    hBeforeRole, _, bootTakeEvent hB (bootTakeEvent hF hBefore hTau hFenceStep) .refl hBarStep,
    run_rtg hLocal⟩

/-- Warp zero's scheduler ABI state is already determined at the first role entry. -/
theorem zeroDispatchOfEvent {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {target : Event}
    (he : X.get (g,j) = some target) (hLate : 173 < target.pc) (hZero : warpIndex l g = 0) :
    ∃ n u o, n ≤ j ∧ beforeFirstScan X g n ∧ At u 3101 (dispatchOutput p l g 0) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop n) o := by
  obtain ⟨n, u, o, hi, hCount, hu, hTail, _⟩ := zeroDispatchPrefixOfEvent hp hX he hLate hZero
  exact ⟨n, u, o, hi, hCount, hu, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax

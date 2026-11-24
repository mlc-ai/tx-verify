-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
public import Lemmas.Order.ElectSiteOrdinal
public import Kernels.TmlFa4Fwd.Proof.MmaProbabilityCursor
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.CtaMemoryOrder
import Lemmas.Flow.ElectMask

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame AsyncCopy

noncomputable section

def slotWait (i : Fin 4) : WaitSite := waitSite (releaseWaitSite i)

def slotElect (i : Fin 4) : ElectSite :=
  electSite (commitElection (releaseCommitSite i))

def readyAtSite (i : Fin 4) (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => e.pc == (slotWait i).pc
  | _ => false

def releaseAtSite (i : Fin 4) : Event → Bool :=
  ElectOrd.atSites (fun pc => pc == (slotElect i).pc)

private def readyBalanceGate (i : Fin 4) : Fin 11 := ⟨i.val, by have := i.isLt; omega⟩

private def probabilityBalanceGate (i : Fin 4) : Fin 11 :=
  ⟨i.val + 4, by have := i.isLt; omega⟩

private def balanceWait (i : Fin 11) : WaitSite :=
  if hs : i.val < 4 then slotWait ⟨i.val, hs⟩
  else if hm : i.val < 8 then
    waitSite (probabilityWait ⟨i.val - 4, by omega⟩ false)
  else if i.val = 10 then slotWait 1 else slotWait 2

private def balanceElection (i : Fin 11) : Fin 20 :=
  if hs : i.val < 4 then commitElection (releaseCommitSite ⟨i.val, hs⟩)
  else if i.val = 10 then commitElection (releaseCommitSite 2)
  else if i.val < 6 ∨ i.val = 8 then commitElection (qkCommitSite 2)
  else commitElection (qkCommitSite 3)

private def balanceElect (i : Fin 11) : ElectSite := electSite (balanceElection i)

private def balancePollMark (i : Fin 11) (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => e.pc == (balanceWait i).pc
  | _ => false

private def balanceElectionMark (i : Fin 11) : Event → Bool :=
  ElectOrd.atSites (fun pc => pc == (balanceElect i).pc)

private def pendingBand (i : Fin 11) (pc : Nat) : Bool :=
  decide ((balanceWait i).pc + 2 < pc ∧ pc ≤ (balanceElect i).pc)

private def pending (i : Fin 11) (s : TState) : Bool :=
  pendingBand i s.pc ||
    (s.pc == (balanceWait i).pc + 1 && s.regs (balanceWait i).result == some (.pred true))

private theorem balanceWaitWindow (i : Fin 11) :
    2145 ≤ (balanceWait i).pc ∧ (balanceWait i).pc + 3 ≤ (balanceElect i).pc ∧
      (balanceElect i).pc + 1 < 2768 := by
  fin_cases i <;> decide

private theorem overlap {i : Fin 11} :
    pendingBand i ((balanceWait i).pc) = false ∧
    pendingBand i ((balanceWait i).pc + 1) = false ∧
    pendingBand i ((balanceWait i).pc + 2) = false ∧
    pendingBand i ((balanceWait i).pc + 3) = true ∧
    pendingBand i ((balanceElect i).pc) = true ∧
    pendingBand i ((balanceElect i).pc + 1) = false := by
  fin_cases i <;> decide

private theorem balanceSpinCode (i : Fin 11) :
    let w := balanceWait i
    kernel.code[w.pc]? = some ⟨none, .mbarWait w.result w.base 0 (.reg w.phase) true .cta⟩ ∧
    kernel.code[w.pc + 1]? = some ⟨some (w.result, false), .bra (w.pc + 3) w.uniform⟩ := by
  fin_cases i
  · exact ⟨Flow.code_2145, Flow.code_2146⟩
  · exact ⟨Flow.code_2294, Flow.code_2295⟩
  · exact ⟨Flow.code_2352, Flow.code_2353⟩
  · exact ⟨Flow.code_2545, Flow.code_2546⟩
  · exact ⟨Flow.code_2297, Flow.code_2298⟩
  · exact ⟨Flow.code_2335, Flow.code_2336⟩
  · exact ⟨Flow.code_2419, Flow.code_2420⟩
  · exact ⟨Flow.code_2450, Flow.code_2451⟩
  · exact ⟨Flow.code_2352, Flow.code_2353⟩
  · exact ⟨Flow.code_2352, Flow.code_2353⟩
  · exact ⟨Flow.code_2294, Flow.code_2295⟩

private def cleanEdge (i : Fin 11) (source target : Nat) : Bool :=
  (target != (balanceWait i).pc + 1) && (pendingBand i source == pendingBand i target)

private def neutralCode (i : Fin 11) (pc : Nat) (ins : Instr) : Bool :=
  ((ins.op.isLocal || linearEventOp ins.op) &&
  if pc == (balanceWait i).pc || pc == (balanceWait i).pc + 1 || pc == (balanceElect i).pc
  then true
  else (match ins.op with
    | .bra dest _ =>
      cleanEdge i pc dest && (ins.guard.isNone || cleanEdge i pc (pc + 1))
    | .brx .. => false
    | _ => cleanEdge i pc (pc + 1)))

private theorem checkedNeutral (i : Fin 11) {pc : Nat} {ins : Instr}
    (hLo : 1907 ≤ pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some ins) :
    neutralCode i pc ins = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have hCode : code.all (fun pair => neutralCode i pair.2 pair.1) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  apply List.all_eq_true.mp hCode (ins, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem cleanPending (i : Fin 11) {s u : TState}
    (hs : s.pc ≠ (balanceWait i).pc + 1) (hc : cleanEdge i s.pc u.pc = true) :
    pending i s = pending i u := by
  simp only [cleanEdge, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc
  simp only [pending, beq_eq_false_iff_ne.mpr hs, beq_eq_false_iff_ne.mpr hc.1,
    Bool.false_and, Bool.or_false, hc.2]

private theorem noFaultOfReturning {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) : s.fault = none := by
  cases h : s.fault
  · rfl
  · obtain ⟨tm, hOut, hf⟩ := he
    simp only [out, h, Out.ev.injEq] at hOut
    subst tm
    cases hf.2

private theorem expectation {s : TState} (i : Fin 11) (hs : RoleShape s)
    (hf : s.fault = none) (hp : s.pc = (balanceElect i).pc) : At s (balanceElect i).pc [] := by
  have h := balanceWaitWindow i
  exact ⟨hp, hs.2.2 (by omega), hs.2.1, hf, trivial⟩

private theorem afterPollBranch (i : Fin 11) {l : Launch} {g : Nat} {s u : TState}
    (hp : s.pc = (balanceWait i).pc + 1) (hf : s.fault = none)
    (ht : Tau kernel [] l g s u) : pending i s = pending i u := by
  have hc := (balanceSpinCode i).2
  rw [← hp] at hc
  have hFalse : pendingBand i ((balanceWait i).pc + 1) = false := overlap.2.1
  cases hR : s.regs (balanceWait i).result with
  | none =>
    simp [Tau, out, hf, hc, guardHolds, readReg, hR, bind, Except.bind, pure, Except.pure] at ht
  | some v =>
    cases v
    case pred b =>
      have hG : guardHolds s (some ((balanceWait i).result, false)) = .ok b := by
        simp [guardHolds, readReg, hR, bind, Except.bind, pure, Except.pure]
      cases b
      · have hEq : skip s = u :=
          Out.tau.inj (by simpa only [Tau, out, hf, hc, hG] using ht)
        have hU : u.pc = (balanceWait i).pc + 2 := by
          rw [← hEq]
          change s.pc + 1 = (balanceWait i).pc + 2
          rw [hp]
        have hNe : (balanceWait i).pc + 2 ≠ (balanceWait i).pc + 1 := by omega
        rw [pending, pending, hp, hU, hFalse, overlap.2.2.1, hR,
          beq_eq_false_iff_ne.mpr hNe, beq_self_eq_true, Bool.false_or, Bool.false_and,
          Bool.true_and]
        rfl
      · have hEq : {s with pc := (balanceWait i).pc + 3} = u :=
          Out.tau.inj (by simpa only [Tau, out, hf, hc, hG, execLocalA, execLocalRule,
            execLocal, Op.rule, Op.isLocal, execBranch, List.findSome?_nil, ↓reduceIte,
            pure, Except.pure] using ht)
        have hU : u.pc = (balanceWait i).pc + 3 := congrArg TState.pc hEq.symm
        rw [pending, pending, hp, hU, hFalse, hR, overlap.2.2.2.1]
        simp
    all_goals
      simp [Tau, out, hf, hc, guardHolds, readReg, hR, bind, Except.bind, pure, Except.pure] at ht

private theorem pendingTau (i : Fin 11)
    {l : Launch} {g : Nat} {s u : TState} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hs : RoleShape s) (ht : Tau kernel Assumptions.all l g s u) :
    pending i s = pending i u := by
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← out_eq_core (by omega) hHi]
  obtain ⟨ins, hc, hf, hGuard⟩ := Softmax.tauScoreSource ht
  by_cases hWait : s.pc = (balanceWait i).pc
  · apply False.elim
    have hCode := (balanceSpinCode i).1
    rw [← hWait] at hCode
    exact tau_core_not_event hCode rfl ht'
  by_cases hBranch : s.pc = (balanceWait i).pc + 1
  · exact afterPollBranch i hBranch hf ht'
  by_cases hElect : s.pc = (balanceElect i).pc
  · have hOut := electTemplate (l := l) (g := g) (balanceElection i)
      (expectation i hs hf hElect)
    rw [Tau, hOut] at ht
    cases ht
  have hCode := checkedNeutral i hLo hHi hc
  simp only [neutralCode, beq_eq_false_iff_ne.mpr hWait, beq_eq_false_iff_ne.mpr hBranch,
    beq_eq_false_iff_ne.mpr hElect, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
    at hCode
  rcases hGuard with ⟨rfl, hFalse⟩ | ⟨_, _, hExec⟩
  · apply cleanPending i hBranch
    change cleanEdge i s.pc (s.pc + 1) = true
    have h := hCode.2
    cases hop : ins.op <;> simp only [hop, Bool.and_eq_true, Bool.or_eq_true] at h
    case bra dest uniform =>
      rcases h.2 with h | h
      · have hNone := Option.isNone_iff_eq_none.mp h
        simp [hNone, guardHolds, pure, Except.pure] at hFalse
      · exact h
    case brx => cases h
    all_goals exact h
  · have hFrame : LocalFrame ins.op s u := by
      rcases Softmax.scoreExecLocal hExec with h | ⟨_, hSites, _, _⟩
      · exact h
      · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSites
        omega
    apply cleanPending i hBranch
    have hp := hFrame.pc
    have h := hCode.2
    cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hp <;>
      simp only [hop, Bool.and_eq_true] at h
    case bra dest uniform => rw [hp]; exact h.1
    case brx => cases h
    all_goals rwa [hp]

private theorem readyMarkOther (i : Fin 11) {e : Event} (h : e.pc ≠ (balanceWait i).pc) :
    balancePollMark i e = false := by
  cases e with
  | mk pc kind =>
    cases kind <;> try rfl
    case wait loc phase ok acq scope => cases ok <;> simp [balancePollMark, h]

private theorem electionMarkOther (i : Fin 11) {e : Event} (h : e.pc ≠ (balanceElect i).pc) :
    balanceElectionMark i e = false := by
  simp [balanceElectionMark, ElectOrd.atSites, h]

private theorem pendingEvent (i : Fin 11) {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768) (hs : RoleShape s)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    (pending i s).toNat + (balancePollMark i e).toNat =
      (pending i u).toNat + (balanceElectionMark i e).toNat := by
  have hWindow := balanceWaitWindow i
  have hf := noFaultOfReturning he
  obtain ⟨ins, hc, hLocal, hFire⟩ := estep_event_source he
  by_cases hWait : s.pc = (balanceWait i).pc
  · rw [hWait, (balanceSpinCode i).1] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨loc, parity, ok, scope, rfl, rfl⟩ := fires_wait hFire
    have hD : ((balanceWait i).pc == (balanceWait i).pc + 1) = false := by
      apply beq_eq_false_iff_ne.mpr
      omega
    cases ok <;>
      simp only [pending, hWait, overlap.1, overlap.2.1, balancePollMark, next, setReg,
        balanceElectionMark, ElectOrd.atSites, isElectEv, hD, Bool.false_and, Bool.false_or,
        beq_self_eq_true, Bool.true_and, Function.update_self] <;> rfl
  by_cases hElect : s.pc = (balanceElect i).pc
  · have hOut := electTemplate (l := l) (g := g) (balanceElection i)
      (expectation i hs hf hElect)
    obtain ⟨tm, hTm, hF⟩ := he
    rw [hOut] at hTm
    obtain rfl := Out.ev.inj hTm.symm
    obtain ⟨inst, leader, rfl, hU⟩ := hF
    obtain rfl := Option.some.inj hU
    have hNE : ((balanceElect i).pc + 1 == (balanceWait i).pc + 1) = false := by
      apply beq_eq_false_iff_ne.mpr
      omega
    have hU : (electState l g s (balanceElection i) leader).pc =
        (balanceElect i).pc + 1 := by
      change (((balanceElect i).result.elim s (fun r => setReg s r (b32 leader))).pc + 1) = _
      cases (balanceElect i).result <;> exact congrArg (· + 1) hElect
    simp only [pending, hElect, hU, overlap.2.2.2.2.1, overlap.2.2.2.2.2, hNE,
      balanceElectionMark, ElectOrd.atSites, isElectEv, balancePollMark, Bool.false_and,
      Bool.true_or,
      Bool.false_or, Bool.true_and, beq_self_eq_true]
    rfl
  have hBranch : s.pc ≠ (balanceWait i).pc + 1 := by
    intro h
    rw [h, (balanceSpinCode i).2] at hc
    obtain rfl := Option.some.inj hc.symm
    cases hLocal
  have hEvent := estep_source_pc he
  rw [readyMarkOther i (hEvent.trans_ne hWait), electionMarkOther i (hEvent.trans_ne hElect)]
  have hCode := checkedNeutral i hLo hHi hc
  simp only [neutralCode, hLocal, Bool.false_or, beq_eq_false_iff_ne.mpr hWait,
    beq_eq_false_iff_ne.mpr hBranch, beq_eq_false_iff_ne.mpr hElect, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hCode
  have hFall : cleanEdge i s.pc (s.pc + 1) = true := by
    cases hop : ins.op <;> simp only [hop, Op.isLocal] at hLocal hCode
    case bra => cases hLocal
    case brx => cases hLocal
    all_goals exact hCode.2
  have hKeep : pending i s = pending i u := by
    rcases (linearEventProgressWithSub hc hCode.1 hs.1 hs.2.1 he).2.2 with h | h | h
    · exact cleanPending i hBranch (h.1.symm ▸ hFall)
    · exact cleanPending i hBranch (by
        simp only [cleanEdge, h.1, bne_iff_ne.mpr hBranch, beq_self_eq_true, Bool.and_self])
    · exact cleanPending i hBranch (by
        simp only [cleanEdge, h.1, bne_iff_ne.mpr hBranch, beq_self_eq_true, Bool.and_self])
  simp [Bool.toNat, hKeep]

private theorem reachesPendingBalance (i : Fin 11) {l : Launch} {g : Nat}
    {t : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g t es vs)
    (ht : 1907 ≤ t.pc ∧ t.pc < 2768) (hs : RoleShape t ∧ t.regs 1062 = some (b32 12))
    {j : Nat} {e : Event} (he : es[j]? = some e)
    (hAvoid : e.pc ≠ (balanceWait i).pc + 1) (hEnd : e.pc < 2768) :
    (pending i t).toNat + (es.take j).countP (balancePollMark i) =
      (pendingBand i e.pc).toNat + (es.take j).countP (balanceElectionMark i) := by
  have hStart {s : TState} (h : s.pc = e.pc) : pending i s = pendingBand i e.pc := by
    simp [pending, h, hAvoid]
  have hExit {s : TState} {es : List Event} {vs : List Visit}
      (hP : s.pc ∈ [3099] ∧ s.fault = none) (hR : s.regs 1062 = some (b32 12))
      (hW : Walk kernel Assumptions.all l g s es vs) (hm : e ∈ es) : False := by
    have h := mmaEpilogueExitEvents (by simpa using hP.1) hP.2 (.inl rfl) hR hW e hm
    omega
  induction hw generalizing j with
  | stop => simp at he
  | tau hTau hW ih =>
    obtain ⟨hPc' | hPc', hS⟩ := mmaCutStep ht.1 ht.2 (.inl ⟨rfl, hTau⟩) hs
    · rw [pendingTau i ht.1 ht.2 hs.1 hTau]
      exact ih hPc' hS he
    · exact (hExit hPc' hS.2 hW (List.mem_of_getElem? he)).elim
  | @ev s u front tail trail hE hW ih =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      simp [hStart (estep_source_pc hE).symm, Bool.toNat]
    | succ j =>
      have hj : tail[j]? = some e := he
      obtain ⟨hPc' | hPc', hS⟩ := mmaCutStep ht.1 ht.2 (.inr ⟨_, rfl, hE⟩) hs
      · have hEq := pendingEvent i ht.1 ht.2 hs.1 hE
        have hNext := ih hPc' hS hj
        simp only [List.take_succ_cons, List.countP_cons]
        cases hR : balancePollMark i front <;> cases hE' : balanceElectionMark i front <;>
          rw [hR, hE'] at hEq <;>
          simp only [Bool.toNat_false, Bool.toNat_true] at hEq <;>
          simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      · exact (hExit hPc' hS.2 hW (List.mem_of_getElem? hj)).elim
  | last hE =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      simp [hStart (estep_source_pc hE).symm, Bool.toNat]
    | succ j => simp at he

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

theorem releaseBody (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g index : Nat}
    {e : Event} (he : X.get (g, index) = some e) (hLo : 2145 ≤ e.pc) (hHi : e.pc < 2768) :
    ∃ (t : TState) (visits : List Visit) (inst : Nat), 6 ≤ index ∧
      X.get (g, 5) = some ⟨1907, .setMaxReg false 80 inst⟩ ∧
      At t 1908 [(1062, b32 12), (2535, b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop 6) visits := by
  have hg : g < l.threads := event_thread_lt hX he
  have hHint : e.pc ∉ registerHintSites := by simp [registerHintSites]; omega
  have hWarp : Prologue.warpIndex l g = 12 := by
    rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨start, o, hEarly, hs, hRun⟩ :=
    Prologue.nonzeroCommonPrefixOfLateEvent hp hX hg (by rw [hWarp]; decide) he (by omega)
  have hn : (X.tr g).drop 5 ≠ [] := by
    intro h
    have hLen := (List.getElem?_eq_some_iff.mp he).1
    have hDrop := List.drop_eq_nil_iff.mp h
    change index < (X.tr g).length at hLen
    omega
  have hAt : At start 174 [(1062, b32 12), (2535, b32 l.sharedBase)] :=
    hs.mono ⟨hWarp ▸ hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩
  obtain ⟨t, inst, hr, ht, hRest⟩ :=
    firstRegisterHintFromCommon hp hg (⟨12, by decide⟩ : Fin 16) hAt hRun hn
  change X.get (g, 5) = some ⟨1907, .setMaxReg false 80 inst⟩ at hr
  have hLater : 6 ≤ index := by
    by_contra h
    have heq : index = 5 := by omega
    rw [heq] at he
    have hp := congrArg Event.pc (Option.some.inj (he.symm.trans hr))
    change e.pc = 1907 at hp
    omega
  obtain ⟨visits, hw⟩ := walkFromRun hRest
  exact ⟨t, visits, inst, hLater, hr, ht, hw⟩

private theorem gateBalance (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 11) {g index : Nat} {event : Event} (he : X.get (g, index) = some event)
    (hLo : 2145 ≤ event.pc) (hHi : event.pc < 2768) (hAvoid : event.pc ≠ (balanceWait i).pc + 1) :
    ((X.tr g).take index).countP (balancePollMark i) =
      (pendingBand i event.pc).toNat +
        ElectOrd.siteOrdinal (fun pc => pc == (balanceElect i).pc) X g index := by
  have hWindow := balanceWaitWindow i
  obtain ⟨t, visits, _, hIndex, _, ht, hw⟩ := releaseBody hp hX he hLo hHi
  have hPrefix : ∀ ev ∈ (X.tr g).take 6, ev.pc ≠ (balanceWait i).pc ∧
      ev.pc ≠ (balanceElect i).pc := by
    intro ev hMem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hMem
    have hLen := hj
    rw [List.length_take] at hLen
    have hJ : j < (X.tr g).length := by omega
    rw [List.getElem_take]
    have hGet : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hJ
    have hDiff (hLate : 2145 ≤ (X.tr g)[j].pc) (hRole : (X.tr g)[j].pc < 2768) :
        False := by
      obtain ⟨_, _, _, hLater, _, _, _⟩ := releaseBody hp hX hGet hLate hRole
      omega
    exact ⟨fun h => hDiff (h ▸ hWindow.1) (by rw [h]; omega),
      fun h => hDiff (by rw [h]; omega) (by rw [h]; omega)⟩
  have hEmptyReady : ((X.tr g).take 6).countP (balancePollMark i) = 0 :=
    List.countP_eq_zero.mpr fun ev hm => by simp [readyMarkOther i (hPrefix ev hm).1]
  have hEmptyElect : ((X.tr g).take 6).countP (balanceElectionMark i) = 0 :=
    List.countP_eq_zero.mpr fun ev hm => by simp [electionMarkOther i (hPrefix ev hm).2]
  have hGet : ((X.tr g).drop 6)[index - 6]? = some event := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hShape : RoleShape t := ⟨by rw [ht.2.1]; decide, ht.2.2.1, fun _ => ht.2.1⟩
  have hRank := reachesPendingBalance i hw (by rw [ht.1]; decide)
    ⟨hShape, ht.2.2.2.2.1⟩ hGet hAvoid hHi
  have hPending : pending i t = false := by
    rw [pending, ht.1]
    fin_cases i <;> rfl
  have hTake : (X.tr g).take index =
      (X.tr g).take 6 ++ ((X.tr g).drop 6).take (index - 6) := by
    conv_lhs => rw [← Nat.add_sub_of_le hIndex, List.take_add]
  simp only [hPending, Bool.toNat_false, Nat.zero_add] at hRank
  change ((X.tr g).take index).countP (balancePollMark i) =
    (pendingBand i event.pc).toNat + ((X.tr g).take index).countP (balanceElectionMark i)
  simp only [hTake, List.countP_append, hEmptyReady, hEmptyElect,
    Nat.zero_add]
  exact hRank

private theorem pendingGateBalance (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 11) {g index : Nat} {event : Event} (he : X.get (g, index) = some event)
    (hGate : (balanceWait i).pc + 3 ≤ event.pc ∧ event.pc ≤ (balanceElect i).pc) :
    ((X.tr g).take index).countP (balancePollMark i) =
      1 + ElectOrd.siteOrdinal (fun pc => pc == (balanceElect i).pc) X g index := by
  have hWindow := balanceWaitWindow i
  have h := gateBalance hp hX i he (by omega) (by omega) (by omega)
  have hBand : pendingBand i event.pc = true := decide_eq_true ⟨by omega, hGate.2⟩
  simpa only [hBand, Bool.toNat_true] using h

/-- From a gate's successful poll through the release election, one acquire
is pending. The counts range over the lane's whole prefix. -/
theorem pendingReadyBalance (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g index : Nat} {event : Event} (he : X.get (g, index) = some event)
    (hGate : (slotWait i).pc + 3 ≤ event.pc ∧ event.pc ≤ (slotElect i).pc) :
    ((X.tr g).take index).countP (readyAtSite i) =
      1 + ElectOrd.siteOrdinal (fun pc => pc == (slotElect i).pc) X g index := by
  have hW : balanceWait (readyBalanceGate i) = slotWait i := by fin_cases i <;> rfl
  have hE : balanceElect (readyBalanceGate i) = slotElect i := by fin_cases i <;> rfl
  have hGate' : (balanceWait (readyBalanceGate i)).pc + 3 ≤ event.pc ∧
      event.pc ≤ (balanceElect (readyBalanceGate i)).pc := by rwa [hW, hE]
  have hM : balancePollMark (readyBalanceGate i) = readyAtSite i := by
    funext e
    unfold balancePollMark readyAtSite
    rw [hW]
    rfl
  have h := pendingGateBalance hp hX (readyBalanceGate i) he hGate'
  rwa [hM, hE] at h

/-- A lane's ready count is its release-election count plus the acquisition currently pending
at the observed point of that gate. -/
theorem readyBalanceAtEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g index : Nat} {event : Event} (he : X.get (g,index) = some event)
    (hLo : 2145 ≤ event.pc) (hHi : event.pc < 2768) (hAvoid : event.pc ≠ (slotWait i).pc + 1) :
    ((X.tr g).take index).countP (readyAtSite i) =
      (if (slotWait i).pc + 2 < event.pc ∧ event.pc ≤ (slotElect i).pc then 1 else 0) +
        ElectOrd.siteOrdinal (· == (slotElect i).pc) X g index := by
  have hW : balanceWait (readyBalanceGate i) = slotWait i := by fin_cases i <;> rfl
  have hE : balanceElect (readyBalanceGate i) = slotElect i := by fin_cases i <;> rfl
  have hMark : balancePollMark (readyBalanceGate i) = readyAtSite i := by
    funext e
    unfold balancePollMark readyAtSite
    rw [hW]
    rfl
  have h := gateBalance hp hX (readyBalanceGate i) he hLo hHi (by rwa [hW])
  rw [hMark,hE,pendingBand,hW,hE] at h
  split <;> simp_all

/-- The recurring score election that follows the selected probability packet. -/
def probabilityScoreElection (i : Fin 4) : Nat :=
  (electSite (commitElection (qkCommitSite (if i.val < 2 then 2 else 3)))).pc

/-- Inside a recurring probability gate, the actual poll cursor is one past the
number of previously finished score elections for that stage. -/
theorem probabilityPendingPollCount (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hGate : probabilityPc i false + 3 ≤ e.pc ∧ e.pc ≤ probabilityScoreElection i) :
    ((X.tr g).take index).countP (fun e => match e.kind with
      | .wait _ _ true _ _ => e.pc == probabilityPc i false
      | _ => false) =
      1 + ElectOrd.siteOrdinal
        (fun pc => pc == probabilityScoreElection i) X g index := by
  have hW : (balanceWait (probabilityBalanceGate i)).pc = probabilityPc i false := by
    fin_cases i <;> rfl
  have hE : (balanceElect (probabilityBalanceGate i)).pc = probabilityScoreElection i := by
    fin_cases i <;> rfl
  have hGate' : (balanceWait (probabilityBalanceGate i)).pc + 3 ≤ e.pc ∧
      e.pc ≤ (balanceElect (probabilityBalanceGate i)).pc := by rwa [hW,hE]
  have hM : balancePollMark (probabilityBalanceGate i) = (fun (e : Event) => match e.kind with
      | .wait _ _ true _ _ => e.pc == probabilityPc i false | _ => false) := by
    funext e
    unfold balancePollMark
    rw [hW]
  have h := pendingGateBalance hp hX (probabilityBalanceGate i) he hGate'
  rwa [hM,hE] at h

/-- An actual event inside the recurring gate has the successful poll of its score ordinal. -/
theorem probabilityWaitAtGateEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g index : Nat} {target : Event} (he : X.get (g,index) = some target)
    (hGate : probabilityPc i false + 3 ≤ target.pc ∧ target.pc ≤ probabilityScoreElection i) :
    ∃ j < index, ∃ (loc : Loc) (q : Nat) (acq : Bool) (scope : MbarScope),
      X.get (g,j) = some ⟨probabilityPc i false, .wait loc q true acq scope⟩ ∧
        ((X.tr g).take j).countP (fun e => match e.kind with
          | .wait _ _ true _ _ => e.pc == probabilityPc i false
          | _ => false) =
          ElectOrd.siteOrdinal (fun pc => pc == probabilityScoreElection i) X g index := by
  have hCount := probabilityPendingPollCount hp hX i he hGate
  let mark (e : Event) : Bool :=
    match e.kind with
    | .wait _ _ true _ _ => e.pc == probabilityPc i false
    | _ => false
  let n := ElectOrd.siteOrdinal (fun pc => pc == probabilityScoreElection i) X g index
  obtain ⟨j, hj, e, hGet, hSelected, hOrdinal⟩ :=
    Flow.exists_nth mark (X.tr g) (k := index) (n := n) (by

      change ((X.tr g).take index).countP mark = 1 + n at hCount
      omega)
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [mark, Bool.false_eq_true] at hSelected
  case wait loc parity ok acquire scope =>
    cases ok
    · cases hSelected
    · have hPc : pc = probabilityPc i false := beq_iff_eq.mp hSelected
      exact ⟨j,hj,loc,parity,acquire,scope,hPc ▸ hGet,hOrdinal⟩

/-- A recurring score election has the actual successful poll with the same local ordinal. -/
theorem probabilityWaitAtScoreElection (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (i : Fin 4) {g index mask inst leader : Nat}
    (he : X.Elect (g,index) (probabilityScoreElection i) mask inst leader) :
    ∃ j < index, ∃ (loc : Loc) (q : Nat) (acq : Bool) (scope : MbarScope),
      X.get (g,j) = some ⟨probabilityPc i false, .wait loc q true acq scope⟩ ∧
        ((X.tr g).take j).countP (fun e => match e.kind with
          | .wait _ _ true _ _ => e.pc == probabilityPc i false
          | _ => false) =
          ElectOrd.siteOrdinal (fun pc => pc == probabilityScoreElection i) X g index := by
  have hLo : probabilityPc i false + 3 ≤ probabilityScoreElection i := by
    fin_cases i <;> decide
  exact probabilityWaitAtGateEvent hp hX i he ⟨hLo, le_rfl⟩

private def keyScoreBalanceGate (stage : Fin 2) : Fin 11 :=
  ⟨8 + stage.val, by have := stage.isLt; omega⟩

/-- Steady V acquisition and the closing key release advance in the same MMA visit. -/
theorem valueReadyBalanceAtEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {event : Event} (he : X.get (g,index) = some event) (hLo : 2145 ≤ event.pc)
    (hHi : event.pc < 2768) (hAvoid : event.pc ≠ (slotWait 1).pc+1) :
    ((X.tr g).take index).countP (readyAtSite 1) =
      (if (slotWait 1).pc+2 < event.pc ∧ event.pc ≤ (slotElect 2).pc then 1 else 0) +
        ElectOrd.siteOrdinal (· == (slotElect 2).pc) X g index := by
  have h := gateBalance hp hX 10 he hLo hHi hAvoid
  change ((X.tr g).take index).countP (readyAtSite 1) =
    (pendingBand 10 event.pc).toNat +
      ElectOrd.siteOrdinal (· == (slotElect 2).pc) X g index at h
  unfold pendingBand at h
  change ((X.tr g).take index).countP (readyAtSite 1) =
    (decide ((slotWait 1).pc+2 < event.pc ∧ event.pc ≤ (slotElect 2).pc)).toNat +
      ElectOrd.siteOrdinal (· == (slotElect 2).pc) X g index at h
  split <;> simp_all

/-- The key acquire and one stage's score election differ only while the key gate is pending. -/
theorem keyScoreBalanceAtEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index : Nat} {event : Event} (he : X.get (g,index) = some event)
    (hLo : 2145 ≤ event.pc) (hHi : event.pc < 2768) (hAvoid : event.pc ≠ (slotWait 2).pc+1) :
    let election := (electSite (commitElection
      (qkCommitSite (if stage = 0 then 2 else 3)))).pc
    ((X.tr g).take index).countP (readyAtSite 2) =
      (if (slotWait 2).pc+2 < event.pc ∧ event.pc ≤ election then 1 else 0) +
      ElectOrd.siteOrdinal (· == election) X g index := by
  dsimp only
  let i := keyScoreBalanceGate stage
  have hW : balanceWait i = slotWait 2 := by fin_cases stage <;> rfl
  have hE : (balanceElect i).pc =
      (electSite (commitElection (qkCommitSite (if stage = 0 then 2 else 3)))).pc := by
    fin_cases stage <;> rfl
  have hMark : balancePollMark i = readyAtSite 2 := by
    funext e
    unfold balancePollMark readyAtSite
    rw [hW]
    rfl
  have h := gateBalance hp hX i he hLo hHi (by rwa [hW])
  rw [hMark,pendingBand,hE,hW] at h
  by_cases hPending : (slotWait 2).pc+2 < event.pc ∧
      event.pc ≤ (electSite (commitElection (qkCommitSite (if stage = 0 then 2 else 3)))).pc
  · simpa [hPending] using h
  · simpa [hPending] using h

/-- A recurring QK score election consumes the ready use of the same local ordinal. -/
theorem recurringKeyReadyAtScoreElection (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index inst leader : Nat}
    (he : X.Elect (g, index) (electSite (commitElection
      (qkCommitSite (if stage = 0 then 2 else 3)))).pc (2 ^ 32 - 1) inst leader) :
    ((X.tr g).take index).countP (readyAtSite 2) =
      1 + ElectOrd.siteOrdinal (· == (electSite (commitElection
        (qkCommitSite (if stage = 0 then 2 else 3)))).pc) X g index := by
  let i := keyScoreBalanceGate stage
  have hSite : (electSite (commitElection (qkCommitSite (if stage = 0 then 2 else 3)))).pc =
      (balanceElect i).pc := by fin_cases stage <;> rfl
  rw [hSite] at he ⊢
  let e : Event := ⟨(balanceElect i).pc, .elect (2 ^ 32 - 1) inst leader⟩
  have hGet : X.get (g, index) = some e := he
  have hReady := pendingGateBalance hp hX i hGet (by
    change (balanceWait i).pc + 3 ≤ (balanceElect i).pc ∧ (balanceElect i).pc ≤ (balanceElect i).pc
    fin_cases stage <;> decide)
  have hMark : balancePollMark i = readyAtSite 2 := by
    funext event
    fin_cases stage <;> rfl
  exact hMark ▸ hReady

/-- Each actual recurring K release election has both QK score elections of
its own successful ready occurrence. -/
theorem recurringKeyScoreElectionBeforeRelease (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index inst leader : Nat}
    (he : X.Elect (g, index) (slotElect 2).pc (2 ^ 32 - 1) inst leader) :
    let election := (electSite (commitElection (qkCommitSite (if stage = 0 then 2 else 3)))).pc
    ∃ j < index, ∃ inst', X.Elect (g, j) election (2 ^ 32 - 1) inst' leader ∧
      ElectOrd.siteOrdinal (· == election) X g j =
        ElectOrd.siteOrdinal (· == (slotElect 2).pc) X g index := by
  dsimp only
  let i := keyScoreBalanceGate stage
  let e : Event := ⟨(slotElect 2).pc, .elect (2 ^ 32 - 1) inst leader⟩
  let election := (balanceElect i).pc
  have hSite : (electSite (commitElection (qkCommitSite (if stage = 0 then 2 else 3)))).pc =
      election := by fin_cases stage <;> rfl
  rw [hSite]
  have hGet : X.get (g, index) = some e := he
  have hBalance := gateBalance hp hX i hGet
    (show 2145 ≤ (slotElect 2).pc by decide) (show (slotElect 2).pc < 2768 by decide)
    (by change (slotElect 2).pc ≠ (balanceWait i).pc + 1; fin_cases stage <;> decide)
  have hNone : pendingBand i e.pc = false := by fin_cases stage <;> rfl
  have hMark : balancePollMark i = readyAtSite 2 := by
    funext event
    fin_cases stage <;> rfl
  have hReady := pendingReadyBalance hp hX 2 hGet (show
    (slotWait 2).pc + 3 ≤ (slotElect 2).pc ∧ (slotElect 2).pc ≤ (slotElect 2).pc by decide)
  simp only [hNone, Bool.toNat_false, Nat.zero_add, hMark] at hBalance
  rw [hBalance] at hReady
  let ordinal := ElectOrd.siteOrdinal (· == (slotElect 2).pc) X g index
  change ElectOrd.siteOrdinal (· == election) X g index = 1 + ordinal at hReady
  obtain ⟨j, hj, event, hEvent, hSelected, hOrdinal⟩ :=
    Flow.exists_nth (balanceElectionMark i) (X.tr g) (k := index) (n := ordinal)
      (by change ordinal < ElectOrd.siteOrdinal (· == election) X g index; omega)
  obtain ⟨pc, kind⟩ := event
  cases kind <;> simp only [balanceElectionMark, ElectOrd.atSites, isElectEv,
    Bool.false_and, Bool.false_eq_true] at hSelected
  case elect mask inst' leader' =>
    have hPc : pc = election := by simpa only [Bool.true_and, beq_iff_eq] using hSelected
    rw [hPc] at hEvent
    have hActual : X.Elect (g, j) election mask inst' leader' := hEvent
    obtain ⟨ins, ty, ret, pred, operand, hc, hOp, t, bits, hRead, hMask⟩ :=
      elect_mask (hX.thr g (event_thread_lt hX hActual)) (List.mem_of_getElem? hEvent) rfl
    have hOpnd : operand = .imm (-1) := by
      cases hs : stage.val with
      | zero =>
        have hQ : stage = 0 := Fin.ext hs
        subst stage
        change kernel.code[2415]? = some ins at hc
        rw [Flow.code_2415] at hc
        obtain rfl := Option.some.inj hc.symm
        simp at hOp
        exact hOp.2.2.symm
      | succ k =>
        have hQ : stage = 1 := Fin.ext (by have := stage.isLt; omega)
        subst stage
        change kernel.code[2516]? = some ins at hc
        rw [Flow.code_2516] at hc
        obtain rfl := Option.some.inj hc.symm
        simp at hOp
        exact hOp.2.2.symm
    subst operand
    have hBits : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 (2 ^ 32 - 1)) := rfl
    rw [hBits] at hRead
    obtain rfl := Except.ok.inj hRead.symm
    have hm : mask = 2 ^ 32 - 1 := hMask.symm
    subst mask
    have hg := event_thread_lt hX he
    have hWarp : SameWarp l g g := ⟨⟨hg, hg, rfl⟩, rfl⟩
    have hLead := sameLeader hX hWarp hActual he
    subst leader'
    exact ⟨j, hj, inst', hActual, hOrdinal⟩

private theorem waitWindow (i : Fin 4) :
    2145 ≤ (slotWait i).pc ∧ (slotWait i).pc + 3 ≤ (slotElect i).pc ∧
      (slotElect i).pc + 1 < 2768 := by fin_cases i <;> decide

private theorem spinCode (i : Fin 4) :
    let w := slotWait i
    kernel.code[w.pc]? = some ⟨none, .mbarWait w.result w.base 0 (.reg w.phase) true .cta⟩ ∧
      kernel.code[w.pc + 1]? = some ⟨some (w.result, false), .bra (w.pc + 3) w.uniform⟩ := by
  fin_cases i
  · exact ⟨Flow.code_2145, Flow.code_2146⟩
  · exact ⟨Flow.code_2294, Flow.code_2295⟩
  · exact ⟨Flow.code_2352, Flow.code_2353⟩
  · exact ⟨Flow.code_2545, Flow.code_2546⟩

/-- The release election consumes the pending ready event of its own occurrence. -/
theorem releaseElectionBalance (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g index mask inst lead : Nat}
    (he : X.Elect (g, index) (slotElect i).pc mask inst lead) :
    ((X.tr g).take index).countP (readyAtSite i) =
      1 + ElectOrd.siteOrdinal (fun pc => pc == (slotElect i).pc) X g index := by
  have hGate := (waitWindow i).2.1
  exact pendingReadyBalance hp hX i he ⟨hGate, le_rfl⟩

/-- A pending event has the actual unmatched ready acquisition of its gate. -/
theorem pendingReadyOrdinal (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g index : Nat} {event : Event} (he : X.get (g, index) = some event)
    (hGate : (slotWait i).pc + 3 ≤ event.pc ∧ event.pc ≤ (slotElect i).pc) :
    ∃ j < index, ∃ (loc : Loc) (parity : Nat) (acquire : Bool) (scope : MbarScope),
      X.get (g, j) = some ⟨(slotWait i).pc, .wait loc parity true acquire scope⟩ ∧
      ((X.tr g).take j).countP (readyAtSite i) =
        ElectOrd.siteOrdinal (fun pc => pc == (slotElect i).pc) X g index := by
  have hBal := pendingReadyBalance hp hX i he hGate
  obtain ⟨j, hj, e, hGet, hSelected, hOrdinal⟩ :=
    Flow.exists_nth (readyAtSite i) (X.tr g) (k := index)
      (n := ElectOrd.siteOrdinal (fun pc => pc == (slotElect i).pc) X g index)
      (by omega)
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [readyAtSite, Bool.false_eq_true] at hSelected
  case wait loc parity ok acquire scope =>
    cases ok
    · cases hSelected
    · have hPc : pc = (slotWait i).pc := beq_iff_eq.mp hSelected
      exact ⟨j, hj, loc, parity, acquire, scope, hPc ▸ hGet, hOrdinal⟩

/-- At the release election, the last successful acquire has the election's ordinal. -/
theorem releaseElectionWaitOrdinal (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g index mask inst lead : Nat}
    (he : X.Elect (g, index) (slotElect i).pc mask inst lead) :
    ∃ j < index, ∃ (loc : Loc) (parity : Nat) (acquire : Bool) (scope : MbarScope),
      X.get (g, j) = some ⟨(slotWait i).pc, .wait loc parity true acquire scope⟩ ∧
      ((X.tr g).take j).countP (readyAtSite i) =
        ElectOrd.siteOrdinal (fun pc => pc == (slotElect i).pc) X g index := by
  have hGate := (waitWindow i).2.1
  exact pendingReadyOrdinal hp hX i he ⟨hGate, le_rfl⟩

/-- Every observed wait at one of the K/V gates is a CTA acquire. -/
theorem readyGateAcquireFlags {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (i : Fin 4)
    {g j parity : Nat} {loc : Loc} {ok acquire : Bool} {scope : MbarScope}
    (he : X.get (g, j) = some ⟨(slotWait i).pc, .wait loc parity ok acquire scope⟩) :
    acquire = true ∧ scope = .cta := by
  have hScope := actualPollScope hX he
  obtain ⟨_, hf⟩ | ⟨_, ins, _, _, hCode, hFire⟩ := get_source hX he
  · cases hf
  have hIns := Option.some.inj (hCode.symm.trans (spinCode i).1)
  obtain ⟨_, _, _, _, _, hOp, _⟩ := fires_wait_flags hFire rfl
  rw [hIns] at hOp
  cases hOp
  exact ⟨rfl, hScope⟩

private theorem decodedReleaseElection (i : Fin 4) :
    let e := slotElect i
    kernel.code[e.pc]? = some
      ⟨none, .warp ⟨.elect, none, [e.result, some e.pred], [], some (.imm (-1))⟩⟩ := by
  fin_cases i
  · exact Flow.code_2271
  · exact Flow.code_2459
  · exact Flow.code_2520
  · exact Flow.code_2635

private theorem slotElectFull {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (i : Fin 4)
    {e : EvId} {mask inst lead : Nat} (he : X.Elect e (slotElect i).pc mask inst lead) :
    mask = 2 ^ 32 - 1 := by
  have hGet : X.get e = some ⟨(slotElect i).pc, .elect mask inst lead⟩ := he
  obtain ⟨_, hb⟩ | ⟨t, ins, o, _, hCode, hF⟩ := get_source hX hGet
  · cases hb
  rw [decodedReleaseElection i] at hCode
  obtain rfl := Option.some.inj hCode.symm
  obtain ⟨_, _, _, operand, hop, _, bits, hValue, hNat⟩ :=
    elect_op hF (show (Event.mk (slotElect i).pc (.elect mask inst lead)).kind = _ from rfl)
  have hEqual : operand = .imm (-1) := by cases hop; rfl
  subst operand
  have hBits : readBits l e.1 t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 (2 ^ 32 - 1)) := rfl
  rw [hBits] at hValue
  obtain rfl := Except.ok.inj hValue
  exact hNat.symm

private theorem warpMember (l : Launch) (g : Nat) :
    electMember (2 ^ 32 - 1) (laneOf l g) := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  refine ⟨hLane, ?_⟩
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact hLane

/-- The indexed release election gives each peer's corresponding successful ready occurrence
and the dependency from that ready return to the released commit. -/
theorem readyWaitAtReleaseOrdinal (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 4) {g h index : Nat} {spec : TcCommit.Spec} (hWarp : SameWarp l g h)
    (he : X.get (g, index) = some ⟨(commitSite (releaseCommitSite i)).pc, .tc (.commit spec)⟩) :
    ∃ j loc parity, X.get (h, j) =
      some ⟨(slotWait i).pc, .wait loc parity true true .cta⟩ ∧
      ((X.tr h).take j).countP (readyAtSite i) =
        ElectOrd.siteOrdinal (fun pc => pc == (slotElect i).pc) X g (index - 1) ∧
      Relation.TransGen (DepStep l kernel X)
        (.thread (h, j), true) (.thread (g, index), false) := by
  obtain ⟨hI, inst, lead, hE⟩ := readyReleaseElection hp hX i he
  change X.Elect (g, index - 1) (slotElect i).pc (2 ^ 32 - 1) inst lead at hE
  obtain ⟨k, hPeer⟩ := ElectOrd.partner hX hWarp hE (warpMember l h)
  have namesPeer {a b : Nat} (j pc mask inst lead : Nat)
      (hs : (pc == (slotElect i).pc) = true) (hh : X.Elect (a, j) pc mask inst lead) :
      electMember mask (laneOf l b) := by
    have hSite := beq_iff_eq.mp hs
    subst pc
    rw [slotElectFull hX i hh]
    exact warpMember l b
  have hOrdinal := ElectOrd.siteOrdinal_eq hX (fun pc => pc == (slotElect i).pc)
    hWarp namesPeer namesPeer hPeer
  obtain ⟨pc, pc', mask, mask', instanceId, chosen, chosen', hElect, hOther⟩ := hPeer
  have hPc : pc = (slotElect i).pc :=
    congrArg Event.pc (Option.some.inj (hElect.symm.trans hE))
  obtain ⟨hSamePc, _, _, _⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hElect hOther hWarp
  rw [← hSamePc, hPc] at hOther
  obtain ⟨j, hj, loc, parity, acquire, scope, hPoll, hJOrdinal⟩ :=
    releaseElectionWaitOrdinal hp hX i hOther
  obtain ⟨t, ins, o, _, hCode, hF⟩ := (get_source hX hPoll).resolve_left (by
    rintro ⟨_, hBad⟩
    cases hBad)
  rw [(spinCode i).1] at hCode
  obtain rfl := Option.some.inj hCode.symm
  have hFlags : acquire = true ∧ scope = .cta := by
    have hCore :
        eventTmpl Assumptions.all l h t
          (.mbarWait (slotWait i).result (slotWait i).base 0 (.reg (slotWait i).phase) true .cta) =
        eventTmpl [] l h t
          (.mbarWait (slotWait i).result (slotWait i).base 0 (.reg (slotWait i).phase) true .cta) :=
      rfl
    rw [hCore] at hF
    simp only [eventTmpl, tmaTmpl, widenMbarScope, List.any_nil, Bool.false_eq_true,
      ↓reduceIte] at hF
    cases hm : mbarLoc l h t (slotWait i).base 0 with
    | error f =>
      simp only [hm, bind, Except.bind, ofExec, Fires] at hF
      have hF' := congrArg Event.kind hF.1
      cases hF'
    | ok mb =>
      cases hq : readBits l h t 32 (.reg (slotWait i).phase) with
      | error f =>
        simp only [hm, hq, bind, Except.bind, ofExec, Fires] at hF
        have hF' := congrArg Event.kind hF.1
        cases hF'
      | ok q =>
        simp only [hm, hq, bind, Except.bind, pure, Except.pure, ofExec, Fires] at hF
        obtain ⟨ok, hEvent, _⟩ := hF
        exact (Kind.wait.inj (congrArg Event.kind hEvent)).2.2.2
  obtain ⟨rfl, rfl⟩ := hFlags
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hPoll
  have hTrace : TraceBefore X (h, j) (h, k) := ⟨rfl, hj, ElectOrd.lt_len hOther⟩
  have hResume : Resumes kernel X (h, j) (h, k) := by
    refine ⟨hTrace, ?_⟩
    simp only [hPoll, Option.map_some, Kind.resume]
    exact ⟨_, exit, loc, parity, true, .cta, hPoll, hSpin, hTrace⟩
  have hDep := elect_depStep hX (sameWarp_symm hWarp)
    hOther ((hPc ▸ hElect) : X.Elect (g, index - 1) (slotElect i).pc mask instanceId chosen)
    (show index - 1 < index by omega) (List.getElem?_eq_some_iff.mp he).1
  exact ⟨j, loc, parity, hPoll, hJOrdinal.trans hOrdinal.symm,
    hDep.head (DepStep.of_resumes l hResume)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma

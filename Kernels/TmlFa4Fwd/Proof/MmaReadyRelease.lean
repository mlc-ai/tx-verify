-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Kernels.TmlFa4Fwd.Proof.MmaProbabilityCursor
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Flow.Code.Part034
import Kernels.TmlFa4Fwd.Flow.Code.Part037

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open Epilogue Loader Prologue Softmax

noncomputable section

/-- The four K/V-ready polls that precede the MMA releases of their slots. -/
def releaseWaitSite : Fin 4 → Fin 14
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 9

/-- The commit that returns each acquired K/V slot to the loader. -/
def releaseCommitSite : Fin 4 → Fin 12
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 9

private inductive AcquireGate
  | release (site : Fin 4)
  | firstQuery
  | secondQuery
  | terminalValue
  | terminalProbability (packet : Fin 4)
  | steadyProbability (stage : Fin 2)

private def earlyPacket (stage : Fin 2) : Fin 4 :=
  ⟨2*stage.val, by have := stage.isLt; omega⟩

private def earlyProbabilityGate (stage : Fin 2) (terminal : Bool) : AcquireGate :=
  if terminal then .terminalProbability (earlyPacket stage) else .steadyProbability stage

/-- The returning wait for the first probability packet of a PV bank. -/
def earlyProbabilityHead (stage : Fin 2) (terminal : Bool) : Nat :=
  probabilityPc ⟨2*stage.val,by have := stage.isLt; omega⟩ terminal

/-- The last PV fragment reachable within the early packet's gate. -/
def earlyProbabilityEnd (stage : Fin 2) (terminal : Bool) : Nat :=
  if terminal then (if stage.val = 0 then 2594 else 2634)
  else (if stage.val = 0 then 2343 else 2458)

private def releaseWait : AcquireGate → WaitSite
  | .release site => waitSite (releaseWaitSite site)
  | .firstQuery => waitSite 0
  | .secondQuery => waitSite 2
  | .terminalValue => waitSite 9
  | .terminalProbability packet => waitSite (probabilityWait packet true)
  | .steadyProbability stage => waitSite (probabilityWait (earlyPacket stage) false)

private def releasePc : AcquireGate → Nat
  | .release site => (commitSite (releaseCommitSite site)).pc
  | .firstQuery => 2642
  | .secondQuery => 2541
  | .terminalValue => 2646
  | .terminalProbability packet => if packet.val < 2 then 2594 else 2634
  | .steadyProbability stage => earlyProbabilityEnd stage false

private theorem releaseBounds (site : AcquireGate) :
    2141 ≤ (releaseWait site).pc ∧ (releaseWait site).pc + 3 ≤ releasePc site ∧
      releasePc site < 2768 := by
  cases site with
  | firstQuery | secondQuery | terminalValue => decide
  | release site | terminalProbability site | steadyProbability site => fin_cases site <;> decide

private theorem releaseWaitCode (site : AcquireGate) :
    let w := releaseWait site
    kernel.code[w.pc]? = some ⟨none, .mbarWait w.result w.base 0 (.reg w.phase) true .cta⟩ ∧
    kernel.code[w.pc + 1]? = some ⟨some (w.result, false), .bra (w.pc + 3) w.uniform⟩ := by
  cases site with
  | firstQuery => exact ⟨Flow.code_2141, Flow.code_2142⟩
  | secondQuery => exact ⟨Flow.code_2210, Flow.code_2211⟩
  | terminalValue => exact ⟨Flow.code_2545, Flow.code_2546⟩
  | terminalProbability packet =>
    fin_cases packet
    · exact ⟨Flow.code_2548, Flow.code_2549⟩
    · exact ⟨Flow.code_2586, Flow.code_2587⟩
    · exact ⟨Flow.code_2595, Flow.code_2596⟩
    · exact ⟨Flow.code_2626, Flow.code_2627⟩
  | steadyProbability stage =>
    fin_cases stage
    · exact ⟨Flow.code_2297,Flow.code_2298⟩
    · exact ⟨Flow.code_2419,Flow.code_2420⟩
  | release site =>
    fin_cases site
    · exact ⟨Flow.code_2145, Flow.code_2146⟩
    · exact ⟨Flow.code_2294, Flow.code_2295⟩
    · exact ⟨Flow.code_2352, Flow.code_2353⟩
    · exact ⟨Flow.code_2545, Flow.code_2546⟩

private def afterAcquire (site : AcquireGate) (pc : Nat) : Prop :=
  (releaseWait site).pc + 3 ≤ pc ∧ pc ≤ releasePc site

private instance (site : AcquireGate) (pc : Nat) : Decidable (afterAcquire site pc) :=
  inferInstanceAs (Decidable ((releaseWait site).pc + 3 ≤ pc ∧ pc ≤ releasePc site))

private def releaseBranches (site : AcquireGate) (pc : Nat) (i : Instr) : Bool :=
  (pc != (releaseWait site).pc + 2 || i.guard.isNone) &&
    match i.op with
    | .bra target _ =>
      (target != (releaseWait site).pc + 1) &&
      (!decide (afterAcquire site target) ||
        pc == (releaseWait site).pc + 1 || decide (afterAcquire site pc))
    | .brx .. => false
    | _ => pc != (releaseWait site).pc + 2

private theorem releaseBranchesAt (site : AcquireGate) {pc : Nat} {i : Instr}
    (hLo : 1907 ≤ pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some i) :
    releaseBranches site pc i = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have hAll : code.all (fun (ins, pc) => releaseBranches site pc ins) = true := by
    cases site with
    | firstQuery | secondQuery | terminalValue => set_option maxRecDepth 100000 in kernel_rfl
    | release site | terminalProbability site | steadyProbability site =>
      fin_cases site <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def AwaitingAcquire (site : AcquireGate) (s : TState) : Prop :=
  ¬ afterAcquire site s.pc ∧
    (s.pc = (releaseWait site).pc + 1 → s.regs (releaseWait site).result = some (.pred false))

private theorem acquiredWaitReturn {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (site : AcquireGate) (hPc : s.pc = (releaseWait site).pc)
    (he : EStep kernel [] l g s e (some u)) :
    ∃ loc q ok, e = ⟨(releaseWait site).pc, .wait loc q ok true .cta⟩ ∧
      u.pc = (releaseWait site).pc + 1 ∧ u.regs (releaseWait site).result = some (.pred ok) := by
  obtain ⟨_, hc, _, hFire⟩ := estep_event_source he
  rw [hPc, (releaseWaitCode site).1] at hc
  obtain rfl := Option.some.inj hc.symm
  let w := releaseWait site
  change Fires s.pc (eventTmpl [] l g s
    (.mbarWait w.result w.base 0 (.reg w.phase) true .cta)) e (some u) at hFire
  cases hm : mbarLoc l g s w.base 0 with
  | error f =>
    simp only [eventTmpl, tmaTmpl, hm, bind, Except.bind, ofExec,
      widenMbarScope, List.any_nil, Bool.false_eq_true, ↓reduceIte] at hFire
    cases hFire.2
  | ok loc =>
    cases hq : readBits l g s 32 (.reg w.phase) with
    | error f =>
      simp only [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, ofExec,
        widenMbarScope, List.any_nil, Bool.false_eq_true, ↓reduceIte] at hFire
      cases hFire.2
    | ok q =>
      simp only [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, pure, Except.pure, ofExec,
        widenMbarScope, List.any_nil, Bool.false_eq_true, ↓reduceIte] at hFire
      obtain ⟨ok, rfl, hState⟩ := hFire
      obtain rfl := Option.some.inj hState
      refine ⟨loc, q.toNat % 2, ok, ?_, ?_, Function.update_self _ _ _⟩
      · rw [hPc]
      · change s.pc + 1 = w.pc + 1
        rw [hPc]

private theorem awaitingAcquireStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (site : AcquireGate) (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hBefore : AwaitingAcquire site s) (hStep : WStep kernel Assumptions.all l g s e u) :
    AwaitingAcquire site u ∨
      ∃ loc q, e = some ⟨(releaseWait site).pc, .wait loc q true true .cta⟩ := by
  have hFall (hp : u.pc = s.pc + 1) (hRetry : s.pc ≠ (releaseWait site).pc + 2) :
      ¬ afterAcquire site u.pc := by
    have hPrev := hBefore.1
    unfold afterAcquire at hPrev ⊢
    change s.pc ≠ (releaseWait site).pc + 2 at hRetry
    omega
  rcases hStep with ⟨_, ht⟩ | ⟨ev, rfl, he⟩
  · left
    obtain ⟨i, hc, _, hSource⟩ := tauScoreSource ht
    have hCode := releaseBranchesAt site hLo hHi hc
    simp only [releaseBranches, Bool.and_eq_true] at hCode
    rcases hSource with ⟨rfl, hg⟩ | ⟨hg, hLocal, hExec⟩
    · refine ⟨hFall rfl ?_, ?_⟩
      · intro h
        have hNone := Option.isNone_iff_eq_none.mp (by simpa [h] using hCode.1)
        simp [hNone, guardHolds, pure, Except.pure] at hg
      · intro h
        change s.pc + 1 = (releaseWait site).pc + 1 at h
        have hEq : s.pc = (releaseWait site).pc := by omega
        rw [hEq, (releaseWaitCode site).1] at hc
        obtain rfl := Option.some.inj hc.symm
        simp [guardHolds, pure, Except.pure] at hg
    · have htPc : u.pc = nextPc i.op s.pc ∨ BrxTarget i.op u.pc := by
        rcases scoreExecLocal hExec with hh | ⟨_, hs, _, _⟩
        · exact hh.pc
        · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hs
          omega
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at htPc
      case bra target uni =>
        have h := hCode.2
        simp only [ho, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq, bne_iff_ne] at h
        refine ⟨?_, fun hPc => (h.1 (htPc.symm.trans hPc)).elim⟩
        intro hBad
        rw [htPc] at hBad
        rcases h.2 with (hNot | hGate) | hActive
        · exact hNot hBad
        · have hResult := hBefore.2 hGate
          rw [hGate, (releaseWaitCode site).2] at hc
          obtain rfl := Option.some.inj hc.symm
          simp only [guardHolds, readReg, hResult, bind, Except.bind, pure,
            Except.pure] at hg
          cases hg
        · exact hBefore.1 hActive
      case brx => simp [ho] at hCode
      all_goals refine ⟨hFall htPc (by simpa [ho] using hCode.2), ?_⟩
      all_goals
        intro h
        have hEq : s.pc = (releaseWait site).pc := by rw [htPc] at h; omega
        rw [hEq, (releaseWaitCode site).1] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hLocal
  · have he' : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm, hOut, hFire⟩ := he
      exact ⟨tm, by rwa [← out_eq_core (by omega) hHi], hFire⟩
    by_cases hAt : s.pc = (releaseWait site).pc
    · obtain ⟨loc, q, ok, hEvent, hNext, hReg⟩ := acquiredWaitReturn site hAt he'
      cases ok
      · exact .inl ⟨hFall (by rwa [hAt]) (by omega), fun _ => hReg⟩
      · exact .inr ⟨loc, q, congrArg some hEvent⟩
    obtain ⟨ins, hc, hl, _⟩ := estep_event_source he'
    have hCode := releaseBranchesAt site hLo hHi hc
    simp only [releaseBranches, Bool.and_eq_true] at hCode
    have hRetry : s.pc ≠ (releaseWait site).pc + 2 := by
      cases ho : ins.op <;> simp only [ho, Op.isLocal] at hl hCode
      case bra => cases hl
      case brx => cases hl
      all_goals simpa using hCode.2
    have hBlocked : s.pc ≠ (releaseWait site).pc + 1 := by
      intro h
      rw [h, (releaseWaitCode site).2] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hl
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact .inl ⟨h.symm ▸ hBefore.1, fun h' => (hBlocked (h.symm.trans h')).elim⟩
    · exact .inl ⟨hFall h hRetry, fun h' => (hAt (by rw [h] at h'; omega)).elim⟩


section
variable {l : Launch} {g : Nat} {s : TState} {events : List Event}

private theorem acquireBeforeReleaseInWalk {visits : List Visit} (site : AcquireGate)
    (hWalk : Walk kernel Assumptions.all l g s events visits) (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hBefore : AwaitingAcquire site s)
    {i : Nat} {e : Event} (he : events[i]? = some e) (hRelease : afterAcquire site e.pc) :
    ∃ j < i, ∃ loc q, events[j]? = some ⟨(releaseWait site).pc, .wait loc q true true .cta⟩ := by
  have hLate : e.pc < 2768 := hRelease.2.trans_lt (releaseBounds site).2.2
  induction hWalk generalizing i with
  | stop => simp at he
  | @tau s u events visits ht hw ih =>
    have hStep : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl, ht⟩
    obtain h | ⟨_, _, h⟩ := awaitingAcquireStep site hPc.1 hPc.2 hBefore hStep
    · obtain ⟨hNew | hExit, hShape'⟩ := mmaCutStep hPc.1 hPc.2 hStep hShape
      · exact ih hNew hShape' h he
      · have hP : u.pc = 3099 := by simpa using hExit.1
        have hRet := mmaEpilogueExitEvents hP hExit.2 (.inl rfl) hShape'.2 hw _
          (List.mem_of_getElem? he)
        omega
    · cases h
  | @ev s u ev events visits hv hw ih =>
    cases i with
    | zero =>
      obtain rfl := Option.some.inj he
      have h := estep_source_pc hv
      exact (hBefore.1 (h ▸ hRelease)).elim
    | succ i =>
      have hh : events[i]? = some e := he
      have hStep : WStep kernel Assumptions.all l g s (some ev) u := .inr ⟨ev, rfl, hv⟩
      rcases awaitingAcquireStep site hPc.1 hPc.2 hBefore hStep with h | ⟨loc, q, h⟩
      · obtain ⟨hNew | hExit, hShape'⟩ := mmaCutStep hPc.1 hPc.2 hStep hShape
        · obtain ⟨j, hj, loc, q, hEv⟩ := ih hNew hShape' h hh
          exact ⟨j + 1, Nat.succ_lt_succ hj, loc, q, hEv⟩
        · have hP : u.pc = 3099 := by simpa using hExit.1
          have hRet := mmaEpilogueExitEvents hP hExit.2 (.inl rfl) hShape'.2 hw _
            (List.mem_of_getElem? hh)
          omega
      · exact ⟨0, Nat.zero_lt_succ i, loc, q, h⟩
  | last hv =>
    cases i with
    | zero =>
      obtain rfl := Option.some.inj he
      have h := estep_source_pc hv
      exact (hBefore.1 (h ▸ hRelease)).elim
    | succ i => simp at he

private theorem waitBeforeGate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (site : AcquireGate) {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hRelease : afterAcquire site e.pc) (hEntry : 2145 ≤ e.pc) :
    ∃ j < index, ∃ loc q, X.get (g, j) =
      some ⟨(releaseWait site).pc, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) := by
  obtain ⟨_, _, hHi⟩ := releaseBounds site
  obtain ⟨pos, s, _, hLt, ht, hWalk⟩ :=
    initialMmaTrace hp hX he hEntry (hRelease.2.trans_lt hHi)
  have hScope : 1907 ≤ s.pc ∧ s.pc < 2768 := by rw [ht.1]; decide
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _, ht.2.2.1, fun _ => ht.2.1⟩, ht.2.2.2.2.1⟩
  have hBefore : AwaitingAcquire site s := by
    refine ⟨?_, ?_⟩
    · rw [ht.1]
      unfold afterAcquire
      have h := (releaseBounds site).1
      omega
    · intro h
      rw [ht.1] at h
      have hLo := (releaseBounds site).1
      omega
  have hAt : ((X.tr g).drop (pos + 1))[index - (pos + 1)]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hLt]
    exact he
  obtain ⟨k, hk, loc, q, hPoll⟩ :=
    acquireBeforeReleaseInWalk site hWalk hScope hShape hBefore hAt hRelease
  have hGet : X.get (g, pos + 1 + k) =
      some ⟨(releaseWait site).pc, .wait loc q true true .cta⟩ := by
    rw [List.getElem?_drop] at hPoll
    exact hPoll
  have hEarlier : pos + 1 + k < index := by omega
  have hLength : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hOrder : TraceBefore X (g, pos + 1 + k) (g, index) := ⟨rfl, hEarlier, hLength⟩
  obtain ⟨ex, hCanonical⟩ := actualCanonicalPoll hX hGet
  refine ⟨_, hEarlier, loc, q, hGet, hOrder, ?_⟩
  simp only [hGet, Option.map_some, Kind.resume]
  exact ⟨_, ex, loc, q, true, .cta, hGet, hCanonical, hOrder⟩


private theorem acquireBetweenInWalk {visits : List Visit} (site : AcquireGate)
    (hWalk : Walk kernel Assumptions.all l g s events visits) (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12)) {i j : Nat} {origin target : Event}
    (hi : events[i]? = some origin) (hj : events[j]? = some target) (hOrder : i < j)
    (hOut : ¬ afterAcquire site origin.pc) (hWait : origin.pc ≠ (releaseWait site).pc)
    (hNext : origin.pc ≠ (releaseWait site).pc + 1) (hIn : afterAcquire site target.pc) :
    ∃ k, i < k ∧ k < j ∧
      ∃ loc q, events[k]? = some ⟨(releaseWait site).pc,.wait loc q true true .cta⟩ := by
  have hLate := hIn.2.trans_lt (releaseBounds site).2.2
  induction hWalk generalizing i j with
  | stop => simp at hi
  | @tau s u events visits ht hw ih =>
    have hStep : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,ht⟩
    obtain ⟨hNew | hExit,hShape'⟩ := mmaCutStep hPc.1 hPc.2 hStep hShape
    · exact ih hNew hShape' hi hj hOrder
    · have hP : u.pc = 3099 := by simpa using hExit.1
      have hRet := mmaEpilogueExitEvents hP hExit.2 (.inl rfl) hShape'.2 hw _
        (List.mem_of_getElem? hj)
      omega
  | @ev s u ev events visits hv hw ih =>
    cases j with
    | zero => omega
    | succ j =>
      have hTarget : events[j]? = some target := hj
      have hStep : WStep kernel Assumptions.all l g s (some ev) u := .inr ⟨ev,rfl,hv⟩
      obtain ⟨hNew | hExit,hShape'⟩ := mmaCutStep hPc.1 hPc.2 hStep hShape
      · cases i with
        | zero =>
          obtain rfl := Option.some.inj hi
          have hSrc := estep_source_pc hv
          have hBefore : AwaitingAcquire site s :=
            ⟨fun h => hOut (hSrc.symm ▸ h),fun h => (hNext (hSrc.trans h)).elim⟩
          rcases awaitingAcquireStep site hPc.1 hPc.2 hBefore hStep with h | ⟨_,_,he⟩
          · obtain ⟨k,hk,loc,q,hPoll⟩ :=
              acquireBeforeReleaseInWalk site hw hNew hShape' h hTarget hIn
            exact ⟨k+1,by omega,Nat.succ_lt_succ hk,loc,q,hPoll⟩
          · exact (hWait (congrArg Event.pc (Option.some.inj he))).elim
        | succ i =>
          obtain ⟨k,hk,hj,loc,q,hPoll⟩ := ih hNew hShape' hi hTarget (by omega)
          exact ⟨k+1,Nat.succ_lt_succ hk,Nat.succ_lt_succ hj,loc,q,hPoll⟩
      · have hP : u.pc = 3099 := by simpa using hExit.1
        have hRet := mmaEpilogueExitEvents hP hExit.2 (.inl rfl) hShape'.2 hw _
          (List.mem_of_getElem? hTarget)
        omega
  | last hv =>
    cases j with
    | zero => omega
    | succ j => simp at hj
end

private theorem earlyProbabilityGateValues (stage : Fin 2) (terminal : Bool) :
    (releaseWait (earlyProbabilityGate stage terminal)).pc =
      earlyProbabilityHead stage terminal ∧
    releasePc (earlyProbabilityGate stage terminal) = earlyProbabilityEnd stage terminal := by
  fin_cases stage <;> cases terminal <;> decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- An earlier event outside the PV gate precedes a successful probability acquire
which returns before the selected event in that gate. -/
theorem earlyProbabilityWaitBetween (stage : Fin 2) (terminal : Bool) {g i j : Nat}
    {origin target : Event} (hi : X.get (g,i) = some origin) (hj : X.get (g,j) = some target)
    (hOrder : i < j) (hEntry : 2145 ≤ origin.pc ∧ origin.pc < 2768)
    (hOut : origin.pc < earlyProbabilityHead stage terminal ∨
      earlyProbabilityEnd stage terminal < origin.pc)
    (hIn : earlyProbabilityHead stage terminal+3 ≤ target.pc ∧
      target.pc ≤ earlyProbabilityEnd stage terminal) :
    ∃ k, i < k ∧ k < j ∧
      ∃ loc q, X.get (g,k) = some ⟨earlyProbabilityHead stage terminal,.wait loc q true true .cta⟩ ∧
        Resumes kernel X (g,k) (g,j) := by
  let site := earlyProbabilityGate stage terminal
  have hValues := earlyProbabilityGateValues stage terminal
  change (releaseWait site).pc = _ ∧ releasePc site = _ at hValues
  have hInside : afterAcquire site target.pc := by
    unfold afterAcquire
    rw [hValues.1,hValues.2]
    exact hIn
  have hOutside : origin.pc < (releaseWait site).pc ∨ releasePc site < origin.pc := by
    rw [hValues.1,hValues.2]
    exact hOut
  obtain ⟨pos,s,_,hLt,ht,hWalk⟩ := initialMmaTrace hp hX hi hEntry.1 hEntry.2
  have hScope : 1907 ≤ s.pc ∧ s.pc < 2768 := by rw [ht.1]; decide
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.1⟩
  have hi' : ((X.tr g).drop (pos+1))[i-(pos+1)]? = some origin := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hLt]
  have hj' : ((X.tr g).drop (pos+1))[j-(pos+1)]? = some target := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
  have hWidth := (releaseBounds site).2.1
  obtain ⟨k,hKLo,hKHi,loc,q,hPoll⟩ :=
    acquireBetweenInWalk site hWalk hScope hShape hi' hj' (by omega)
      (by unfold afterAcquire; omega) (by omega) (by omega) hInside
  rw [List.getElem?_drop,hValues.1] at hPoll
  have hGet : X.get (g,pos+1+k) = some
      ⟨earlyProbabilityHead stage terminal,.wait loc q true true .cta⟩ := hPoll
  have hTrace : TraceBefore X (g,pos+1+k) (g,j) := ⟨rfl,by omega,len_of_get hj⟩
  obtain ⟨exit,hCanonical⟩ := actualCanonicalPoll hX hGet
  refine ⟨_,by omega,by omega,loc,q,hGet,hTrace,?_⟩
  simp only [hGet,Option.map_some,Kind.resume]
  exact ⟨_,exit,loc,q,true,.cta,hGet,hCanonical,hTrace⟩

/-- Any actual event in a K/V release gate follows a success at the gate's ready poll. -/
theorem readyWaitBeforeGate (site : Fin 4) {g index : Nat} {e : Event}
    (he : X.get (g, index) = some e)
    (hGate : (waitSite (releaseWaitSite site)).pc + 3 ≤ e.pc ∧
      e.pc ≤ (commitSite (releaseCommitSite site)).pc) :
    ∃ j < index, ∃ loc q, X.get (g, j) =
      some ⟨(waitSite (releaseWaitSite site)).pc, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) := by
  have hFloor : 2145 ≤ (waitSite (releaseWaitSite site)).pc := by
    fin_cases site <;> decide
  exact waitBeforeGate hp hX (.release site) he hGate (by have := hGate.1; omega)

/-- A tail PV event follows the successful acquire of each probability packet it consumes. -/
theorem tailProbabilityWaitBeforeGate (packet : Fin 4) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hLo : probabilityPc packet true + 3 ≤ e.pc)
    (hHi : e.pc ≤ if packet.val < 2 then 2594 else 2634) :
    ∃ j < index, ∃ loc parity, X.get (g,j) =
      some ⟨probabilityPc packet true,.wait loc parity true true .cta⟩ ∧
      Resumes kernel X (g,j) (g,index) := by
  have hHead : 2145 ≤ probabilityPc packet true := by fin_cases packet <;> decide
  exact waitBeforeGate hp hX (.terminalProbability packet) he ⟨hLo,hHi⟩ (by omega)

/-- The selected tail PV event follows the successful V-ready acquire. -/
theorem tailValueWaitBeforeGate {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hLo : 2548 ≤ e.pc) (hHi : e.pc ≤ 2646) :
    ∃ j < index, ∃ loc q, X.get (g,j) = some ⟨2545,.wait loc q true true .cta⟩ ∧
      Resumes kernel X (g,j) (g,index) :=
  waitBeforeGate hp hX .terminalValue he ⟨hLo,hHi⟩ (by omega)

/-- The second final output commit follows the successful ready poll of the tail PV pair. -/
theorem tailValueWaitBeforeSecondOutput {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2646, .tc (.commit spec)⟩) :
    ∃ j < index, ∃ loc q, X.get (g, j) = some ⟨2545, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) :=
  tailValueWaitBeforeGate hp hX he (show 2548 ≤ 2646 by decide) (Nat.le_refl _)

/-- The terminal output commit and its preceding QK fragments follow the successful Q0 wait. -/
theorem firstQueryWaitBeforeGate {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2145 ≤ e.pc) (hHi : e.pc ≤ 2642) :
    ∃ j < index, ∃ loc q, X.get (g, j) = some ⟨2141, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) :=
  waitBeforeGate hp hX .firstQuery he ⟨by change 2144 ≤ e.pc; omega, hHi⟩ hLo

/-- Initial and recurring Q1 fragments follow a successful second query acquire. -/
theorem secondQueryWaitBeforeBank {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2259 ≤ e.pc) (hHi : e.pc ≤ 2541) :
    ∃ j < index, ∃ loc q, X.get (g, j) = some ⟨2210, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) :=
  waitBeforeGate hp hX .secondQuery he
    ⟨by change 2213 ≤ e.pc; omega, hHi⟩ (by omega)

/-- The first Q1 fragments follow a successful return from the second query acquire. -/
theorem secondQueryWaitBeforeGate {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 2259 ≤ e.pc) (hHi : e.pc ≤ 2266) :
    ∃ j < index, ∃ loc q, X.get (g, j) = some ⟨2210, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) :=
  secondQueryWaitBeforeBank hp hX he hLo (hHi.trans (by decide))

/-- The MMA lane acquires the second query before returning its empty-slot notification. -/
theorem secondQueryWaitBeforeDrain {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2541, .tc (.commit spec)⟩) :
    ∃ j < index, ∃ loc q, X.get (g, j) = some ⟨2210, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) :=
  waitBeforeGate hp hX .secondQuery he
    (by change afterAcquire .secondQuery 2541; decide)
    (by change 2145 ≤ 2541; decide)

/-- Every actual K/V release follows a successful ready poll of its gated interval. -/
theorem readyWaitBeforeCommit (site : Fin 4) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨(commitSite (releaseCommitSite site)).pc, .tc (.commit spec)⟩) :
    ∃ j < index, ∃ loc q, X.get (g, j) =
      some ⟨(waitSite (releaseWaitSite site)).pc, .wait loc q true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) :=
  readyWaitBeforeGate hp hX site he ⟨(releaseBounds (.release site)).2.1, le_rfl⟩

/-- The initial empty-slot release in MMA follows a successful acquire of ready slot zero
with the initialized request parity. -/
theorem initialReadyBeforeCommit {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2274, .tc (.commit spec)⟩) :
    ∃ j < index, X.get (g, j) =
      some ⟨2145, .wait (initObject l (g / l.block) (readySlot 0)) 0 true true .cta⟩ ∧
      Resumes kernel X (g, j) (g, index) := by
  obtain ⟨j, hj, loc, q, hPoll, hResume⟩ := readyWaitBeforeCommit hp hX 0 he
  change X.get (g, j) = some ⟨2145, .wait loc q true true .cta⟩ at hPoll
  obtain ⟨rfl, rfl, _, _⟩ := initialReadyPollOperands hp hX hPoll
  exact ⟨j, hj, hPoll, hResume⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma

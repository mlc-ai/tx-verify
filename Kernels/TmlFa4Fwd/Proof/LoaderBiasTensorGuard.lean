-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Flow.TensorIssue
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Thread.Loader

private def packetWait : Fin 5 → DrainWaitSite
  | 0 => ⟨704, 9608, 1897, 1898⟩
  | 1 => ⟨756, 9610, 1917, 1918⟩
  | 2 => ⟨1146, 9613, 2039, 7177⟩
  | 3 => ⟨1175, 9614, 2052, 7178⟩
  | 4 => ⟨1361, 9616, 2121, 7177⟩

private def tensorWait (i : Fin 10) : DrainWaitSite :=
  packetWait ⟨i.val / 2, by have := i.isLt; omega⟩

private theorem tensorWaitCode (i : Fin 10) : LoaderWaitCode (tensorWait i) := by
  suffices ∀ j, LoaderWaitCode (packetWait j) from this _
  intro j
  fin_cases j
  · exact ⟨Flow.code_704, Flow.code_705, Flow.code_706⟩
  · exact ⟨Flow.code_756, Flow.code_757, Flow.code_758⟩
  · exact ⟨Flow.code_1146, Flow.code_1147, Flow.code_1148⟩
  · exact ⟨Flow.code_1175, Flow.code_1176, Flow.code_1177⟩
  · exact ⟨Flow.code_1361, Flow.code_1362, Flow.code_1363⟩

private def tensorGuardLive (i : Fin 10) (pc : Nat) : Prop :=
  (tensorWait i).pc < pc ∧ pc ≤ (biasTensorSelector i).issue

private instance (i : Fin 10) (pc : Nat) : Decidable (tensorGuardLive i pc) :=
  inferInstanceAs (Decidable ((tensorWait i).pc < pc ∧ pc ≤ (biasTensorSelector i).issue))

private def tensorGuardBranch (i : Fin 10) (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dest _ => decide (tensorGuardLive i dest → tensorGuardLive i pc)
  | .brx .. => false
  | _ => true

private theorem tensorGuardBranchAt (i : Fin 10) {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some ins) :
    tensorGuardBranch i pc ins.op = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins,pc) => tensorGuardBranch i pc ins.op) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins,pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def GuardNotReached (i : Fin 10) (s : TState) : Prop :=
  (s.pc = (tensorWait i).pc + 1 → s.regs (tensorWait i).result = some (.pred false)) ∧
    ¬ ((tensorWait i).pc + 3 ≤ s.pc ∧ s.pc ≤ (biasTensorSelector i).issue)

private def TensorGuard (i : Fin 10) (e : Event) : Prop :=
  e.pc = (tensorWait i).pc ∧ ∃ target q sc, e.kind = .wait target q true true sc

private theorem tensorGuardStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (i : Fin 10) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hS : RingShape s)
    (hBefore : GuardNotReached i s) (hStep : WStep kernel Assumptions.all l g s ev u)
    (hNone : ∀ e ∈ ev.toList, ¬ TensorGuard i e) : GuardNotReached i u := by
  let w := tensorWait i
  have hc := tensorWaitCode i
  by_cases hInit : s.pc = w.pc
  · obtain ⟨a, q, ok, sc, hEv, rfl⟩ := wstep_poll hStep (hInit.symm ▸ hc.1)
    have hF : ok = false := by
      cases ok
      · rfl
      · exact (hNone ⟨s.pc, .wait a q true true sc⟩ (by simp [hEv])
          ⟨hInit, a, q, sc, rfl⟩).elim
    subst ok
    constructor
    · intro _
      simp [next, setReg]
    · intro h
      change w.pc + 3 ≤ s.pc + 1 ∧ _ at h
      omega
  have progress (hNext : u.pc = s.pc ∨ u.pc = s.pc + 1)
      (hC : s.pc ≠ w.pc + 1) (hR : s.pc ≠ w.pc + 2) : GuardNotReached i u := by
    have hDst := hBefore.2
    change ¬ (w.pc + 3 ≤ s.pc ∧ s.pc ≤ (biasTensorSelector i).issue) at hDst
    constructor
    · intro h
      change u.pc = w.pc + 1 at h
      omega
    · intro h
      change w.pc + 3 ≤ u.pc ∧ u.pc ≤ (biasTensorSelector i).issue at h
      omega
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    by_cases hC : s.pc = w.pc + 1
    · have hBranch := hC.symm ▸ hc.2.1
      have hr := hBefore.1 hC
      unfold Tau out at hCore
      cases hF : s.fault
      · simp [hF, hBranch, guardHolds, readReg, hr, bind, Except.bind, pure, Except.pure] at hCore
        obtain rfl := hCore
        have h' : (skip s).pc = w.pc + 2 := by simp [skip, hC]
        constructor <;> intro h
        · change (skip s).pc = w.pc + 1 at h
          omega
        · change w.pc + 3 ≤ (skip s).pc ∧ _ at h
          omega
      · simp [hF] at hCore
    by_cases hR : s.pc = w.pc + 2
    · have hBranch := hR.symm ▸ hc.2.2
      unfold Tau out at hCore
      cases hF : s.fault
      · simp [hF, hBranch, guardHolds, execLocalA, execLocalRule, execLocal, Op.isLocal,
          Op.rule, execBranch, pure, Except.pure] at hCore
        obtain rfl := hCore
        constructor <;> intro h
        · change w.pc = w.pc + 1 at h
          omega
        · change w.pc + 3 ≤ w.pc ∧ _ at h
          omega
      · simp [hF] at hCore
    obtain ⟨ins, hCode⟩ := tau_core_has_code hCore
    have hSafe := tensorGuardBranchAt i hLo hHi hCode
    rcases tau_core_frame hCode hCore with rfl | hF
    · exact progress (.inr rfl) hC hR
    have hPc := hF.pc
    cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
    case bra dst align =>
      have hOutside : ¬ tensorGuardLive i s.pc := by
        intro h
        have hEx := hBefore.2
        change ¬ (w.pc + 3 ≤ s.pc ∧ s.pc ≤ (biasTensorSelector i).issue) at hEx
        change w.pc < s.pc ∧ s.pc ≤ (biasTensorSelector i).issue at h
        omega
      rw [ho] at hSafe
      have hDont : ¬ tensorGuardLive i u.pc := by
        intro h
        exact hOutside (of_decide_eq_true hSafe (hPc ▸ h))
      constructor <;> intro h
      · have hBound : w.pc + 3 ≤ (biasTensorSelector i).issue := by fin_cases i <;> decide
        change u.pc = w.pc + 1 at h
        exact (hDont ⟨by change w.pc < u.pc; omega, by omega⟩).elim
      · change w.pc + 3 ≤ u.pc ∧ u.pc ≤ (biasTensorSelector i).issue at h
        exact hDont ⟨by change w.pc < u.pc; omega, h.2⟩
    case brx => simp [ho, tensorGuardBranch] at hSafe
    all_goals exact progress (.inr hPc) hC hR
  · obtain ⟨ins, hCode, hLocal, _⟩ := estep_event_source he
    have hC : s.pc ≠ w.pc + 1 := by
      intro h
      rw [h, hc.2.1] at hCode
      obtain rfl := Option.some.inj hCode
      cases hLocal
    have hR : s.pc ≠ w.pc + 2 := by
      intro h
      rw [h, hc.2.2] at hCode
      obtain rfl := Option.some.inj hCode
      cases hLocal
    obtain ⟨_, hp | ⟨hp, _⟩⟩ := loaderEventProgress hLo (by omega) hS.1 he
    · exact progress (.inr hp) hC hR
    · exact progress (.inl hp) hC hR

private theorem tensorAdvances {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (i : Fin 10) (hPc : e.pc = (biasTensorSelector i).issue)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = (biasTensorSelector i).issue + 1 := by
  have hs := (estep_source_pc he).symm.trans hPc
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source he
  have hi := inputSiteCode (biasTensorSelector i).input
  dsimp only at hi
  change s.pc = (inputSite (biasTensorSelector i).input).pc at hs
  rw [hs, hi] at hc
  obtain rfl := Option.some.inj hc
  obtain ⟨_,_,_,rfl,_⟩ := fires_cpTensor_issue hFire
  exact congrArg (· + 1) hs

private theorem tensorOutsideNext (i a : Fin 10)
    (hStage : (biasTensorSelector a).stage = (biasTensorSelector i).stage)
    (hHalf : (biasTensorSelector a).half = (biasTensorSelector i).half) :
    (biasTensorSelector a).issue + 1 ≠ (tensorWait i).pc + 1 ∧
      ¬ ((tensorWait i).pc + 3 ≤ (biasTensorSelector a).issue + 1 ∧
        (biasTensorSelector a).issue + 1 ≤ (biasTensorSelector i).issue) := by
  fin_cases i <;> fin_cases a <;> first | contradiction | decide


private theorem tensorGuardRange (i : Fin 10) :
    (tensorWait i).pc + 3 ≤ (biasTensorSelector i).issue ∧
      677 ≤ (biasTensorSelector i).issue ∧ (biasTensorSelector i).issue ≤ 1383 ∧
      (tensorWait i).pc ∈ [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893] ∧
      fixedLoaderWaitOffset (tensorWait i).pc = 336 + 8 * (biasTensorSelector i).stage.val := by
  fin_cases i <;> decide

/-- Actual Bias tensor halves consume a successful empty guard before their issue.
When an earlier half of the same stage and side is given, the guard is fresh. -/
theorem biasTensorGuardedSince {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 10) {g j addr : Nat} {spec : TensorCopy.Spec}
    (hIssue : X.get (g,j) = some ⟨(biasTensorSelector i).issue, .tensorIssue addr spec⟩)
    (lower : Option Nat)
    (hLower : ∀ a, lower = some a → a < j ∧ ∃ (b : Fin 10) (addr : Nat) (spec : TensorCopy.Spec),
      (biasTensorSelector b).stage = (biasTensorSelector i).stage ∧
      (biasTensorSelector b).half = (biasTensorSelector i).half ∧
      X.get (g,a) = some ⟨(biasTensorSelector b).issue, .tensorIssue addr spec⟩) :
    ∃ (k : Nat) (poll : Event) (q : Nat) (scope : MbarScope),
      X.get (g,k) = some poll ∧
      poll.kind = .wait (biasEmptyObject l (g / l.block) (biasTensorSelector i).stage)
        q true true scope ∧ Resumes kernel X (g,k) (g,j) ∧
      ∀ a, lower = some a → a < k := by
  let site := biasTensorSelector i
  have hLo : 677 ≤ site.issue := (tensorGuardRange i).2.1
  have hHi : site.issue ≤ 1383 := (tensorGuardRange i).2.2.1
  obtain ⟨warp, s, vs, hWarp, hN, hAt, hWalk, hGet⟩ :=
    biasInstructionWalk hp hX hIssue ⟨hLo,hHi⟩
  have hStart : 174 ≤ s.pc ∧ s.pc ≤ 1901 := by rw [hAt.1]; decide
  have hShape := ringShapeOfAt hAt
  have hFrame := hAt.2.2.2.2
  have hBeyond {t : TState} (h : GuardNotReached i t) (hPc : t.pc = site.issue) : False := by
    have hT : (tensorWait i).pc + 3 ≤ site.issue := (tensorGuardRange i).1
    exact h.2 ⟨hPc.symm ▸ hT, hPc.le⟩
  have hTransition {t u : TState} {ev : Option Event}
      (hLo : 174 ≤ t.pc) (hHi : t.pc < 1901) (hs : RingShape t)
      (hb : GuardNotReached i t) (hStep : WStep kernel Assumptions.all l g t ev u)
      (hn : ∀ e ∈ ev.toList, ¬ TensorGuard i e) : GuardNotReached i u :=
    tensorGuardStep i hLo hHi hs hb hStep hn
  have hSite : site.issue < 1901 := by omega
  have hPrior : ∃ k < j - 5, ∃ e, ((X.tr g).drop 5)[k]? = some e ∧ TensorGuard i e ∧
      ∀ a, lower = some a → a < 5 + k := by
    cases hLowerCase : lower with
    | none =>
      have hb : GuardNotReached i s := by
        have hWait : 704 ≤ (tensorWait i).pc := by fin_cases i <;> decide
        constructor
        · intro h; rw [hAt.1] at h; omega
        · intro h
          have h := h.1
          rw [hAt.1] at h
          omega
      obtain ⟨k, hk, e, he, hm⟩ :=
        loaderEventPrecededBy warp hWalk hStart hShape hFrame hb hGet hSite hBeyond
          (fun lo hi ss _ hb hs hn => hTransition lo hi ss hb hs hn)
      exact ⟨k,hk,e,he,hm,by simp⟩
    | some a =>
      obtain ⟨haj, b, addr', spec', hStage, hHalf, ha⟩ := hLower a hLowerCase
      have hA : 677 ≤ (biasTensorSelector b).issue ∧ (biasTensorSelector b).issue ≤ 1383 :=
        ⟨(tensorGuardRange b).2.1, (tensorGuardRange b).2.2.1⟩
      obtain ⟨_, _, _, _, hAB, _, _, _⟩ := biasInstructionWalk hp hX ha hA
      have ha' : ((X.tr g).drop 5)[a - 5]? =
          some ⟨(biasTensorSelector b).issue, .tensorIssue addr' spec'⟩ := by
        rw [List.getElem?_drop, Nat.add_sub_of_le hAB]
        exact ha
      have hB {t u : TState}
          (hStep : EStep kernel Assumptions.all l g t
            ⟨(biasTensorSelector b).issue, .tensorIssue addr' spec'⟩ (some u)) :
          GuardNotReached i u := by
        have hPc := tensorAdvances b rfl hStep
        obtain ⟨hFirst,hSecond⟩ := tensorOutsideNext i b hStage hHalf
        constructor
        · intro h
          exact (hFirst (hPc.symm.trans h)).elim
        · rw [hPc]
          exact hSecond
      obtain ⟨k, hk, hk', e, he, hm⟩ :=
        loaderEventBetween warp hWalk hStart hShape hFrame ha' hGet (by omega)
          (by dsimp; omega) hSite hB hBeyond
          (fun lo hi ss _ hb hs hn => hTransition lo hi ss hb hs hn)
      exact ⟨k,hk',e,he,hm, by intro b hb; cases hb; omega⟩
  obtain ⟨k, hk, poll, hPoll, hGuard, hOrder⟩ := hPrior
  rw [List.getElem?_drop] at hPoll
  obtain ⟨hSource, mb, q, sc, hKind⟩ := hGuard
  have hTrace : TraceBefore X (g,5+k) (g,j) :=
    ⟨rfl, by omega, (List.getElem?_eq_some_iff.mp hIssue).1⟩
  obtain ⟨source, kind⟩ := poll
  change source = (tensorWait i).pc at hSource
  change kind = _ at hKind
  subst kind source
  have hAddr := loaderFixedWaitOffset hp hX (g := g) (index := 5+k) hPoll
    (tensorGuardRange i).2.2.2.1
  have hLoc : mb = biasEmptyObject l (g / l.block) site.stage := by
    rw [hAddr, (tensorGuardRange i).2.2.2.2]
    rfl
  rw [hLoc] at hPoll
  change X.get (g, 5 + k) = _ at hPoll
  obtain ⟨exit, hCanonical⟩ := actualCanonicalPoll hX hPoll
  refine ⟨5+k, _, q, sc, hPoll, rfl, ⟨hTrace, ?_⟩, hOrder⟩
  simp only [hPoll, Option.map_some, Kind.resume]
  exact ⟨_, exit, _, q, true, sc, hPoll, hCanonical, hTrace⟩
end PTX.Kernels.TmlFa4Fwd.Loader

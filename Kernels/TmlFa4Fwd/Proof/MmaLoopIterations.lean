-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

noncomputable section

private def loopTests (visits : List Visit) : Nat :=
  (visits.takeWhile (fun v => v.pc < 2534)).countP (fun v => v.pc == 2533)

private def reachesTail (visits : List Visit) : Prop :=
  ∃ v ∈ visits, v.pc = 2534

private theorem reachesTail_cons {v : Visit} {vs : List Visit} (hNot : v.pc ≠ 2534) :
    reachesTail (v :: vs) ↔ reachesTail vs := by
  simp [reachesTail, List.mem_cons, hNot]

private def observesTail (events : List Event) : Prop :=
  ∃ e ∈ events, 2534 ≤ e.pc

private theorem observesTail_cons {e : Event} {es : List Event} (hBefore : e.pc < 2534) :
    observesTail (e :: es) ↔ observesTail es := by
  constructor
  · rintro ⟨f, hf, hPc⟩
    rcases List.mem_cons.mp hf with rfl | hm
    · omega
    · exact ⟨f, hm, hPc⟩
  · rintro ⟨f, hf, hPc⟩
    exact ⟨f, List.mem_cons_of_mem e hf, hPc⟩

private theorem counterPrefixLanding {l : Launch} {g : Nat} {s u : TState}
    (hLo : 2530 ≤ s.pc) (hHi : s.pc < 2533) (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = s.pc + 1 := by
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← out_eq_core (by omega) (by omega)]
  have hCode : ∃ i, kernel.code[s.pc]? = some i ∧
      nextPc i.op s.pc = s.pc + 1 ∧ ∀ p, ¬ BrxTarget i.op p := by
    generalize hPc : s.pc = pc at hLo hHi ⊢
    interval_cases pc
    · exact ⟨_, Flow.code_2530, rfl, nofun⟩
    · exact ⟨_, Flow.code_2531, rfl, nofun⟩
    · exact ⟨_, Flow.code_2532, rfl, nofun⟩
  obtain ⟨i, hc, hNext, hNoBrx⟩ := hCode
  rcases tau_core_frame hc ht' with rfl | h
  · rfl
  · rcases h.pc with hp | hp
    · exact hp.trans hNext
    · exact (hNoBrx _ hp).elim

private theorem advanceCounterWalk {l : Launch} {g steps : Nat} {s u : TState}
    {es : List Event} {vs : List Visit}
    (hLo : 2530 ≤ s.pc) (hSum : s.pc + steps = 2534)
    (hr : run kernel Assumptions.all l g steps s = some u)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    (loopTests vs = 0 ∧ ¬ reachesTail vs ∧ es = []) ∨
      ∃ post, post.length + steps = vs.length ∧
        loopTests vs = loopTests post + (if 0 < steps then 1 else 0) ∧
        Walk kernel Assumptions.all l g u es post ∧ (reachesTail vs → reachesTail post) := by
  induction steps generalizing s es vs with
  | zero =>
    obtain rfl := Option.some.inj hr
    exact .inr ⟨vs, by simp, by simp, hw, id⟩
  | succ steps ih =>
    have hPc : s.pc < 2534 := by omega
    simp only [run] at hr
    cases ht : tauStep kernel Assumptions.all l g s with
    | none => simp [ht] at hr
    | some t =>
      rw [ht, Option.bind_some] at hr
      have hTau := tauStep_iff.mp ht
      cases hw with
      | stop => exact .inl ⟨rfl, by simp [reachesTail], rfl⟩
      | @tau s s' es vs hs hw' =>
        have hEq := Out.tau.inj (hTau.symm.trans hs)
        subst t
        have hTail : reachesTail (visit kernel l g s none :: vs) ↔ reachesTail vs :=
          reachesTail_cons (by simpa only [visit_pc] using Nat.ne_of_lt hPc)
        cases steps with
        | zero =>
          obtain rfl := Option.some.inj hr
          have hPC : s.pc = 2533 := by omega
          exact .inr ⟨vs, by simp, by simp [loopTests, visit_pc, hPC], hw', hTail.mp⟩
        | succ steps =>
          have hPC : s.pc < 2533 := by omega
          have hNext := counterPrefixLanding hLo hPC hs
          have hCount : loopTests (visit kernel l g s none :: vs) = loopTests vs := by
            have hNe : s.pc ≠ 2533 := by omega
            simp [loopTests, visit_pc, hPc, hNe]
          rcases ih (by omega) (by omega) hr hw' with hNone |
            ⟨post, hLen, hTest, hWalk, hReached⟩
          · exact .inl ⟨hCount.trans hNone.1, fun h => hNone.2.1 (hTail.mp h), hNone.2.2⟩
          · exact .inr ⟨post, by simp; omega,
              by simpa only [hCount, Nat.zero_lt_succ, ↓reduceIte] using hTest,
              hWalk, hReached ∘ hTail.mp⟩
      | ev he _ => exact (not_tau_of_stops (stops_of_estep he) hTau).elim
      | last he => exact (not_tau_of_stops (stops_of_estep he) hTau).elim

set_option maxRecDepth 100000 in
private theorem afterSteadyLoop :
    (kernel.code.drop 2534).all (fun i => Thread.staysPastEvent 2534 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterSteadyLoopSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2534 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem noSteadyReadyAfterLoop {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (gate : Fin 2)
    (hWalk : Walk kernel Assumptions.all l g s es vs) (hPc : 2534 ≤ s.pc) :
    es.countP (steadyReadyAt gate) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hMem hMark
  have hAfter := Thread.eventTailEventsOfSegmentFloor afterSteadyLoop
    (fun site _ hSite seg hMatch => by
      have hStop := List.all_eq_true.mp afterSteadyLoopSegments site hSite
      rw [hMatch,decide_eq_true_eq] at hStop
      exact hStop) hWalk hPc e hMem
  obtain ⟨pos,kind⟩ := e
  cases kind <;> try cases hMark
  case wait loc parity ok acquire sc =>
    cases ok <;> simp [steadyReadyAt] at hMark
    have hBefore : (steadyReadySite gate).1 < 2534 := by fin_cases gate <;> decide
    change 2534 ≤ pos at hAfter
    omega

private theorem loopTestCount {l : Launch} {g : Nat} :
    ∀ fuel n {s : TState} {es : List Event} {vs : List Visit},
      vs.length = fuel → (2291 ≤ s.pc ∧ s.pc ≤ 2530) → 2 ≤ n → n ≤ 2 ^ 32 + 1 →
      At s s.pc [(7204, wideCounterWord n)] → Walk kernel Assumptions.all l g s es vs →
      loopTests vs ≤ n - 1 ∧ (reachesTail vs ∨ observesTail es → loopTests vs = n - 1) ∧
        (∀ gate, loopTests vs ≤ es.countP (steadyReadyAt gate) + steadyReadyCredit gate s) ∧
        (observesTail es → ∀ gate,
          es.countP (steadyReadyAt gate) + steadyReadyCredit gate s = loopTests vs) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro n s es vs hLength hSlice hn hN hAt hw
    obtain ⟨hLo, hHi⟩ := hSlice
    by_cases hEnd : s.pc = 2530
    · obtain ⟨u, hLocals, hU⟩ := stepWideCounter (l := l) (g := g) hn hN
        (by simpa only [hEnd] using hAt)
      rcases advanceCounterWalk hEnd.ge (by omega) hLocals hw with hNone |
        ⟨post, hCount, hTest, hWalk, hTail⟩
      · refine ⟨by simp [hNone.1], ?_, (fun _ => by simp [hNone.1]), ?_⟩
        rintro (hVisit | hEvent)
        · exact (hNone.2.1 hVisit).elim
        · simp [hNone.2.2, observesTail] at hEvent
        · simp [hNone.2.2, observesTail]
      · by_cases hContinue : 2 < n
        · have hPC : u.pc = 2291 := by simpa only [ite_eq_left hContinue] using hU.1
          have hBound := ih post.length (by omega) (n - 1) rfl (by omega) (by omega) (by omega)
            (by simpa only [hPC, ite_eq_left hContinue] using hU) hWalk
          simp only [ite_eq_left (show 0 < 4 by decide)] at hTest
          refine ⟨by have := hBound.1; omega, (fun h => ?_), (fun gate => ?_), fun h gate => ?_⟩
          · have := hBound.2.1 (Or.imp hTail id h)
            omega
          · have hCredit := hBound.2.2.1 gate
            rw [steadyReadyCreditEntry gate hPC] at hCredit
            rw [steadyReadyCreditTest gate hEnd]
            omega
          · have hCredit := hBound.2.2.2 h gate
            rw [steadyReadyCreditEntry gate hPC] at hCredit
            rw [steadyReadyCreditTest gate hEnd]
            omega
        · have hPC : u.pc = 2534 := by simpa only [ite_eq_right hContinue] using hU.1
          have hZ : loopTests post = 0 := by cases hWalk <;> simp [loopTests, visit_pc, hPC]
          simp only [hZ, ite_eq_left (show 0 < 4 by decide), Nat.zero_add] at hTest
          refine ⟨by omega, (fun _ => by omega), (fun gate => ?_), fun _ gate => ?_⟩
          · rw [steadyReadyCreditTest gate hEnd]
            omega
          · rw [steadyReadyCreditTest gate hEnd, noSteadyReadyAfterLoop gate hWalk hPC.ge]
            exact hTest.symm
    · have hLt : s.pc < 2530 := by omega
      have hCut : s.pc < 2534 := by omega
      have hTest : s.pc ≠ 2533 := by omega
      cases hw with
      | stop => simp [loopTests, reachesTail, observesTail]
      | @tau s u es vs ht hw =>
        have hFrame := steadyTauFrame hLo hLt hAt.2.1 hAt.2.2.1 ht
        have hU : At u u.pc [(7204, wideCounterWord n)] := by
          refine ⟨rfl, hFrame.2.2.2.1.trans hAt.2.1, hFrame.2.2.2.2.1.trans hAt.2.2.1,
            hFrame.2.2.2.2.2.1.trans hAt.2.2.2.1, ?_, trivial⟩
          exact hFrame.2.2.2.2.2.2.trans hAt.2.2.2.2.1
        have hBound := ih vs.length (by simp only [List.length_cons] at hLength; omega) n rfl
          ⟨hFrame.2.1, hFrame.2.2.1⟩ hn hN hU hw
        rw [reachesTail_cons (by simpa only [visit_pc] using Nat.ne_of_lt hCut)]
        have hSame :
            loopTests (visit kernel l g s none :: vs) = loopTests vs := by
          simp [loopTests, visit_pc, hCut, hTest]
        rw [hSame]
        refine ⟨hBound.1, hBound.2.1, (fun gate => ?_), fun h gate => ?_⟩
        · exact steadyReadyCreditTau gate hLo hLt hAt.2.1 hAt.2.2.1 ht ▸ hBound.2.2.1 gate
        · exact steadyReadyCreditTau gate hLo hLt hAt.2.1 hAt.2.2.1 ht ▸ hBound.2.2.2 h gate
      | @ev s u e es vs he hw =>
        have hFrame := steadyEventFrame hLo hLt he
        have hU : At u u.pc [(7204, wideCounterWord n)] := by
          refine ⟨rfl, hFrame.2.1.trans hAt.2.1, hFrame.2.2.1.trans hAt.2.2.1,
            hFrame.2.2.2.1.trans hAt.2.2.2.1, ?_, trivial⟩
          exact hFrame.2.2.2.2.trans hAt.2.2.2.2.1
        have hBound := ih vs.length (by simp only [List.length_cons] at hLength; omega) n rfl
          (by omega) hn hN hU hw
        rw [reachesTail_cons (by simpa only [visit_pc] using Nat.ne_of_lt hCut)]
        have hSame :
            loopTests (visit kernel l g s (some e) :: vs) = loopTests vs := by
          simp [loopTests, visit_pc, hCut, hTest]
        rw [hSame, observesTail_cons ((estep_source_pc he).trans_lt hCut)]
        have hCredit (gate : Fin 2) := steadyReadyCreditEvent gate hLo hLt he
        have hCount (gate : Fin 2) :
            (e::es).countP (steadyReadyAt gate) =
              es.countP (steadyReadyAt gate) + (steadyReadyAt gate e).toNat := by
          cases hMark : steadyReadyAt gate e <;> simp [hMark]
        refine ⟨hBound.1,hBound.2.1,(fun gate => ?_),fun h gate => ?_⟩
        · have hRank := hBound.2.2.1 gate
          rw [hCredit] at hRank
          rw [hCount]
          omega
        · have hRank := hBound.2.2.2 h gate
          rw [hCredit] at hRank
          rw [hCount]
          omega
      | last he =>
        rw [observesTail_cons ((estep_source_pc he).trans_lt hCut)]
        simp [loopTests, visit_pc, hCut, hTest, reachesTail, observesTail, Nat.ne_of_lt hCut]

variable {l : Launch} {g n : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (h : Walk kernel Assumptions.all l g s es vs) (hn : 2 ≤ n) (hN : n ≤ 2 ^ 32 + 1)
    (hs : At s 2291 [(7204, wideCounterWord n)])
include h hn hN hs

/-- A trace through any actual tail event already contains the steady ready
observations required by the counter, even if the lane stops before exiting. -/
theorem steadyReadyAcquiresBeforeTailEvent {event : Event} (hTail : event ∈ es)
    (hAfter : 2534 ≤ event.pc) (gate : Fin 2) :
    n - 1 ≤ es.countP (steadyReadyAt gate) := by
  have hBound := loopTestCount (l := l) (g := g) vs.length n (s := s) rfl
    (by rw [hs.1]; decide) hn hN (by simpa only [hs.1] using hs) h
  have hReady := hBound.2.2.1 gate
  rwa [hBound.2.1 (.inr ⟨event, hTail, hAfter⟩),
    steadyReadyCreditEntry gate hs.1, Nat.add_zero] at hReady

/-- At a witnessed tail event, each steady cache gate has exactly one successful
wait per completed traversal of the initialized trip counter. -/
theorem steadyReadyAcquireCountBeforeTailEvent {event : Event} (hTail : event ∈ es)
    (hAfter : 2534 ≤ event.pc) (gate : Fin 2) :
    es.countP (steadyReadyAt gate) = n - 1 := by
  have hBound := loopTestCount (l := l) (g := g) vs.length n (s := s) rfl
    (by rw [hs.1]; decide) hn hN (by simpa only [hs.1] using hs) h
  have hHas : observesTail es := ⟨event,hTail,hAfter⟩
  have hReady := hBound.2.2.2 hHas gate
  rwa [hBound.2.1 (.inr hHas), steadyReadyCreditEntry gate hs.1, Nat.add_zero] at hReady

end
end PTX.Kernels.TmlFa4Fwd.Mma

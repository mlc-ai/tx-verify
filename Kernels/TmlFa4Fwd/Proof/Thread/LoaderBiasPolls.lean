-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasOrdinals
import Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.Proof PTX.Flow PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader

/-- A loader can poll the first Bias buffer while priming, in a pair, or in its last single
transfer. The second buffer is only used while priming and in a pair. -/
def biasEmptyWaitSites (stage : Fin 2) : List Nat :=
  if stage = 0 then [704, 1146, 1361] else [756, 1175]

private def fixedLoaderPolls : List Nat := [517, 679, 704, 730, 756, 782, 1146, 1175, 1361, 1893]
private def ringLoaderPolls : List Nat := [960, 1206, 1430, 1611, 1866, 1877, 1888]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem loaderPollClass {g index pc phase : Nat} {loc : Loc} {ok acq : Bool}
    {scope : MbarScope} (hWarp : 14 ≤ Prologue.warpIndex l g)
    (hEvent : X.get (g,index) = some ⟨pc, .wait loc phase ok acq scope⟩) :
    pc ∈ fixedLoaderPolls ∨ pc ∈ ringLoaderPolls := by
  have hSite := actualMbarPollSite hX hEvent
  have hAudit : Flow.mbarWait.toList.all (fun source =>
      decide (173 < source ∧ source < 9205 ∧ source ∉ registerHintSites)) = true := by decide
  obtain ⟨hLo, hTop, hHint⟩ := of_decide_eq_true (List.all_eq_true.mp hAudit _ hSite)
  have hRole := roleBodyPcOfEvent hp hX hEvent hLo hHint
  change roleBodyPc (Prologue.warpIndex l g) pc at hRole
  have hHi : pc ≤ 1901 := by
    rcases hRole with h | h
    · omega
    · rw [ite_eq_left hWarp] at h
      exact h.2
  have hCut : Flow.mbarWait.toList.all (fun source =>
      decide (source ≤ 1901 → source ∈ fixedLoaderPolls ∨ source ∈ ringLoaderPolls)) = true :=
    by decide
  exact (of_decide_eq_true (List.all_eq_true.mp hCut _ hSite)) hHi

/-- An actual poll of the chosen Bias return buffer on a loader lane has its fixed site. -/
theorem biasEmptyLoaderPollSite {g index pc cta phase : Nat} {ok acq : Bool} {scope : MbarScope}
    (stage : Fin 2) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (hEvent : X.get (g,index) = some ⟨pc, .wait (biasEmptyObject l cta stage) phase ok acq scope⟩) :
    pc ∈ biasEmptyWaitSites stage := by
  have off {n owner : Nat}
      (h : biasEmptyObject l cta stage = ⟨.shared, owner, l.sharedBase + n⟩) :
      n = 336 + 8 * stage.val := by
    have hAddr := congrArg Loc.addr h
    change l.sharedBase + (336 + 8 * stage.val) = l.sharedBase + n at hAddr
    omega
  rcases loaderPollClass hp hX hWarp hEvent with hf | hr
  · have hLoc := loaderFixedWaitOffset hp hX hEvent hf
    have hOffset := off hLoc
    have hTab : fixedLoaderPolls.all (fun j =>
        decide (fixedLoaderWaitOffset j = 336 + 8 * stage.val → j ∈ biasEmptyWaitSites stage)) =
        true := by
      fin_cases stage <;> decide
    exact (of_decide_eq_true (List.all_eq_true.mp hTab _ hf)) hOffset
  · obtain ⟨n, hn, hLoc⟩ := loaderRingWaitAddress hp hX hEvent hr
    have hOffset := off hLoc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    have := stage.isLt
    omega

omit hp hX in
private theorem biasWaitCode (stage : Fin 2) {pc : Nat} (h : pc ∈ biasEmptyWaitSites stage) :
    ∃ result base phase,
      kernel.code[pc]? = some ⟨none, .mbarWait result base 0 (.reg phase) true .cta⟩ := by
  fin_cases stage
  · have hs : pc = 704 ∨ pc = 1146 ∨ pc = 1361 := by simpa [biasEmptyWaitSites] using h
    rcases hs with rfl | rfl | rfl
    · exact ⟨_, _, _, Flow.code_704⟩
    · exact ⟨_, _, _, Flow.code_1146⟩
    · exact ⟨_, _, _, Flow.code_1361⟩
  · have hs : pc = 756 ∨ pc = 1175 := by simpa [biasEmptyWaitSites] using h
    rcases hs with rfl | rfl
    · exact ⟨_, _, _, Flow.code_756⟩
    · exact ⟨_, _, _, Flow.code_1175⟩

/-- Each recorded Bias-empty loader poll is a CTA acquire and uses a one-bit parity. -/
theorem biasEmptyLoaderPollShape {g index pc cta phase : Nat} {ok acq : Bool} {scope : MbarScope}
    (stage : Fin 2) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (hEvent : X.get (g,index) = some ⟨pc, .wait (biasEmptyObject l cta stage) phase ok acq scope⟩) :
    pc ∈ biasEmptyWaitSites stage ∧ phase < 2 ∧ acq = true ∧ scope = .cta := by
  have hSite := biasEmptyLoaderPollSite hp hX stage hWarp hEvent
  refine ⟨hSite, ?_⟩
  obtain ⟨result, base, par, hc⟩ := biasWaitCode stage hSite
  rcases get_source hX hEvent with ⟨_, hBad⟩ | ⟨s, ins, o, _, code, hf⟩
  · cases hBad
  obtain rfl := Option.some.inj (hc.symm.trans code)
  have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
  simp only [eventTmpl, tmaTmpl, hWide, widenMbarScope, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure] at hf
  cases hm : mbarLoc l g s base 0 with
  | error f => simp [hm, ofExec, Fires] at hf
  | ok loc =>
    cases hq : readBits l g s 32 (.reg par) with
    | error f => simp [hm, hq, ofExec, Fires] at hf
    | ok q =>
      obtain ⟨_, hf, _⟩ := (show ∃ ok', _ ∧ _ from by
        simpa only [hm, hq, ofExec, Fires] using hf)
      obtain ⟨_, hPhase, _, hAcq, hScope⟩ := Kind.wait.inj (congrArg Event.kind hf)
      exact ⟨hPhase ▸ Nat.mod_lt _ (by decide), hAcq, hScope⟩

/-- An actual expectation resumes from the successful Bias-empty acquire at its exact
thread-local generation number. -/
theorem biasExpectationOrdinalGuard {cta g j : Nat} (stage : Fin 2)
    (hIssue : X.Arrive (g,j) (biasReadyObject l cta stage) 32768 1 true .cta) :
    ∃ (k : Nat) (e : Event) (phase : Nat), k < j ∧
      X.get (g,k) = some e ∧
      e.kind = .wait (biasEmptyObject l cta stage) phase true true .cta ∧
      okPolls (biasEmptyObject l cta stage) ((X.tr g).take k) =
        arrivals (biasReadyObject l cta stage) ((X.tr g).take j) ∧
      Resumes kernel X (g,k) (g,j) := by
  have hBudget := biasExpectationPollBudget hp hX stage hIssue
  obtain ⟨k, source, phase, acquire, scope, hk, he, hOrdinal⟩ :=
    MbarRing.Poll.exists_nth hBudget
  have hWarp := PTX.Kernels.TmlFa4Fwd.Loader.biasExpectationIssuerWarp hp hX stage hIssue
  obtain ⟨_, _, rfl, rfl⟩ := biasEmptyLoaderPollShape hp hX stage hWarp.ge he
  obtain ⟨exit, hs⟩ := actualCanonicalPoll hX he
  obtain ⟨pc, hEnd⟩ := hIssue
  have hTrace : TraceBefore X (g,k) (g,j) := ⟨rfl, hk, (List.getElem?_eq_some_iff.mp hEnd).1⟩
  refine ⟨k, _, phase, hk, he, rfl, hOrdinal, hTrace, ?_⟩
  simp only [he, Option.map_some, Kind.resume]
  exact ⟨source, exit, _, phase, true, .cta, he, hs, hTrace⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

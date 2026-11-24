-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryStatisticsTrace
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Flow.Code.Part055

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

/-- A Bias rendezvous joins the four softmax warps of a single stage. -/
def biasParticipants (stage : Fin 2) : Finset Nat :=
  if stage.val = 0 then {0, 1, 2, 3} else {4, 5, 6, 7}

theorem biasParticipantIff (stage : Fin 2) (warp : Nat) :
    warp ∈ biasParticipants stage ↔ warp < 8 ∧ warp / 4 = stage.val := by
  fin_cases stage <;>
    simp [biasParticipants, Finset.mem_insert, Finset.mem_singleton] <;> omega

/-- The two Bias resources each require exactly 128 participants. -/
theorem biasBarrierShape {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (stage : Fin 2) : NamedBar.Shape l (some 128) (biasParticipants stage) (11 + stage.val) := by
  have hCard : (biasParticipants stage).card = 4 := by fin_cases stage <;> decide
  have hStage := stage.isLt
  refine ⟨by omega, ?_, ?_, by omega⟩
  · rw [hp.block, hCard]
    rfl
  · intro w hw
    have hWarp := ((biasParticipantIff stage w).mp hw).1
    rw [hp.block]
    omega

/-- The two decoded Bias sites are the only named barriers with this participant count. -/
theorem biasCountSite {site : Nat} (hSite : site ∈ namedBarrierSites)
    (hCount : namedBarrierCount site = some 128) :
    site = 3583 ∨ site = 5271 := by
  have audit : namedBarrierSites.all (fun j =>
      decide (namedBarrierCount j = some 128 → j = 3583 ∨ j = 5271)) = true := by decide
  exact (of_decide_eq_true (List.all_eq_true.mp audit site hSite)) hCount

/-- Every arrival on either Bias resource uses the issuing lane's softmax stage and count. -/
theorem biasArrivalStage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {id : Nat} {count : Option Nat} {mode : BarMode}
    (hId : id = 11 ∨ id = 12) (hArrival : BarrierArrival X i id count mode) :
    warpIndex l i.1 < 8 ∧ id = 11 + warpIndex l i.1 / 4 ∧ count = some 128 ∧ mode = .sync := by
  obtain ⟨⟨site, kind⟩, hGet, hKind⟩ := hArrival
  change kind = _ at hKind
  subst kind
  have hCount : count = some 128 := by
    have h := actualNamedBarrierCountById hp hX hGet
    rcases hId with rfl | rfl <;> exact h
  obtain ⟨hSite, hActual, hMode, _, _⟩ := actualNamedBarrier hp hX hGet
  rcases biasCountSite hSite (hActual.symm.trans hCount) with rfl | rfl
  · have h := Softmax.actualBiasBarrierStage hp hX false hGet
    exact ⟨h.1, h.2, hCount, hMode⟩
  · have h := Softmax.actualBiasBarrierStage hp hX true hGet
    exact ⟨h.1, h.2, hCount, hMode⟩

/-- All actual Bias arrivals come from the four selected softmax warps. -/
theorem biasBarrierSources {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) :
    NamedBar.Sources l X (some 128) (biasParticipants stage) (11 + stage.val) := by
  intro i site count hArrive hg
  obtain ⟨mode, hGet⟩ := hArrive
  have hId : 11 + stage.val = 11 ∨ 11 + stage.val = 12 := by fin_cases stage <;> decide
  obtain ⟨hWarp, hExact, hCount, _⟩ := biasArrivalStage hp hX hId
    (i := i) (count := count) (mode := mode) ⟨_, hGet, rfl⟩
  exact ⟨(biasParticipantIff stage (warpIndex l i.1)).mpr ⟨hWarp, by omega⟩, hCount⟩

private theorem firstBiasSourceAfterSelector {l : Launch} {g : Nat} {s t u : TState}
    {e : Event} (hPc : s.pc = 3582)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hEvent : EStep kernel Assumptions.all l g t e (some u)) : t.pc = 3583 := by
  rcases Relation.ReflTransGen.cases_head hLocal with rfl | ⟨v, hTau, hTail⟩
  · obtain ⟨ins, hc, hNonlocal, _⟩ := estep_event_source hEvent
    rw [hPc, Flow.code_3582] at hc
    obtain rfl := Option.some.inj hc
    cases hNonlocal
  · obtain ⟨ins, hc, _, hExec⟩ := Softmax.tauScoreSource hTau
    rw [hPc, Flow.code_3582] at hc
    obtain rfl := Option.some.inj hc
    have hv : v.pc = 3583 := by
      rcases hExec with ⟨_, hSkip⟩ | ⟨_, _, hLocal⟩
      · cases hSkip
      · rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨seg, hSite, _, _⟩
        · have h := hFrame.pc
          rw [hPc] at h
          simpa only [nextPc, BrxTarget, or_false] using h
        · exact ((by rw [hPc]; decide : s.pc ∉ Assumptions.swExp2Sites) hSite).elim
    rcases Relation.ReflTransGen.cases_head hTail with rfl | ⟨_, hTau', _⟩
    · exact hv
    · obtain ⟨ins, hc, _, hExec⟩ := Softmax.tauScoreSource hTau'
      rw [hv, Flow.code_3583] at hc
      obtain rfl := Option.some.inj hc
      rcases hExec with ⟨_, hSkip⟩ | ⟨_, hNonlocal, _⟩
      · cases hSkip
      · cases hNonlocal

private theorem biasEventAfterFirstFence {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g fence : Nat} (hg : g < l.threads)
    (hFence : X.get (g,fence) =
      some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩)
    (hLen : fence + 2 < (X.tr g).length) :
    ∃ id count mode, X.get (g,fence+1) = some ⟨3583, .bar id count mode⟩ := by
  obtain ⟨_, hRun⟩ := hX.thr g hg
  obtain ⟨s, v, hStep, hTail⟩ := hRun.after_event hFence (by omega)
  have hPc : s.pc = 3581 := (estep_source_pc hStep).symm
  have hv : v.pc = 3582 := by
    obtain ⟨ins, hc, _, hFire⟩ := estep_event_source hStep
    rw [hPc, Flow.code_3581] at hc
    obtain rfl := Option.some.inj hc
    have hCont : v = next s := Option.some.inj hFire.2
    rw [hCont]
    exact congrArg (· + 1) hPc
  have hTwo : 2 ≤ ((X.tr g).drop (fence+1)).length := by rw [List.length_drop]; omega
  generalize hEvents : (X.tr g).drop (fence+1) = events at hTail hTwo
  cases hTail with
  | nil => simp at hTwo
  | last => simp at hTwo
  | @step _ t1 t2 event rest _ hLocal hEvent hRest =>
    have ht := firstBiasSourceAfterSelector hv hLocal hEvent
    obtain ⟨_, id, count, mode, hKind⟩ :=
      markedBarrierContinues ht Flow.code_3583 rfl hEvent
    have hePc := (estep_source_pc hEvent).trans ht
    have hGet : X.get (g,fence+1) = some event := by
      change ((X.tr g)[fence+1]?) = some event
      rw [← show ((X.tr g).drop (fence+1))[0]? = (X.tr g)[fence+1]? by simp,
        hEvents]
      rfl
    have hEq : event = ⟨3583, .bar id count mode⟩ := by
      obtain ⟨site, kind⟩ := event
      change site = 3583 at hePc
      change kind = _ at hKind
      rw [hePc, hKind]
    exact ⟨id, count, mode, hGet.trans (congrArg some hEq)⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g : Nat}
include hp hX hCuQ

/-- An exiting active softmax lane has already reached the first Bias rendezvous. -/
theorem firstBiasFenceArrivalOfActiveExit (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hWarp : warpIndex l g < 8) (hExit : Exited X g) :
    ∃ fence, X.get (g,fence) =
        some ⟨3581,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g,fence+1) = some ⟨3583,.bar (11+warpIndex l g/4) (some 128) .sync⟩ := by
  obtain ⟨j, ⟨site, kind⟩, hGet, hKind⟩ := hExit
  change kind = _ at hKind
  subst kind
  have hSite := actualExitPc hX hGet
  subst site
  have hg := event_thread_lt hX hGet
  obtain ⟨_, fence, notice, _, _, hFence, ⟨e, hNotice, hPublish⟩, _, hBefore⟩ :=
    firstScoreStatisticsOfExit hp hX hWarp hWork hCuQ
      (usedKProtected hp hX) hGet
  have hLen := Execution.exit_last hX hg hGet
  have hNoticeLen := len_of_get hNotice
  have hDifferent : notice ≠ j := by
    intro hn
    rw [hn, hGet] at hNotice
    obtain rfl := Option.some.inj hNotice
    cases hPublish
  have hTwo : fence + 2 < (X.tr g).length := by
    change j + 1 = (X.tr g).length at hLen
    change notice < (X.tr g).length at hNoticeLen
    omega
  obtain ⟨id, count, mode, he⟩ := biasEventAfterFirstFence hX hg hFence hTwo
  obtain ⟨_, hCount, hMode, _, _⟩ := actualNamedBarrier hp hX he
  have hExact := (Softmax.actualBiasBarrierStage hp hX false he).2
  rw [hExact, hCount, hMode] at he
  exact ⟨fence,hFence,he⟩

/-- An actual first Bias barrier reached by a completed active softmax lane. -/
theorem firstBiasDecodedArrivalOfActiveExit (hWork : g/l.block < tilePrefix p p.batch*p.heads)
    (hWarp : warpIndex l g < 8) (hExit : Exited X g) :
    ∃ j, X.get (g,j) = some ⟨3583,.bar (11+warpIndex l g/4) (some 128) .sync⟩ := by
  obtain ⟨fence,_,he⟩ := firstBiasFenceArrivalOfActiveExit hp hX hCuQ hWork hWarp hExit
  exact ⟨fence+1,he⟩

/-- An exiting active softmax lane has reached the Bias rendezvous of its stage. -/
theorem firstBiasArrivalOfActiveExit (hWork : g/l.block < tilePrefix p p.batch*p.heads)
    (hWarp : warpIndex l g < 8) (hExit : Exited X g) :
    ∃ j, BarrierArrival X (g,j) (11+warpIndex l g/4) (some 128) .sync := by
  obtain ⟨j,he⟩ := firstBiasDecodedArrivalOfActiveExit hp hX hCuQ hWork hWarp hExit
  exact ⟨j,_,he,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Thread

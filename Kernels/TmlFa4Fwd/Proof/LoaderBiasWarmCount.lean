-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.LoaderPacketFlow
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
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
import Kernels.TmlFa4Fwd.Flow.Code.Part018
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

/-- Each stage and half has one tensor issue site per warm traversal. -/
def warmBiasIssueSite (stage half : Fin 2) : Nat :=
  if stage = 0 then (if half = 0 then 1163 else 1173)
  else (if half = 0 then 1191 else 1200)

private def remainingWarmMarker (marker : Nat) (s : TState) : Nat :=
  if s.pc ≤ marker then 1 else 0

private theorem warmMarkerBounds (stage half : Fin 2) :
    917 ≤ warmBiasIssueSite stage half ∧ warmBiasIssueSite stage half < 1348 := by
  fin_cases stage <;> fin_cases half <;> decide

private theorem warmMarkerCode (stage half : Fin 2) :
    ∃ ca grp dst offset map coords mb off mode policy,
      kernel.code[warmBiasIssueSite stage half]? = some
        ⟨none,.cpTensor ca grp dst offset map coords mb off none mode policy⟩ := by
  fin_cases stage <;> fin_cases half
  · exact ⟨_,_,_,_,_,_,_,_,_,_,Flow.code_1163⟩
  · exact ⟨_,_,_,_,_,_,_,_,_,_,Flow.code_1173⟩
  · exact ⟨_,_,_,_,_,_,_,_,_,_,Flow.code_1191⟩
  · exact ⟨_,_,_,_,_,_,_,_,_,_,Flow.code_1200⟩

private theorem warmMarkerBackedge (stage half : Fin 2) :
    ∀ edge ∈ loaderBackEdges, 917 ≤ edge.1 → edge.1 < 1348 →
      warmBiasIssueSite stage half < edge.1 → warmBiasIssueSite stage half < edge.2 := by
  fin_cases stage <;> fin_cases half <;> decide

private theorem warmMarkerStep (stage half : Fin 2)
    {l : Launch} {g : Nat} {s t : TState} {e : Option Event}
    (hLo : 917 ≤ s.pc) (hHi : s.pc < 1348)
    (he : WStep kernel Assumptions.all l g s e t) :
    e.toList.countP (fun e => e.pc == warmBiasIssueSite stage half) +
      remainingWarmMarker (warmBiasIssueSite stage half) t ≤
        remainingWarmMarker (warmBiasIssueSite stage half) s := by
  let mark := warmBiasIssueSite stage half
  rcases he with ⟨rfl,hTau⟩ | ⟨ev,rfl,hEvent⟩
  · simp only [Option.toList_none, List.countP_nil, Nat.zero_add]
    change remainingWarmMarker mark t ≤ remainingWarmMarker mark s
    by_cases hPast : mark < s.pc
    · have ht : mark < t.pc := by
        by_contra! h
        have hEdge := loaderTauBackEdge (by omega) (by omega) (by omega) hTau
        exact (Nat.not_lt_of_ge h)
          (warmMarkerBackedge stage half _ hEdge hLo hHi hPast)
      simp [remainingWarmMarker,show ¬ s.pc ≤ mark by omega, show ¬ t.pc ≤ mark by omega]
    · unfold remainingWarmMarker
      rw [ite_eq_left (Nat.le_of_not_gt hPast)]
      split <;> omega
  · have hSource := estep_source_pc hEvent
    have hEvent' : EStep kernel [] l g s ev (some t) := by
      obtain ⟨tm,ho,hf⟩ := hEvent
      exact ⟨tm,by rwa [← loaderOutCore (by omega) (by omega)],hf⟩
    have hStep := (estep_return_pc hEvent' (fun _ _ _ h => execLocal_frame h)).2
    have hAdvance : s.pc = mark → t.pc = s.pc+1 := by
      intro h
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hc⟩ := warmMarkerCode stage half
      obtain ⟨ins,hCode,_,hf⟩ := estep_event_source hEvent
      rw [h,hc] at hCode
      obtain rfl := Option.some.inj hCode
      obtain ⟨_,_,_,rfl,_⟩ := fires_cpTensor_issue hf
      rfl
    change (if ev.pc == mark then 1 else 0) + remainingWarmMarker mark t ≤
      remainingWarmMarker mark s
    rw [hSource]
    rcases Nat.lt_trichotomy s.pc mark with hBefore | hOn | hAfter
    · simp [remainingWarmMarker,hBefore.le,show s.pc ≠ mark by omega]
      split <;> omega
    · have ht := hAdvance hOn
      simp [remainingWarmMarker,hOn,ht]
    · have ht : mark < t.pc := by rcases hStep with h | h <;> omega
      simp [remainingWarmMarker,show s.pc ≠ mark by omega,show ¬ s.pc ≤ mark by omega,
        show ¬ t.pc ≤ mark by omega]

variable {l : Launch}

private theorem noWarmMarkersAfter {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (stage half : Fin 2) (hp : 1353 ≤ s.pc) (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (fun e => e.pc == warmBiasIssueSite stage half) = 0 := by
  have hFloor : (kernel.code.drop 1353).all (fun i => Thread.staysPastEvent 1353 i.op) =
      true := by set_option maxRecDepth 100000 in kernel_rfl
  have hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (1353 ≤ seg.stop)
      | none => false) = true := by set_option maxRecDepth 100000 in kernel_rfl
  apply List.countP_eq_zero.mpr
  intro e hE hMark
  have h := Thread.eventTailEvents hFloor hSegments hw hp e hE
  have hPc := beq_iff_eq.mp hMark
  have hLimit := (warmMarkerBounds stage half).2
  omega

private theorem warmCutBeforeIncrement {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    {k trips : Nat} (stage half : Fin 2) (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : 917 ≤ s.pc ∧ s.pc ≤ 1348) (hShape : RingShape s) (hk : s.regs 7174 = some (b32 k))
    (hT : s.regs 1091 = some (b32 trips)) :
    let mark := warmBiasIssueSite stage half
    let selected := fun (e : Event) => e.pc == mark
    es.countP selected ≤ remainingWarmMarker mark s ∨
      ∃ u before rest tail, es = before ++ rest ∧
        before.countP selected ≤ remainingWarmMarker mark s ∧
        u.pc = 1348 ∧ RingShape u ∧ u.regs 7174 = some (b32 k) ∧
        u.regs 1091 = some (b32 trips) ∧ Walk kernel Assumptions.all l g u rest tail := by
  dsimp only
  let mark := warmBiasIssueSite stage half
  let selected := fun (e : Event) => e.pc == mark
  have step {s t : TState} {e : Option Event} {rest : List Event} {tail : List Visit}
      (hW : Walk kernel Assumptions.all l g s (e.toList ++ rest)
        (visit kernel l g s e :: tail))
      (hTail : Walk kernel Assumptions.all l g t rest tail)
      (hp : 917 ≤ s.pc ∧ s.pc ≤ 1348) (hS : RingShape s)
      (hk : s.regs 7174 = some (b32 k)) (hT : s.regs 1091 = some (b32 trips))
      (hStep : WStep kernel Assumptions.all l g s e t)
      (ih : (917 ≤ t.pc ∧ t.pc ≤ 1348) → RingShape t → t.regs 7174 = some (b32 k) →
        t.regs 1091 = some (b32 trips) →
        rest.countP selected ≤ remainingWarmMarker mark t ∨
          ∃ u before after vs, rest = before ++ after ∧
            before.countP selected ≤ remainingWarmMarker mark t ∧
            u.pc = 1348 ∧ RingShape u ∧ u.regs 7174 = some (b32 k) ∧
            u.regs 1091 = some (b32 trips) ∧ Walk kernel Assumptions.all l g u after vs) :
      (e.toList ++ rest).countP selected ≤ remainingWarmMarker mark s ∨
        ∃ u before after vs, e.toList ++ rest = before ++ after ∧
          before.countP selected ≤ remainingWarmMarker mark s ∧
          u.pc = 1348 ∧ RingShape u ∧ u.regs 7174 = some (b32 k) ∧
          u.regs 1091 = some (b32 trips) ∧ Walk kernel Assumptions.all l g u after vs := by
    by_cases hEq : s.pc = 1348
    · exact .inr ⟨s,[],_,_,rfl,by simp,hEq,hS,hk,hT,hW⟩
    have hlt : s.pc < 1348 := by omega
    have hBudget := warmMarkerStep stage half hp.1 hlt hStep
    change e.toList.countP selected + remainingWarmMarker mark t ≤
      remainingWarmMarker mark s at hBudget
    obtain ⟨hU,hK,hTrips,hLo,hBound | hBound⟩ := warmBodyStep hp.1 hlt hS hStep
    · rcases ih ⟨hLo,hBound⟩ hU (hK.trans hk) (hTrips.trans hT) with hDone |
        ⟨u,before,after,vs,hList,hPre,hPc,hShape,hI,hT,hAfter⟩
      · left
        rw [List.countP_append]
        omega
      · refine .inr ⟨u,e.toList ++ before,after,vs,by rw [hList,List.append_assoc],
          ?_,hPc,hShape,hI,hT,hAfter⟩
        rw [List.countP_append]
        omega
    · left
      rw [List.countP_append,noWarmMarkersAfter stage half hBound hTail]
      omega
  induction hw with
  | stop => exact .inl (by simp)
  | tau ht hW ih => exact step (.tau ht hW) hW hPc hShape hk hT (.inl ⟨rfl,ht⟩) ih
  | ev he hW ih => exact step (.ev he hW) hW hPc hShape hk hT (.inr ⟨_,rfl,he⟩) ih
  | @last t ev he =>
    left
    change [ev].countP selected ≤ remainingWarmMarker mark t
    rw [List.countP_singleton]
    change (if ev.pc == mark then 1 else 0) ≤ remainingWarmMarker mark t
    rw [estep_source_pc he]
    by_cases hEq : t.pc = mark
    · simp [hEq,remainingWarmMarker]
    · simp [hEq]

private theorem faultAtWarmIncrementNoMark {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (stage half : Fin 2) (hp : s.pc = 1348) (hf : s.fault ≠ none)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (fun e => e.pc == warmBiasIssueSite stage half) = 0 := by
  cases hof : s.fault with
  | none => exact (hf hof).elim
  | some f =>
    cases hw with
    | stop => rfl
    | tau ht _ => simp [Tau,out,hof] at ht
    | ev he _ =>
      obtain ⟨tm,ho,hFire⟩ := he
      simp [out,hof] at ho
      subst tm
      cases hFire.2
    | last he =>
      rw [List.countP_singleton,estep_source_pc he,hp]
      have hNe : 1348 ≠ warmBiasIssueSite stage half :=
        (Nat.ne_of_lt (warmMarkerBounds stage half).2).symm
      simp [hNe]

private theorem warmMarkersFromCursor {g trips : Nat} (hTrip : trips < 2^31) (stage half : Fin 2)
    (n : Nat) {s : TState} {es : List Event} {vs : List Visit} {k : Nat} (hn : min trips 9 - k = n)
    (hk : k < min trips 9) (hPc : s.pc = 917) (hShape : RingShape s)
    (hK : s.regs 7174 = some (b32 k)) (hT : s.regs 1091 = some (b32 trips))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (fun e => e.pc == warmBiasIssueSite stage half) ≤ n := by
  induction n using Nat.strong_induction_on generalizing s es vs k with
  | h n ih =>
    let mark := warmBiasIssueSite stage half
    let selected := fun (e : Event) => e.pc == mark
    have hBounds := warmMarkerBounds stage half
    have hRem : remainingWarmMarker mark s = 1 := by
      unfold remainingWarmMarker
      rw [hPc,ite_eq_left hBounds.1]
    change es.countP selected ≤ n
    rcases warmCutBeforeIncrement stage half hw ⟨hPc.ge,by omega⟩ hShape hK hT with hDone |
      ⟨u,before,rest,path,hList,hBefore,hU,hShape,hValue,hTrips,hWalk⟩
    · change es.countP selected ≤ remainingWarmMarker mark s at hDone
      omega
    change before.countP selected ≤ remainingWarmMarker mark s at hBefore
    rw [hList,List.countP_append]
    by_cases hf : u.fault = none
    swap
    · rw [faultAtWarmIncrementNoMark stage half hU hf hWalk]
      omega
    obtain ⟨v,hMove,hV⟩ := warmCounterStep hTrip hk hU hShape hf hValue hTrips
    rcases Mma.advanceWalkLocals hMove hWalk with rfl | ⟨_,_,_,hTail⟩
    · simp at *
      omega
    by_cases hMore : k+1 < min trips 9
    · have hNext : At v 917 [(7174,b32 (k+1)),(1091,b32 trips)] := by simpa [hMore] using hV
      have hNew : min trips 9 - (k+1) < n := by omega
      have hBudget := ih _ hNew rfl hMore hNext.1 (ringShapeOfAt hNext)
        hNext.2.2.2.2.1 hNext.2.2.2.2.2.1 hTail
      change rest.countP selected ≤ _ at hBudget
      omega
    · have hEnd : v.pc = 1353 := by simpa [hMore] using hV.1
      rw [noWarmMarkersAfter stage half hEnd.ge hTail]
      omega

/-- Each actual half issues at most once per remaining warm iteration, even on a
finite prefix that stops midway through the current iteration. -/
theorem warmBiasIssuesFromEntry {g k trips : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (stage half : Fin 2) (hTrip : trips < 2^31) (hk : k < min trips 9)
    (hs : At s 917 [(7174,b32 k),(1091,b32 trips)]) (hw : Walk kernel Assumptions.all l g s es vs) :
    es.countP (fun e => e.pc == warmBiasIssueSite stage half) ≤ min trips 9 - k :=
  warmMarkersFromCursor hTrip stage half _ rfl hk hs.1 (ringShapeOfAt hs)
    hs.2.2.2.2.1 hs.2.2.2.2.2.1 hw


private theorem warmRankedVisitBound {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (stage half : Fin 2) (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : 917 ≤ s.pc ∧ s.pc ≤ 1348) (hShape : RingShape s) (j : Nat)
    (hRank : (es.take j).countP Execution.isShfl < loaderShuffleTail 1348 s.pc) :
    (es.take (j+1)).countP (fun e => e.pc == warmBiasIssueSite stage half) ≤
      remainingWarmMarker (warmBiasIssueSite stage half) s := by
  let mark := warmBiasIssueSite stage half
  let selected := fun (e : Event) => e.pc == mark
  have hAudit (bound : Nat) : ((kernel.code.drop 917).take (1348-917)).all
      (fun i => loaderPipelineCutOp 917 1348 bound [] i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCode : (((kernel.code.drop 917).take (1348-917)).zipIdx 917).all
      (fun (i,pc) => LoaderRankedInstr 1348 pc i) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hBefore {t : TState} {n : Nat} (hLimit : t.pc ≤ 1348)
      (hLeft : n < loaderShuffleTail 1348 t.pc) : t.pc < 1348 := by
    by_contra! h
    apply Nat.not_lt_zero n
    have heq : t.pc = 1348 := by omega
    simp [heq,loaderShuffleTail] at hLeft
  have advance {t u : TState} {e : Option Event}
      (hT : 917 ≤ t.pc) (hU : t.pc < 1348) (hShape : RingShape t)
      (hStep : WStep kernel Assumptions.all l g t e u) :
      (917 ≤ u.pc ∧ u.pc ≤ 1348) ∧ RingShape u ∧
      loaderShuffleTail 1348 t.pc =
        e.toList.countP Execution.isShfl+loaderShuffleTail 1348 u.pc := by
    obtain ⟨hLow,hHigh,hS,_⟩ := pipelineCutStep (F := []) (by decide) (by decide)
      ⟨hT,hU⟩ (hAudit u.pc) hStep hShape trivial
    exact ⟨⟨hLow,hHigh.resolve_right (Nat.lt_irrefl _)⟩,hS,
      rankedLoaderStep (by decide) hCode hT hU hStep⟩
  change (es.take (j+1)).countP selected ≤ remainingWarmMarker mark s
  induction hw generalizing j with
  | stop => simp
  | @tau s u es vs ht hw ih =>
    have hHi := hBefore hPc.2 hRank
    let hStep : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,ht⟩
    obtain ⟨hU,hS,hRemaining⟩ := advance hPc.1 hHi hShape hStep
    have hL := warmMarkerStep stage half hPc.1 hHi hStep
    have hR : (es.take j).countP Execution.isShfl < loaderShuffleTail 1348 u.pc := by
      simpa [hRemaining] using hRank
    exact (ih hU hS j hR).trans (by simpa [mark] using hL)
  | @ev s u e es vs he hw ih =>
    have hHi := hBefore hPc.2 hRank
    let hStep : WStep kernel Assumptions.all l g s (some e) u := .inr ⟨_,rfl,he⟩
    have hL := warmMarkerStep stage half hPc.1 hHi hStep
    change [e].countP selected + remainingWarmMarker mark u ≤ remainingWarmMarker mark s at hL
    cases j with
    | zero =>
      rw [Nat.zero_add,List.take_succ_cons,List.take_zero]
      omega
    | succ j =>
      obtain ⟨hU,hS,hRemaining⟩ := advance hPc.1 hHi hShape hStep
      have hR : (es.take j).countP Execution.isShfl < loaderShuffleTail 1348 u.pc := by
        rw [List.take_succ_cons,List.countP_cons,hRemaining] at hRank
        simp only [Option.toList_some,List.countP_singleton] at hRank
        omega
      have hi := ih hU hS j hR
      simp only [List.take_succ_cons,List.countP_cons] at hL ⊢
      omega
  | @last s e he =>
    have hFull : [e].take (j+1) = [e] := by simp
    rw [hFull,List.countP_singleton]
    unfold selected
    rw [estep_source_pc he]
    by_cases h : s.pc = mark
    · simp [h,remainingWarmMarker]
    · simp [h]

/-- Through any observed event in the same warm traversal, a half can issue at most once. -/
theorem warmIssueCountOfRankedPrefix {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (stage half : Fin 2) (hw : Walk kernel Assumptions.all l g s es vs) (hs : s.pc = 917)
    (hShape : RingShape s) (j : Nat) (hRank : (es.take j).countP Execution.isShfl < 64) :
    (es.take (j+1)).countP (fun e => e.pc == warmBiasIssueSite stage half) ≤ 1 := by
  have hCount : loaderShuffleTail 1348 917 = 64 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hBound := warmRankedVisitBound stage half hw (by omega) hShape j (by rwa [hs,hCount])
  exact hBound.trans (by unfold remainingWarmMarker; split <;> omega)

end PTX.Kernels.TmlFa4Fwd.Loader

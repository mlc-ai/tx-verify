-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorContinue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (RingShape recurringEmptyWait reuseArrival packetArrivalStepFrame copyCommitCode
   recurringPacketSite loaderOutCore loaderSliceEvents walkVisitIssuePc)

private theorem afterGuardQuiet (site : Fin 4) {e : Event}
    (hInside : (CursorRoute.packetAfterPoll site).inside e.pc = true) :
    ¬ recurringEmptyEvent e := by
  rintro ⟨i, loc, q, rfl⟩
  fin_cases site <;> fin_cases i <;> cases hInside

/-- The audited packet segment after a successful empty acquire has no further
successful empty acquire before its ready publication. -/
theorem packetGuardWindow (site : Fin 4) {l : Launch} {g copy : Nat}
    {s : TState} {events : List Event} {visits : List Visit}
    (hPc : s.pc = (recurringEmptyWait site).pc + 3) (hShape : RingShape s)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hIndex : copy < events.length)
    (hNoArrival : ∀ j < copy, ∀ e, events[j]? = some e → e.pc = reuseArrival site →
      ¬ recurringPublicationEvent e) :
    ∀ j < copy, ∀ e, events[j]? = some e → ¬ recurringEmptyEvent e := by
  let route := CursorRoute.packetAfterPoll site
  have hInside : route.inside s.pc = true := by
    rw [hPc]
    fin_cases site <;> decide
  intro j hBefore e hGet
  rcases route.cutWalk hw hInside hShape with hAll |
    ⟨u, pre, rest, front, tail, hSplit, _, hFront, hExit, _, _, hPre, hTail⟩
  · exact afterGuardQuiet site (eventInside route hw hAll e (List.mem_of_getElem? hGet))
  have hExit' : u.pc = reuseArrival site := by simpa [route,CursorRoute.stops] using hExit
  have hWithin : j < pre.length := by
    by_contra! hFar
    have hAt : ∃ mark, rest[0]? = some mark ∧ mark.pc = reuseArrival site ∧
        recurringPublicationEvent mark := by
      cases hTail with
      | stop =>
        simp only [hSplit, List.append_nil] at hGet
        have := (List.getElem?_eq_some_iff.mp hGet).1
        omega
      | @tau _ v _ _ h _ =>
        have hc := (copyCommitCode (recurringPacketSite site)).2
        change kernel.code[reuseArrival site]? = _ at hc
        rw [← hExit'] at hc
        have hLo : 174 ≤ reuseArrival site := by fin_cases site <;> decide
        have hHi : reuseArrival site < 1906 := by fin_cases site <;> decide
        have hCore : Tau kernel [] l g u v := by
          unfold Tau at *
          rwa [← loaderOutCore (hExit'.symm ▸ hLo) (hExit'.symm ▸ hHi)]
        exact (tau_core_not_event hc rfl hCore).elim
      | @ev _ _ mark _ _ h _ =>
        obtain ⟨loc,hKind,_⟩ := packetArrivalStepFrame (recurringPacketSite site) hExit' h
        refine ⟨mark,rfl,(estep_source_pc h).trans hExit',site,loc,?_⟩
        cases mark
        simp only [Event.mk.injEq]
        exact ⟨(estep_source_pc h).trans hExit', hKind⟩
      | last h =>
        rw [hSplit] at hIndex
        simp only [List.length_append,List.length_singleton] at hIndex
        omega
    obtain ⟨mark,hMark,hPc,hPub⟩ := hAt
    have hAt : events[pre.length]? = some mark := by
      rw [hSplit, List.getElem?_append_right (by rfl), Nat.sub_self]
      exact hMark
    exact hNoArrival pre.length (by omega) mark hAt hPc hPub
  rw [hSplit, List.getElem?_append_left hWithin] at hGet
  exact afterGuardQuiet site (eventInside route hPre hFront e (List.mem_of_getElem? hGet))

/-- An indexed event within a decoded slice bounds all earlier actual
events in the corresponding lane suffix to the same slice. -/
theorem beforeObservedSliceEvent {l : Launch} {X : Execution}
    {g start index lower stop : Nat} {s : TState} {visits : List Visit} {event : Event}
    (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop start) visits)
    (he : (loaderSliceEvents lower stop visits)[index-start]? = some event)
    {j : Nat} (hStart : start ≤ j) (hEarlier : j < index)
    {e : Event} (hGet : X.get (g,j) = some e) : e.pc < stop := by
  let pre := visits.takeWhile (fun v => lower ≤ v.pc && v.pc < stop)
  obtain ⟨rest,hSplit⟩ : pre <+: visits := List.takeWhile_prefix _
  have hBefore : j - start < (pre.filterMap Visit.ev).length :=
    lt_trans (by omega : j - start < index-start) (List.getElem?_eq_some_iff.mp he).1
  have hAt : ((X.tr g).drop start)[j-start]? = some e := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hStart]
  rw [hw.events, ← hSplit, List.filterMap_append, List.getElem?_append_left hBefore] at hAt
  obtain ⟨v,hv,hm⟩ := List.mem_filterMap.mp (List.mem_of_getElem? hAt)
  have hv' : v ∈ visits := hSplit ▸ List.mem_append_left _ hv
  have hPc := walkVisitIssuePc hw hv' hm
  have hIn := List.all_eq_true.mp List.all_takeWhile _ hv
  exact hPc ▸ (of_decide_eq_true (Bool.and_eq_true_iff.mp hIn).2 : v.pc < stop)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

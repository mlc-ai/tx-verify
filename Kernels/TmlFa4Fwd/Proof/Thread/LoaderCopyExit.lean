-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.LoaderCommittedPacket

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (copyPacketFirst copyCommitPc copyCommitCode loaderPacketBounds packetTauNext packetEventNext
    loaderOutCore packetArrivalStep actualCopyAtInLoader loaderCopyPcInPacket
    loaderPacketEventsNoCommit actualAsyncArrival)

private theorem packetArrivalOfWitness {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {visits : List Visit} (site : Fin 6)
    (ht : t.pc = copyCommitPc site + 1) (hw : Walk kernel Assumptions.all l g t es visits)
    {w : Event} (hWitness : w ∈ es)
    (hContinuing : ¬ Ends w ∨ w.pc ≠ copyCommitPc site + 1) :
    ∃ loc, es[0]? = some ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ := by
  have hLo : 174 ≤ copyCommitPc site + 1 := by fin_cases site <;> decide
  have hHi : copyCommitPc site + 1 < 1906 := by fin_cases site <;> decide
  cases hw with
  | stop => cases hWitness
  | @tau _ u _ _ h _ =>
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at *
      rwa [← loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event (ht.symm ▸ (copyCommitCode site).2) rfl hCore).elim
  | @ev _ _ e _ _ h _ =>
    obtain ⟨loc, hKind, _⟩ := packetArrivalStep site ht h
    have hPc := (estep_source_pc h).trans ht
    refine ⟨loc, ?_⟩
    cases e
    simp only [List.getElem?_cons_zero, Option.some.injEq, Event.mk.injEq]
    exact ⟨hPc, hKind⟩
  | last h =>
    obtain rfl := List.mem_singleton.mp hWitness
    have hPc := (estep_source_pc h).trans ht
    obtain ⟨_, _, hFire⟩ := h
    exact (hContinuing.resolve_left (not_not_intro (fires_none_ends hFire)) hPc).elim

/-- A terminating suffix at a packet publication issues that publication first. -/
theorem packetArrivalAtExit {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {visits : List Visit} (site : Fin 6)
    (ht : t.pc = copyCommitPc site + 1) (hw : Walk kernel Assumptions.all l g t es visits)
    (hExit : ⟨9205, .exit⟩ ∈ es) :
    ∃ loc, es[0]? = some ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ := by
  exact packetArrivalOfWitness site ht hw hExit
    (.inr (by fin_cases site <;> decide))

private theorem findsArrival {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {visits : List Visit} (site : Fin 6) (hw : Walk kernel Assumptions.all l g t es visits)
    (hLo : copyPacketFirst site ≤ t.pc) (hHi : t.pc ≤ copyCommitPc site)
    {j : Nat} {w : Event} (hWitness : es[j]? = some w)
    (hCrosses : (¬ (copyPacketFirst site ≤ w.pc ∧ w.pc ≤ copyCommitPc site)) ∨
      ∃ k < j, ∃ pc, es[k]? = some ⟨pc,.asyncCommit⟩)
    (hContinuing : ¬ Ends w ∨ w.pc ≠ copyCommitPc site + 1) :
    ∃ k loc, k + 1 ≤ j ∧ es[k]? = some ⟨copyCommitPc site, .asyncCommit⟩ ∧
      es[k + 1]? = some ⟨copyCommitPc site + 1, .asyncArrive loc true⟩ ∧
      ∀ j < k, ∀ e, es[j]? = some e → e.kind ≠ .asyncCommit := by
  have hRange := loaderPacketBounds site
  induction hw generalizing j with
  | stop => simp at hWitness
  | @tau t u es visits h hw ih =>
    by_cases hLess : t.pc < copyCommitPc site
    · have hNext := packetTauNext hLo hLess h
      exact ih (by omega) (by omega) hWitness hCrosses
    have ht : t.pc = copyCommitPc site := by omega
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at *
      rwa [← loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event (ht.symm ▸ (copyCommitCode site).1) rfl hCore).elim
  | @ev t u e es visits h hw ih =>
    have hPc := estep_source_pc h
    obtain _ | j := j
    · obtain rfl := Option.some.inj hWitness
      rcases hCrosses with hOutside | ⟨k,hK,_,_⟩
      · exact (hOutside ⟨by omega, by omega⟩).elim
      · omega
    have hTail : es[j]? = some w := hWitness
    by_cases hLess : t.pc < copyCommitPc site
    · have hNo := loaderPacketEventsNoCommit (site := site) (Walk.ev h hw) hLo e
        (by simp [visit,hLess])
      have hu : copyPacketFirst site ≤ u.pc ∧ u.pc ≤ copyCommitPc site := by
        rcases packetEventNext (by omega) (by omega) h with hNext | ⟨hNext,_⟩ <;> omega
      have hCrossTail : (¬ (copyPacketFirst site ≤ w.pc ∧ w.pc ≤ copyCommitPc site)) ∨
          ∃ k < j, ∃ pc, es[k]? = some ⟨pc,.asyncCommit⟩ := by
        rcases hCrosses with hOutside | ⟨k,hK,pc,hCommit⟩
        · exact .inl hOutside
        · cases k with
          | zero =>
            have hEvent := Option.some.inj hCommit
            exact (hNo (congrArg Event.kind hEvent)).elim
          | succ k =>
            exact .inr ⟨k,by omega,pc,hCommit⟩
      obtain ⟨k,loc,hK,hCommit,hArrival,hBefore⟩ := ih hu.1 hu.2 hTail hCrossTail
      refine ⟨k+1,loc,by omega,hCommit,hArrival,?_⟩
      intro j hj event he
      cases j with
      | zero => exact Option.some.inj he ▸ hNo
      | succ j => exact hBefore j (by omega) event he
    have hEq : t.pc = copyCommitPc site := by omega
    have hCore : EStep kernel [] l g t e (some u) := by
      obtain ⟨tmpl,hOut,hFire⟩ := h
      exact ⟨tmpl,by rwa [← loaderOutCore (by omega) (by omega)],hFire⟩
    obtain ⟨ins,hInsn,_,hFire⟩ := estep_event_source hCore
    rw [hEq,(copyCommitCode site).1] at hInsn
    obtain rfl := Option.some.inj hInsn
    simp only [eventTmpl,cpAsyncTmpl,Fires] at hFire
    have hAdvance : u.pc = t.pc + 1 := by
      rcases packetEventNext (by omega) (by omega) h with hAdvance | ⟨hStay,_⟩
      · exact hAdvance
      · have hU := Option.some.inj hFire.2
        simp [next,hU] at hStay
    obtain ⟨loc, hAt⟩ :=
      packetArrivalOfWitness site (by omega) hw (List.mem_of_getElem? hTail) hContinuing
    exact ⟨0,loc,by omega,by simp [hFire.1,hEq],hAt,by simp⟩
  | @last t e h =>
    have hPc := estep_source_pc h
    cases j with
    | zero =>
      obtain rfl := Option.some.inj hWitness
      rcases hCrosses with hOutside | ⟨k,hK,_,_⟩
      · exact (hOutside ⟨by omega, by omega⟩).elim
      · omega
    | succ j => simp at hWitness

variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
include hX

private theorem copyFirstPublicationBeforeWitness {g i j pc : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g,i) = some ⟨pc,.copy spec⟩) {w : Event} (hLater : X.get (g, j) = some w)
    (hOrder : i < j)
    (hCrosses : (∀ site, ¬ (copyPacketFirst site ≤ w.pc ∧ w.pc ≤ copyCommitPc site)) ∨
      ∃ k, i < k ∧ k < j ∧ ∃ pc, X.get (g,k) = some ⟨pc,.asyncCommit⟩)
    (hContinuing : ∀ site, ¬ Ends w ∨ w.pc ≠ copyCommitPc site + 1) :
    ∃ (site : Fin 6) (k : Nat) (loc : Loc), k ≤ j ∧
      copyPacketFirst site ≤ pc ∧ pc < copyCommitPc site ∧
      X.get (g,k) = some ⟨copyCommitPc site+1,.asyncArrive loc true⟩ ∧
      TracksCpAsync X (g, i) (g, k) ∧ i < k - 1 ∧
      ∀ n, i < n → n < k - 1 → ∀ e, X.get (g,n) = some e →
        e.kind ≠ .asyncCommit := by
  obtain ⟨hLo, hHi, hAt⟩ := actualCopyAtInLoader hX he
  obtain ⟨site, hFirst, hCommit⟩ := loaderCopyPcInPacket hLo hHi hAt
  have hJ : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hLater).1
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨t, u, hStep, hRun⟩ := hr.after_event he (by omega)
  have ht : t.pc = pc := (estep_source_pc hStep).symm
  have hu : u.pc = pc + 1 := by
    rcases packetEventNext (by omega) (by omega) hStep with hNext | ⟨_, hNo⟩
    · omega
    · rw [ht, hAt] at hNo
      cases hNo
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hRun
  have hGet : ((X.tr g).drop (i + 1))[j - (i + 1)]? = some w := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
  have hCrosses' : (¬ (copyPacketFirst site ≤ w.pc ∧ w.pc ≤ copyCommitPc site)) ∨
      ∃ k < j - (i+1), ∃ pc, ((X.tr g).drop (i+1))[k]? = some ⟨pc,.asyncCommit⟩ := by
    rcases hCrosses with hOutside | ⟨k,hi,hk,pc,hCommit⟩
    · exact .inl (hOutside site)
    · exact .inr ⟨k-(i+1),by omega,pc,by
        rwa [List.getElem?_drop,Nat.add_sub_of_le (by omega : i+1 ≤ k)]⟩
  obtain ⟨k, loc, hK, _, hReady, hNo⟩ :=
    findsArrival site hWalk (by omega) (by omega) hGet hCrosses' (hContinuing site)
  rw [List.getElem?_drop] at hReady
  let issue := i + 1 + (k + 1)
  have hPub : X.AsyncArrive (g, issue) loc true := ⟨_, hReady⟩
  have hCopy : X.Copy (g, i) spec := ⟨pc, he⟩
  refine ⟨site,issue,loc,by dsimp [issue]; omega,hFirst,hCommit,hReady,
    ⟨rfl, by dsimp [issue]; omega, ⟨spec,hCopy,(actualCopyShape hX hCopy).completion⟩,
      loc,true,hPub⟩, by dsimp [issue]; omega, ?_⟩
  intro n hn hBefore e hn'
  have hIndex : n - (i + 1) < k := by dsimp [issue] at hBefore; omega
  apply hNo _ hIndex e
  rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : i + 1 ≤ n)]
  exact hn'

/-- A later actual publication in the same lane supplies a finite suffix
that identifies the first publication tracking an ordinary copy. -/
theorem copyFirstPublicationBeforePublicationAtPacket {g i j pc : Nat} {spec : AsyncCopy.Spec}
    {target : Loc} (hCopy : X.get (g,i) = some ⟨pc,.copy spec⟩)
    (hLater : X.AsyncArrive (g, j) target true) (hOrder : i < j) :
    ∃ (site : Fin 6) (k : Nat) (loc : Loc), k ≤ j ∧
      copyPacketFirst site ≤ pc ∧ pc < copyCommitPc site ∧
      X.get (g,k) = some ⟨copyCommitPc site+1,.asyncArrive loc true⟩ ∧
      TracksCpAsync X (g, i) (g, k) ∧ i < k - 1 ∧
      ∀ n, i < n → n < k - 1 → ∀ e, X.get (g,n) = some e →
        e.kind ≠ .asyncCommit := by
  obtain ⟨pc, he⟩ := hLater
  obtain ⟨⟨actual, rfl⟩, _, _, _⟩ := actualAsyncArrival hX he
  apply copyFirstPublicationBeforeWitness hX hCopy he hOrder
  · apply Or.inl
    intro site
    change ¬ (copyPacketFirst site ≤ copyCommitPc actual + 1 ∧
      copyCommitPc actual + 1 ≤ copyCommitPc site)
    fin_cases actual <;> fin_cases site <;> decide
  · exact fun _ => .inl (by simp [Ends])

/-- A commit separating two actual copy issues forces the former packet's
publication before the later copy, even when its packet is still open. -/
theorem copyPublicationBeforeSeparatelyCommittedCopy {g i j pc qc : Nat} {a b : AsyncCopy.Spec}
    (ha : X.get (g,i) = some ⟨pc,.copy a⟩) (hb : X.get (g,j) = some ⟨qc,.copy b⟩) (hOrder : i < j)
    (hCommit : ∃ k, i < k ∧ k < j ∧ ∃ pc, X.get (g,k) = some ⟨pc,.asyncCommit⟩) :
    ∃ (site : Fin 6) (k : Nat) (loc : Loc), i < k ∧ k < j ∧
      pc < copyCommitPc site ∧
      X.get (g,k) = some ⟨copyCommitPc site+1,.asyncArrive loc true⟩ := by
  obtain ⟨site,k,loc,hk,_,hBefore,hPub,_,hAfter,_⟩ :=
    copyFirstPublicationBeforeWitness hX ha hb hOrder (.inr hCommit)
      (fun _ => .inl (by simp [Ends]))
  have hStrict : k < j := by
    by_contra! h
    obtain rfl : k = j := by omega
    have hEvent := Option.some.inj (hb.symm.trans hPub)
    exact Kind.noConfusion (congrArg Event.kind hEvent)
  exact ⟨site,k,loc,by omega,hStrict,hBefore,hPub⟩

/-- The first commit after a copy on an exited lane closes its actual publication. -/
theorem copyFirstPublicationAtExit {copy : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy copy spec)
    (hExit : Thread.Exited X copy.1) :
    ∃ (issue : EvId) (loc : Loc), issue.1 = copy.1 ∧ X.AsyncArrive issue loc true ∧
      TracksCpAsync X copy issue ∧ copy.2 < issue.2 - 1 ∧
      ∀ j, copy.2 < j → j < issue.2 - 1 → ∀ e, X.get (copy.1,j) = some e →
        e.kind ≠ .asyncCommit := by
  obtain ⟨g, i⟩ := copy
  obtain ⟨pc, he⟩ := hCopy
  obtain ⟨exitSite, hLast⟩ := hExit.lastEvent hX (event_thread_lt hX he)
  let finish := (X.tr g).length - 1
  have hLastGet : X.get (g, finish) = some ⟨exitSite, .exit⟩ := by
    change (X.tr g)[finish]? = _
    rwa [← List.getLast?_eq_getElem?]
  obtain rfl := actualExitPc hX hLastGet
  have hI := (List.getElem?_eq_some_iff.mp he).1
  have hF := (List.getElem?_eq_some_iff.mp hLastGet).1
  have hBefore : i < finish := by
    by_contra! h
    have hEq : i = finish := by dsimp [finish] at *; omega
    rw [hEq, hLastGet] at he
    cases he
  obtain ⟨_,k,loc,_,_,_,hPub,hTracked,hClose,hNo⟩ :=
    copyFirstPublicationBeforeWitness hX he hLastGet hBefore
      (.inl (by intro site; fin_cases site <;> decide))
      (by intro site; exact .inr (by fin_cases site <;> decide))
  exact ⟨(g,k),loc,rfl,⟨_,hPub⟩,hTracked,hClose,hNo⟩

/-- Every ordinary copy on an exited loader lane is tracked by an actual later publication. -/
theorem copyPublicationAtExit {copy : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy copy spec)
    (hExit : Thread.Exited X copy.1) :
    ∃ (issue : EvId) (loc : Loc), issue.1 = copy.1 ∧ X.AsyncArrive issue loc true ∧
      TracksCpAsync X copy issue := by
  obtain ⟨issue,loc,hLane,hPub,hTracks,_,_⟩ := copyFirstPublicationAtExit hX hCopy hExit
  exact ⟨issue,loc,hLane,hPub,hTracks⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseOrdinal
import Kernels.TmlFa4Fwd.Proof.MmaLoopRank
import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem continuingRoleEvent {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : 1907 ≤ s.pc ∧ s.pc < 2768) (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    {j : Nat} {e : Event} (he : events[j]? = some e)
    (hLate : j + 1 < events.length) (hBound : e.pc < 2768) :
    ∃ t u post, RoleShape t ∧ EStep kernel Assumptions.all l g t e (some u) ∧
      Walk kernel Assumptions.all l g u (events.drop (j + 1)) post := by
  have hContrary {v : TState} {tail : List Event} {post : List Visit}
      (hExit : v.pc ∈ [3099] ∧ v.fault = none) (hRole : v.regs 1062 = some (b32 12))
      (hWalk : Walk kernel Assumptions.all l g v tail post) (hIn : e ∈ tail) : False := by
    have hEnd := mmaEpilogueExitEvents (by simpa using hExit.1) hExit.2 (.inl rfl)
      hRole hWalk e hIn
    omega
  induction hw generalizing j with
  | stop => simp at he
  | tau hTau hTail ih =>
    obtain ⟨hNext | hExit, hState⟩ :=
      mmaCutStep hPc.1 hPc.2 (.inl ⟨rfl, hTau⟩) hShape
    · exact ih hNext hState he hLate
    · exact (hContrary hExit hState.2 hTail (List.mem_of_getElem? he)).elim
  | @ev t u en tail trail hStep hTail ih =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      exact ⟨_, _, _, hShape.1, hStep, hTail⟩
    | succ j =>
      have hGet : tail[j]? = some e := he
      obtain ⟨hNext | hExit, hState⟩ :=
        mmaCutStep hPc.1 hPc.2 (.inr ⟨_, rfl, hStep⟩) hShape
      · exact ih hNext hState hGet (by simp at hLate; omega)
      · exact (hContrary hExit hState.2 hTail (List.mem_of_getElem? hGet)).elim
  | last => simp at hLate

private theorem noFaultOfReturn {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u)) : s.fault = none := by
  cases h : s.fault
  · rfl
  · obtain ⟨tm, hOut, hf⟩ := he
    simp only [out, h, Out.ev.injEq] at hOut
    subst tm
    cases hf.2

private theorem reachedCommit {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (i : Fin 12) (hs : At s (commitSite i).pc [])
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ spec : TcCommit.Spec, e = ⟨(commitSite i).pc, .tc (.commit spec)⟩ := by
  have hCode := commitCode i
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [hs.1, hCode] at hc
  obtain rfl := Option.some.inj hc.symm
  simp only [eventTmpl, tcCommitTmpl] at hf
  by_cases hg : g < l.threads
  · simp only [hg, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hf
    cases hLoc : mbarClusterLoc l g s (commitSite i).base ((commitSite i).off : Int) with
    | error fault => simp [hLoc, ofExec, Fires] at hf
    | ok loc =>
      simp only [hLoc] at hf
      cases hResolve : TcCommit.resolve l .one (g / l.block) loc
          (BitVec.ofNat 16 (2 ^ l.rankOfCta loc.cta)) with
      | none => simp [hResolve, ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
      | some spec =>
        simp only [hResolve, ofExec, Fires] at hf
        exact ⟨spec, hf.1.trans (congrArg (fun pc => (⟨pc, .tc (.commit spec)⟩ : Event)) hs.1)⟩
  · simp [hg, ofExec, Fires, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hf

private theorem reachedCommitFault {l : Launch} {g : Nat} {s : TState} {e : Event}
    (i : Fin 12) (hs : At s (commitSite i).pc [])
    (he : EStep kernel Assumptions.all l g s e none) :
    ∃ fault, e = ⟨(commitSite i).pc,.ub fault⟩ := by
  have hRange : 1904 ≤ (commitSite i).pc ∧ (commitSite i).pc < 2768 := by
    fin_cases i <;> decide
  have hCore := out_eq_core (hs.1.symm ▸ hRange.1) (hs.1.symm ▸ hRange.2)
    (l := l) (g := g) (t := s)
  obtain ⟨tm,hOut,hf⟩ := he
  rw [hCore] at hOut
  have hTmpl : out kernel [] l g s =
      .ev (eventTmpl [] l g s
        (.tcCommit .one (commitSite i).base ((commitSite i).off : Int) none)) := by
    simp [out,hs.1,hs.2.2.2.1,commitCode i,guardHolds,Op.isLocal,pure,Except.pure]
  obtain rfl := Out.ev.inj (hOut.symm.trans hTmpl)
  simp only [eventTmpl, tcCommitTmpl] at hf
  by_cases hg : g < l.threads
  · simp only [hg, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hf
    cases hLoc : mbarClusterLoc l g s (commitSite i).base ((commitSite i).off : Int) with
    | error fault =>
      simp only [hLoc, ofExec, Fires] at hf
      exact ⟨fault,by simpa only [hs.1] using hf.1⟩
    | ok loc =>
      simp only [hLoc] at hf
      cases hResolve : TcCommit.resolve l .one (g / l.block) loc
          (BitVec.ofNat 16 (2 ^ l.rankOfCta loc.cta)) with
      | none =>
        simp only [hResolve, ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
        exact ⟨.badValue,by simpa only [hs.1] using hf.1⟩
      | some spec => simp [hResolve, ofExec, Fires] at hf
  · simp only [hg, ↓reduceIte, ofExec, Fires, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at hf
    exact ⟨.badValue,by simpa only [hs.1] using hf.1⟩

/-- The elected issuer's next event is its commit or an undefined terminal event. -/
theorem electedCommitOccursOrFault {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 12) {g j inst leader : Nat}
    (he : X.Elect (g, j) (electSite (commitElection i)).pc (2 ^ 32 - 1) inst leader)
    (hLead : laneOf l g = leader) (hCont : j + 1 < (X.tr g).length) :
    (∃ spec : TcCommit.Spec, X.get (g, j + 1) =
      some ⟨(commitSite i).pc, .tc (.commit spec)⟩) ∨
    ((X.tr g).length = j+2 ∧ ∃ fault, X.get (g,j+1) = some ⟨(commitSite i).pc,.ub fault⟩) := by
  let site := electSite (commitElection i)
  let e : Event := ⟨site.pc, .elect (2 ^ 32 - 1) inst leader⟩
  have heGet : X.get (g, j) = some e := he
  have hBounds : 2145 ≤ site.pc ∧ site.pc < 2768 := by fin_cases i <;> decide
  obtain ⟨t, vs, _, hj, _, ht, hw⟩ := releaseBody hp hX heGet hBounds.1 hBounds.2
  have hBefore : ((X.tr g).drop 6)[j - 6]? = some e := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le hj]
  have hSize : j - 6 + 1 < ((X.tr g).drop 6).length := by
    rw [List.length_drop]
    omega
  obtain ⟨s, u, post, hShape, hStep, hTail⟩ := continuingRoleEvent hw
    (by rw [ht.1]; decide) ⟨⟨by rw [ht.2.1]; decide, ht.2.2.1, fun _ => ht.2.1⟩,
      ht.2.2.2.2.1⟩ hBefore (by omega) hBounds.2
  have hSite : s.pc = site.pc := (estep_source_pc hStep).symm
  have hs : At s site.pc [] :=
    ⟨hSite, hShape.2.2 (by omega), hShape.2.1, noFaultOfReturn hStep, trivial⟩
  have hOut := electTemplate (l := l) (g := g) (commitElection i) hs
  obtain ⟨tm, hTm, hf⟩ := hStep
  rw [hOut] at hTm
  obtain rfl := Out.ev.inj hTm.symm
  obtain ⟨vote, lead, hEvent, hU⟩ := hf
  have hSame : lead = leader := (Kind.elect.inj (congrArg Event.kind hEvent)).2.2.symm
  subst lead
  obtain rfl := Option.some.inj hU
  have hStart := electStateFrame (l := l) (g := g) (commitElection i) hs leader (by simp) (by simp)
  rw [beq_iff_eq.mpr hLead] at hStart
  obtain ⟨v, hGate, hv⟩ := commitGate i true hStart (by simp)
  have hDrop : ((X.tr g).drop 6).drop (j - 6 + 1) = (X.tr g).drop (j + 1) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hDrop] at hTail
  have hAfter : 0 < ((X.tr g).drop (j + 1)).length := by rw [List.length_drop]; omega
  rcases advanceWalkLocals hGate hTail with hNil | ⟨pVisits, _, _, hWalk⟩
  · simp [hNil] at hAfter
  have hRange : 1904 ≤ (commitSite i).pc ∧ (commitSite i).pc < 2768 := by
    fin_cases i <;> decide
  have hCode := commitCode i
  have hPc : v.pc = (commitSite i).pc := hv.1
  have hCore := out_eq_core (hPc.symm ▸ hRange.1) (hPc.symm ▸ hRange.2)
    (l := l) (g := g) (t := v)
  generalize hEvents : (X.tr g).drop (j + 1) = tail at hWalk hAfter
  cases hWalk with
  | stop => simp at hAfter
  | tau ht _ =>
    unfold Tau at ht
    rw [hCore] at ht
    have hc : kernel.code[v.pc]? =
        some ⟨none, .tcCommit .one (commitSite i).base ((commitSite i).off : Int) none⟩ := by
      rw [hPc]
      exact hCode
    exact (tau_core_not_event hc rfl ht).elim
  | last hStep =>
    obtain ⟨fault,rfl⟩ := reachedCommitFault i hv hStep
    have hLen := congrArg List.length hEvents
    rw [List.length_drop] at hLen
    refine .inr ⟨by simp at hLen; omega, fault,?_⟩
    change (X.tr g)[j + 1]? = _
    rw [← Nat.add_zero (j + 1), ← List.getElem?_drop, hEvents, List.getElem?_cons_zero]
  | ev hStep _ =>
    obtain ⟨spec, rfl⟩ := reachedCommit i hv hStep
    refine .inl ⟨spec, ?_⟩
    change (X.tr g)[j + 1]? = _
    rw [← Nat.add_zero (j + 1), ← List.getElem?_drop, hEvents, List.getElem?_cons_zero]

/-- A continuing elected issuer executes the commit immediately after its election. -/
theorem electedCommitOccurs {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (i : Fin 12) {g j inst leader : Nat}
    (he : X.Elect (g,j) (electSite (commitElection i)).pc (2^32-1) inst leader)
    (hLead : laneOf l g = leader) (hCont : j+2 < (X.tr g).length) :
    ∃ spec : TcCommit.Spec, X.get (g,j+1) =
      some ⟨(commitSite i).pc,.tc (.commit spec)⟩ := by
  rcases electedCommitOccursOrFault hp hX i he hLead (by omega) with h | ⟨hLen,_⟩
  · exact h
  · omega

/-- A recurring K release on the actual elected lane follows both score commits
of that same visit. -/
theorem ReleaseIssue.recurringScoreCommit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {spec : TcCommit.Spec} (hRelease : ReleaseIssue X g index .loopKey spec)
    (stage : Fin 2) :
    let block : Fin 4 := if stage = 0 then 2 else 3
    ∃ (commit : Nat) (s : TcCommit.Spec), TraceBefore X (g, commit) (g, index) ∧
      X.get (g, commit) = some ⟨(commitSite (qkCommitSite block)).pc, .tc (.commit s)⟩ ∧
      PTX.Kernels.TmlFa4Fwd.Thread.Mma.readyOccurrence X g (commit - 1) .loopKey =
        1 + releaseOccurrence X g index .loopKey ∧
      ElectOrd.siteOrdinal (· == (electSite (commitElection (qkCommitSite block))).pc)
        X g (commit - 1) = releaseOccurrence X g index .loopKey := by
  dsimp only
  obtain ⟨hIndex, inst, leader, he, hLead⟩ := readyReleaseLeader hp hX 2 hRelease
  obtain ⟨j, hj, vote, hVote, hRank⟩ := recurringKeyScoreElectionBeforeRelease hp hX stage he
  have hLen : index < (X.tr g).length := len_of_get hRelease
  obtain ⟨commit, hCommit⟩ := electedCommitOccurs hp hX
    (qkCommitSite (if stage = 0 then 2 else 3)) hVote hLead (by omega)
  have hReady := recurringKeyReadyAtScoreElection hp hX stage hVote
  rw [hRank] at hReady
  exact ⟨j + 1, commit, ⟨rfl, by omega, hLen⟩, hCommit, hReady, hRank⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma

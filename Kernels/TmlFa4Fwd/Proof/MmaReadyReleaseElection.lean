-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaCommitGate
public import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
public import Kernels.TmlFa4Fwd.Proof.MmaQkCommit
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Lemmas.Order.ElectOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.AsyncCopy

noncomputable section

/-- The terminal commit that releases one of the two query input stages. -/
def queryReleaseSite (stage : Fin 2) : Fin 12 := if stage = 0 then 7 else 8

private inductive CommitGateKind
  | release (site : Fin 4)
  | score (block : Fin 4)
  | queryRelease (stage : Fin 2)
  | firstOutput
  | secondOutput

private def CommitGateKind.site : CommitGateKind → Fin 12
  | .release site => releaseCommitSite site
  | .score block => qkCommitSite block
  | .queryRelease stage => queryReleaseSite stage
  | .firstOutput => 10
  | .secondOutput => 11

private def releaseElect (i : CommitGateKind) : Fin 20 := commitElection i.site
private def releaseElectPc (i : CommitGateKind) : Nat := (electSite (releaseElect i)).pc
private def releaseCommitPc (i : CommitGateKind) : Nat := (commitSite i.site).pc

private theorem releaseWindow (i : CommitGateKind) :
    2145 ≤ releaseElectPc i ∧ releaseCommitPc i = releaseElectPc i + 3 ∧
      releaseCommitPc i < 2768 := by
  cases i with
  | firstOutput => decide
  | secondOutput => decide
  | release i => fin_cases i <;> decide
  | score i => fin_cases i <;> decide
  | queryRelease i => fin_cases i <;> decide

private def gateInterior (i : CommitGateKind) (pc : Nat) : Prop :=
  releaseElectPc i < pc ∧ pc ≤ releaseCommitPc i

private instance (i : CommitGateKind) (pc : Nat) : Decidable (gateInterior i pc) :=
  inferInstanceAs (Decidable (releaseElectPc i < pc ∧ pc ≤ releaseCommitPc i))

private def gateEntryCode (i : CommitGateKind) (pc : Nat) (ins : Instr) : Bool :=
  (match ins.op with
    | .bra target _ => !decide (gateInterior i target)
    | .brx .. => false
    | _ => true) &&
    (!decide (gateInterior i pc ∧ pc < releaseCommitPc i) || ins.op.isLocal) &&
    (!decide (gateInterior i pc) || !allocationOp ins.op) &&
    (ins.op.isLocal || linearEventOp ins.op)

private theorem gateEntryChecked (i : CommitGateKind) {pc : Nat} {ins : Instr}
    (hLo : 1907 ≤ pc) (hHi : pc < 2768) (hc : kernel.code[pc]? = some ins) :
    gateEntryCode i pc ins = true := by
  let code := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907
  have h : code.all (fun pair => gateEntryCode i pair.2 pair.1) = true := by
    cases i with
    | firstOutput => set_option maxRecDepth 100000 in kernel_rfl
    | secondOutput => set_option maxRecDepth 100000 in kernel_rfl
    | release i => fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
    | score i => fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
    | queryRelease i => fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h (ins, pc)
  apply List.mem_of_getElem? (i := pc - 1907)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def GateHistory (l : Launch) (g : Nat) (i : CommitGateKind) (s : TState)
    (prior : Option Event) : Prop :=
  gateInterior i s.pc → s.fault = none →
    ∃ inst leader, prior = some ⟨releaseElectPc i, .elect (2 ^ 32 - 1) inst leader⟩ ∧
      (laneOf l g = leader ∨ ∃ exit,
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) s exit ∧
        exit.pc = releaseCommitPc i + 1)

private theorem releaseAt {s : TState}
    (i : CommitGateKind) (hs : RoleShape s) (hf : s.fault = none) (hPc : s.pc = releaseElectPc i) :
    At s (electSite (releaseElect i)).pc [] := by
  have hWindow := releaseWindow i
  exact ⟨hPc, hs.2.2 (by omega), hs.2.1, hf, trivial⟩

private theorem gateHistoryTau {l : Launch} {g : Nat} {s u : TState} {prior : Option Event}
    (i : CommitGateKind) (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hs : RoleShape s) (ht : Tau kernel Assumptions.all l g s u)
    (hGate : GateHistory l g i s prior) : GateHistory l g i u prior := by
  intro hu _
  obtain ⟨ins, hc, hf, _⟩ := Softmax.tauScoreSource ht
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← out_eq_core (by omega) hPc.2]
  have hKeep (hp : u.pc = s.pc + 1) : ∃ inst leader,
      prior = some ⟨releaseElectPc i, .elect (2 ^ 32 - 1) inst leader⟩ ∧
        (laneOf l g = leader ∨ ∃ exit,
          Relation.ReflTransGen (Tau kernel Assumptions.all l g) u exit ∧
          exit.pc = releaseCommitPc i + 1) := by
    have hWindow := releaseWindow i
    have hReady : releaseElectPc i ≤ s.pc ∧ s.pc < releaseCommitPc i := by
      have := hu.1
      have := hu.2
      omega
    by_cases hb : s.pc = releaseElectPc i
    · have hOut := electTemplate (l := l) (g := g) (releaseElect i) (releaseAt i hs hf hb)
      rw [Tau, hOut] at ht
      cases ht
    · obtain ⟨inst, leader, hEvent, hLane | ⟨exit, hSteps, hExit⟩⟩ :=
        hGate ⟨by omega, hReady.2.le⟩ hf
      · exact ⟨inst, leader, hEvent, .inl hLane⟩
      · rcases Relation.ReflTransGen.cases_head hSteps with hEq | ⟨v, hTau, hRest⟩
        · subst exit
          omega
        · obtain rfl := tau_det hTau ht
          exact ⟨inst, leader, hEvent, .inr ⟨exit, hRest, hExit⟩⟩
  have hCode := gateEntryChecked i hPc.1 hPc.2 hc
  simp only [gateEntryCode, Bool.and_eq_true] at hCode
  rcases tau_core_frame hc ht' with rfl | h
  · exact hKeep rfl
  have hp := h.pc
  cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hp
  case bra target aligned =>
    have hB : ¬ gateInterior i target := by simpa [ho] using hCode.1.1.1
    exact (hB (hp ▸ hu)).elim
  case brx => simp [ho] at hCode
  all_goals exact hKeep hp

private theorem gateHistoryEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (i : CommitGateKind) (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hs : RoleShape s) (he : EStep kernel Assumptions.all l g s e (some u)) :
    GateHistory l g i u (some e) := by
  intro hU hfU
  obtain ⟨ins, hc, hl, _⟩ := estep_event_source he
  have hCode := gateEntryChecked i hPc.1 hPc.2 hc
  simp only [gateEntryCode, Bool.and_eq_true] at hCode
  have hLinear : linearEventOp ins.op = true := by simpa [hl] using hCode.2
  have hF : s.fault = none := by
    cases h : s.fault
    · rfl
    · obtain ⟨tm, hOut, hf⟩ := he
      simp only [out, h, Out.ev.injEq] at hOut
      subst tm
      cases hf.2
  have hp : u.pc = s.pc + 1 := by
    rcases (linearEventProgressWithSub hc hLinear hs.1 hs.2.1 he).2.2 with h | h | h
    · exact h.1
    · have hInterior : gateInterior i s.pc := h.1 ▸ hU
      have hNo : allocationOp ins.op = false := by simpa [hInterior] using hCode.1.2
      exact Bool.noConfusion (hNo.symm.trans h.2.2.2)
    · simp [hfU] at h
  have hBefore : releaseElectPc i ≤ s.pc ∧ s.pc < releaseCommitPc i := by
    have := hU.1
    have := hU.2
    omega
  have hHead : s.pc = releaseElectPc i := by
    by_contra hNe
    have hMiddle : gateInterior i s.pc ∧ s.pc < releaseCommitPc i :=
      ⟨⟨by omega, hBefore.2.le⟩, hBefore.2⟩
    have hLocal : ins.op.isLocal = true := by simpa [hMiddle] using hCode.1.1.2
    exact Bool.noConfusion (hl.symm.trans hLocal)
  have hOut := electTemplate (l := l) (g := g) (releaseElect i) (releaseAt i hs hF hHead)
  obtain ⟨tm, hTm, hFire⟩ := he
  rw [hOut] at hTm
  obtain rfl := Out.ev.inj hTm.symm
  obtain ⟨inst, leader, rfl, hNext⟩ := hFire
  obtain rfl := Option.some.inj hNext
  refine ⟨inst, leader, by rw [hHead], ?_⟩
  by_cases hLane : laneOf l g = leader
  · exact .inl hLane
  have hAt := electStateFrame (l := l) (g := g) (releaseElect i)
    (releaseAt i hs hF hHead) leader (by simp) (by simp)
  rw [beq_eq_false_iff_ne.mpr hLane] at hAt
  obtain ⟨exit, hRun, hExit⟩ := commitGate i.site false hAt (by simp)
  exact .inr ⟨exit, run_rtg hRun, hExit.1⟩

private theorem releaseEventNonfault {l : Launch} {g : Nat} {s : TState}
    {es : Event} {u : Option TState} {spec : TcCommit.Spec} {pc : Nat}
    (he : EStep kernel Assumptions.all l g s es u) (hKind : es = ⟨pc, .tc (.commit spec)⟩) :
    s.fault = none := by
  by_cases h : s.fault = none
  · exact h
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp h
  obtain ⟨tm, hOut, hFire⟩ := he
  simp only [out, hf, Out.ev.injEq] at hOut
  subst tm
  have h := congrArg Event.kind hFire.1
  rw [hKind] at h
  cases h

private theorem electionPrecedesReleaseInWalk {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {prior : Option Event} (i : CommitGateKind)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hs : RoleShape s ∧ s.regs 1062 = some (b32 12)) (hGate : GateHistory l g i s prior)
    {index : Nat} {spec : TcCommit.Spec}
    (he : es[index]? = some ⟨releaseCommitPc i, .tc (.commit spec)⟩) :
    ∃ inst leader, (if index = 0 then prior else es[index - 1]?) =
      some ⟨releaseElectPc i, .elect (2 ^ 32 - 1) inst leader⟩ ∧ laneOf l g = leader := by
  have current {t : TState} {e : Event} {u : Option TState} {previous : Option Event}
      (hStep : EStep kernel Assumptions.all l g t e u)
      (hEvent : e = ⟨releaseCommitPc i, .tc (.commit spec)⟩)
      (hg : GateHistory l g i t previous) : ∃ inst leader,
        previous = some ⟨releaseElectPc i, .elect (2 ^ 32 - 1) inst leader⟩ ∧
        laneOf l g = leader := by
    have hb := releaseWindow i
    have hP := estep_source_pc hStep
    rw [hEvent] at hP
    change releaseCommitPc i = t.pc at hP
    obtain ⟨inst, leader, hPrior, hLane | ⟨exit, hSteps, hExit⟩⟩ :=
      hg ⟨by omega, by omega⟩ (releaseEventNonfault hStep hEvent)
    · exact ⟨inst, leader, hPrior, hLane⟩
    · rcases Relation.ReflTransGen.cases_head hSteps with hEq | ⟨_, hTau, _⟩
      · subst exit
        omega
      · exact (not_tau_of_stops (stops_of_estep hStep) hTau).elim
  induction hw generalizing index prior with
  | stop => simp at he
  | tau ht hw ih =>
    obtain ⟨hW | ⟨hExit, hF⟩, hState⟩ := mmaCutStep hPc.1 hPc.2 (.inl ⟨rfl, ht⟩) hs
    · exact ih hW hState (gateHistoryTau i hPc hs.1 ht hGate) he
    · have hAt := List.mem_of_getElem? he
      have hTail := mmaEpilogueExitEvents (by simpa using hExit) hF (.inl rfl) hState.2 hw _ hAt
      have hWindow := releaseWindow i
      change releaseCommitPc i = 9205 at hTail
      omega
  | @ev t u e es vs hStep hw ih =>
    cases index with
    | zero =>
      simpa only [↓reduceIte] using current hStep (Option.some.inj he) hGate
    | succ index =>
      rw [List.getElem?_cons_succ] at he
      obtain ⟨hW | ⟨hExit, hF⟩, hState⟩ :=
        mmaCutStep hPc.1 hPc.2 (.inr ⟨_, rfl, hStep⟩) hs
      · obtain ⟨inst, leader, hEq, hLane⟩ :=
          ih hW hState (gateHistoryEvent i hPc hs.1 hStep) he
        cases index <;> exact ⟨inst, leader, hEq, hLane⟩
      · have hAt := List.mem_of_getElem? he
        have hTail := mmaEpilogueExitEvents (by simpa using hExit) hF (.inl rfl) hState.2 hw _ hAt
        have hWindow := releaseWindow i
        change releaseCommitPc i = 9205 at hTail
        omega
  | last hStep =>
    cases index with
    | zero => simpa only [↓reduceIte] using current hStep (Option.some.inj he) hGate
    | succ index => simp at he

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem commitGatedLeader (i : CommitGateKind) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨releaseCommitPc i, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader,
      X.Elect (g, index - 1) (releaseElectPc i) (2 ^ 32 - 1) inst leader ∧
      laneOf l g = leader := by
  have hWindow := releaseWindow i
  change X.get (g, index) = some ⟨releaseCommitPc i, .tc (.commit spec)⟩ at he
  obtain ⟨pos, t, visits, hPos, ht, hWalk⟩ := initialMmaTrace hp hX he
    (by dsimp; omega) (by dsimp; omega)
  have hPc : 1907 ≤ t.pc ∧ t.pc < 2768 := by rw [ht.1]; decide
  have hSh : RoleShape t := ⟨by rw [ht.2.1]; decide, ht.2.2.1, fun _ => ht.2.1⟩
  have hGate : GateHistory l g i t none := by
    intro h _
    rw [ht.1] at h
    have := h.1
    omega
  have hGet : ((X.tr g).drop (pos + 1))[index - (pos + 1)]? =
      some ⟨releaseCommitPc i, .tc (.commit spec)⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨inst, leader, hPrev, hLane⟩ :=
    electionPrecedesReleaseInWalk i hWalk hPc ⟨hSh, ht.2.2.2.2.1⟩ hGate hGet
  have hI : index - (pos + 1) ≠ 0 := by
    intro h
    simp [h] at hPrev
  rw [ite_eq_right hI, List.getElem?_drop] at hPrev
  have hEq : pos + 1 + (index - (pos + 1) - 1) = index - 1 := by omega
  rw [hEq] at hPrev
  exact ⟨by omega, inst, leader, hPrev, hLane⟩

/-- The terminal query release comes from the warp-wide elected lane. -/
theorem queryReleaseLeader (stage : Fin 2) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨(commitSite (queryReleaseSite stage)).pc, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader,
      X.Elect (g, index - 1) (electSite (commitElection (queryReleaseSite stage))).pc
        (2 ^ 32 - 1) inst leader ∧ laneOf l g = leader :=
  commitGatedLeader hp hX (.queryRelease stage) he

/-- Each actual release is issued by the lane elected in the immediately preceding event. -/
theorem readyReleaseLeader (i : Fin 4) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨(commitSite (releaseCommitSite i)).pc, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader, X.Elect (g, index - 1) (electSite (commitElection
      (releaseCommitSite i))).pc (2 ^ 32 - 1) inst leader ∧ laneOf l g = leader :=
  commitGatedLeader hp hX (.release i) he

/-- An actual score-ready commit is issued by the lane of its immediately preceding election. -/
theorem scoreCommitLeader (block : Fin 4) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨(commitSite (qkCommitSite block)).pc, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader, X.Elect (g, index - 1) (electSite (commitElection
      (qkCommitSite block))).pc (2 ^ 32 - 1) inst leader ∧ laneOf l g = leader :=
  commitGatedLeader hp hX (.score block) he

/-- The first output completion commit was issued by its full-warp elected MMA lane. -/
theorem firstOutputCommitLeader {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2642, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader, X.Elect (g, index - 1) 2639 (2 ^ 32 - 1) inst leader ∧
      laneOf l g = leader :=
  commitGatedLeader hp hX .firstOutput he

/-- The second output completion commit was issued by its full-warp elected MMA lane. -/
theorem secondOutputCommitLeader {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨2646, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader, X.Elect (g, index - 1) 2643 (2 ^ 32 - 1) inst leader ∧
      laneOf l g = leader :=
  commitGatedLeader hp hX .secondOutput he

/-- Each actual release is immediately preceded in its lane trace by its full-warp election. -/
theorem readyReleaseElection (i : Fin 4) {g index : Nat} {spec : TcCommit.Spec}
    (he : X.get (g, index) = some ⟨(commitSite (releaseCommitSite i)).pc, .tc (.commit spec)⟩) :
    0 < index ∧ ∃ inst leader, X.Elect (g, index - 1) (electSite (commitElection
      (releaseCommitSite i))).pc (2 ^ 32 - 1) inst leader := by
  obtain ⟨hIndex, inst, leader, hElect, _⟩ := readyReleaseLeader hp hX i he
  exact ⟨hIndex, inst, leader, hElect⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma

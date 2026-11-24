-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcReadFinishMma
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Lemmas.Flow.WarpUniform
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Lemmas.Flow.ElectActor
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotTcShift

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private inductive IssueBank where
  | query (block : Fin 4)
  | value (block : Fin 4)

private def IssueBank.election : IssueBank → Fin 20
  | .query i => #v[0, 2, 6, 10][i]
  | .value i => #v[5, 8, 15, 16][i]

private def IssueBank.gate (b : IssueBank) : Nat := (electSite b.election).pc

private def IssueBank.guard (b : IssueBank) : Nat := (electSite b.election).pred

private def IssueBank.site : IssueBank → Fin 8 → Nat
  | .query b, frag => qkPc b + frag.val
  | .value b, frag => pvPc b frag

private def IssueBank.inGate (b : IssueBank) (site : Nat) : Prop :=
  b.gate < site ∧ site ≤ b.site 7

private instance (b : IssueBank) (site : Nat) : Decidable (b.inGate site) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem issueGateLower (b : IssueBank) : 1910 ≤ b.gate := by
  cases b <;> decide +revert

private theorem issueInGate (b : IssueBank) (f : Fin 8) :
    b.inGate (b.site f) ∧ 2145 ≤ b.site f ∧ b.site f < 2768 := by
  cases b <;> decide +revert +kernel

private def issueGateCode (b : IssueBank) (site : Nat) (i : Instr) : Bool :=
  (!decide (b.inGate site) || !(mmaWrites i.op).contains b.guard) &&
  match i.op with
  | .bra dst _ => !decide (b.inGate dst) || decide (b.inGate site)
  | .brx .. => false
  | _ => true

private def issueBand := ((kernel.code.drop 1907).take (2768 - 1907)).zipIdx 1907

set_option maxRecDepth 100000 in
private theorem issueGateAudit (b : IssueBank) :
    issueBand.all (fun (i, site) => issueGateCode b site i) = true := by
  cases b <;> decide +revert +kernel

private theorem issueGateAt (b : IssueBank) {site : Nat} {i : Instr}
    (hLo : 1907 ≤ site) (hHi : site < 2768) (hCode : kernel.code[site]? = some i) :
    issueGateCode b site i = true := by
  apply List.all_eq_true.mp (issueGateAudit b) (i, site)
  apply List.mem_of_getElem? (i := site - 1907)
  dsimp only [issueBand]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hCode]
  rfl

private theorem gateBranch (b : IssueBank) {s d : Nat} {p : Option (Nat × Bool)} {a : Bool}
    (hCode : issueGateCode b s ⟨p, .bra d a⟩ = true) (hd : b.inGate d) : b.inGate s := by
  simpa [issueGateCode, hd] using (Bool.and_eq_true_iff.mp hCode).2

private def Election (b : IssueBank) (inst leader : Nat) : Event :=
  ⟨b.gate, .elect (2 ^ 32 - 1) inst leader⟩

private def GateFrame (l : Launch) (g : Nat) (b : IssueBank) (past : List Event)
    (s : TState) : Prop :=
  b.inGate s.pc → ∃ inst leader, Election b inst leader ∈ past ∧
    s.regs b.guard = some (.pred (laneOf l g == leader))

variable {l : Launch}

private theorem gateFramePreserved {g : Nat} {s u : TState} {e : Option Event} {past : List Event}
    {b : IssueBank} (hRange : 1907 ≤ s.pc ∧ s.pc < 2768) (hShape : RoleShape s)
    (hFrame : GateFrame l g b past s) (hStep : WStep kernel Assumptions.all l g s e u) :
    GateFrame l g b (e.toList ++ past) u := by
  intro hNew
  have hCore : out kernel Assumptions.all l g s = out kernel [] l g s :=
    out_eq_core (by omega) hRange.2
  have carry (hOld : b.inGate s.pc) : ∃ inst leader, Election b inst leader ∈ e.toList ++ past ∧
      u.regs b.guard = some (.pred (laneOf l g == leader)) := by
    obtain ⟨inst, leader, hPrev, hReg⟩ := hFrame hOld
    have hKeep := mmaStepReg (r := b.guard) (by omega) hRange.2 (fun _ hc => by
      have hAudit := (Bool.and_eq_true_iff.mp (issueGateAt b hRange.1 hRange.2 hc)).1
      simpa [hOld] using hAudit) hStep
    exact ⟨inst, leader, List.mem_append_right _ hPrev, hKeep.trans hReg⟩
  have earlier (hPc : u.pc = s.pc + 1) (hne : s.pc ≠ b.gate) : b.inGate s.pc := by
    unfold IssueBank.inGate at hNew ⊢
    omega
  rcases hStep with ⟨rfl, hTau⟩ | ⟨ev, rfl, he⟩
  · have hTauCore : Tau kernel [] l g s u := by
      unfold Tau at hTau ⊢
      rwa [← hCore]
    obtain ⟨i, hc⟩ := tau_core_has_code hTauCore
    have hNormal : s.fault = none := by
      cases hf : s.fault <;> simp_all [Tau, out]
    have hNonElection : s.pc ≠ b.gate := by
      intro h
      have hAt : At s b.gate [] :=
        ⟨h, hShape.2.2 (by have := issueGateLower b; omega), hShape.2.1, hNormal, trivial⟩
      have ho := electTemplate (l := l) (g := g) b.election hAt
      rw [Tau, ho] at hTau
      cases hTau
    have hOld : b.inGate s.pc := by
      rcases tau_core_frame hc hTauCore with rfl | hf
      · exact earlier rfl hNonElection
      have hNext := hf.pc
      have hAudit := issueGateAt b hRange.1 hRange.2 hc
      cases i with
      | mk pred op =>
        cases op <;> simp only [nextPc, BrxTarget, or_false] at hNext
        case bra dst aligned => exact gateBranch b hAudit (hNext ▸ hNew)
        case brx => simp [issueGateCode] at hAudit
        all_goals exact earlier hNext hNonElection
    exact carry hOld
  · by_cases h : s.pc = b.gate
    · have hNormal : s.fault = none := by
        cases hf : s.fault with
        | none => rfl
        | some f =>
          obtain ⟨tm, ho, hFire⟩ := he
          simp only [out, hf, Out.ev.injEq] at ho
          subst tm
          cases hFire.2
      have hAt : At s b.gate [] :=
        ⟨h, hShape.2.2 (by have := issueGateLower b; omega), hShape.2.1, hNormal, trivial⟩
      obtain ⟨tm, ho, hFire⟩ := he
      rw [electTemplate b.election hAt] at ho
      obtain rfl := Out.ev.inj ho
      obtain ⟨inst, leader, rfl, hAfter⟩ := hFire
      obtain rfl := Option.some.inj hAfter
      have hPred := electStateFrame (l := l) (g := g) b.election hAt leader (by simp) (by simp)
      exact ⟨inst, leader, by simp [Election, h], hPred.2.2.2.2.1⟩
    · have heCore : EStep kernel [] l g s ev (some u) := by
        obtain ⟨m, ho, hf⟩ := he
        exact ⟨m, hCore ▸ ho, hf⟩
      have hOld : b.inGate s.pc := by
        rcases (estep_return_pc heCore (fun _ _ _ hr => execLocal_frame hr)).2 with hp | hp
        · exact hp ▸ hNew
        · exact earlier hp h
      exact carry hOld

private theorem gateSelectionEntry {X : Execution} {g pos : Nat} {s : TState} (bank : IssueBank)
    (hPc : s.pc = 1908) : GateFrame l g bank ((X.tr g).take pos) s := by
  intro h
  have hGate := issueGateLower bank
  rw [hPc] at h
  exact (by have := h.1; omega : False).elim

private theorem gateSelectionStep {X : Execution} {g pos : Nat} {s u : TState} {ev : Option Event}
    {bank : IssueBank} (h : GateFrame l g bank ((X.tr g).take pos) s)
    (hRange : 1907 ≤ s.pc ∧ s.pc < 2768) (hShape : RoleShape s)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    GateFrame l g bank ((X.tr g).take (pos+ev.toList.length)) u := by
  intro hGate
  obtain ⟨inst,leader,hMember,hReg⟩ := gateFramePreserved hRange hShape h hStep hGate
  refine ⟨inst,leader,?_,hReg⟩
  cases ev with
  | none => exact hMember
  | some e =>
    have hGet := hActual e rfl
    have hLen := len_of_get hGet
    change Election bank inst leader ∈ (X.tr g).take (pos+1)
    rw [List.take_succ_eq_append_getElem hLen]
    have hValue := (List.getElem?_eq_some_iff.mp hGet).2
    rw [hValue]
    rcases List.mem_append.mp hMember with hNew | hOld
    · exact List.mem_append_right _ hNew
    · exact List.mem_append_left _ hOld

private theorem gateSelectionGuard {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} {bank : IssueBank} {s : TState}
    (h : GateFrame l g bank ((X.tr g).take pos) s) (frag : Fin 8) (hPc : s.pc = bank.site frag)
    {j tag inst leader : Nat} (he : X.Elect (g,j) tag (2^32-1) inst leader)
    (hWinner : laneOf l g = leader) :
    s.regs bank.guard = some (.pred true) := by
  have hIn : bank.inGate s.pc :=
    hPc.symm ▸ (issueInGate bank frag).1
  obtain ⟨instanceId,selected,hMember,hReg⟩ := h hIn
  obtain ⟨k,hK⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMember)
  have hg := event_thread_lt hX (show X.get (g,j) = _ from he)
  have hSame : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hPrior : X.Elect (g,k) bank.gate (2^32-1) instanceId selected := hK
  have hEq := hX.elect.2.2 _ _ _ _ _ _ _ _ _ he hPrior hSame
  simpa only [hWinner,hEq,beq_self_eq_true] using hReg

/-- The current PV gate's election is present in the consumed prefix. -/
@[no_expose] def PvGateSelection (l : Launch) (X : Execution) (g : Nat) (block : Fin 4)
    (pos : Nat) (s : TState) : Prop :=
  GateFrame l g (.value block) ((X.tr g).take pos) s

/-- The role enters before every PV election gate. -/
theorem PvGateSelection.entry {X : Execution} {g pos : Nat} {s : TState} (block : Fin 4)
    (hPc : s.pc = 1908) : PvGateSelection l X g block pos s :=
  gateSelectionEntry (.value block) hPc

/-- Track the election and predicate through each actual MMA role step. -/
theorem PvGateSelection.step {X : Execution} {g pos : Nat} {s u : TState} {ev : Option Event}
    {block : Fin 4} (h : PvGateSelection l X g block pos s) (hRange : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s) (hStep : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    PvGateSelection l X g block (pos + ev.toList.length) u :=
  gateSelectionStep h hRange hShape hStep hActual

-- The same lane wins all of its warp's full-mask elections.
theorem PvGateSelection.fragmentGuard {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} {block : Fin 4} {s : TState}
    (h : PvGateSelection l X g block pos s) (frag : Fin 8) (hPc : s.pc = pvPc block frag)
    {j tag inst leader : Nat} (he : X.Elect (g,j) tag (2^32-1) inst leader)
    (hWinner : laneOf l g = leader) :
    s.regs (pvSite block).guard = some (.pred true) := by
  have hGuard : ∀ b : Fin 4, (IssueBank.value b).guard = (pvSite b).guard := by decide
  exact hGuard block ▸ gateSelectionGuard hX h frag hPc he hWinner

theorem PvGateSelection.firstGuard {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} {block : Fin 4} {s : TState}
    (h : PvGateSelection l X g block pos s) (hPc : s.pc = pvPc block 0) {j tag inst leader : Nat}
    (he : X.Elect (g,j) tag (2^32-1) inst leader) (hWinner : laneOf l g = leader) :
    s.regs (pvSite block).guard = some (.pred true) :=
  PvGateSelection.fragmentGuard hX h 0 hPc he hWinner

/-- The current QK gate's election is present in the consumed prefix. -/
@[no_expose] def QkGateSelection (l : Launch) (X : Execution) (g : Nat) (block : Fin 4)
    (pos : Nat) (s : TState) : Prop :=
  GateFrame l g (.query block) ((X.tr g).take pos) s

theorem QkGateSelection.entry {X : Execution} {g pos : Nat} {s : TState} (block : Fin 4)
    (hPc : s.pc = 1908) : QkGateSelection l X g block pos s :=
  gateSelectionEntry (.query block) hPc

theorem QkGateSelection.step {X : Execution} {g pos : Nat} {s u : TState} {ev : Option Event}
    {block : Fin 4} (h : QkGateSelection l X g block pos s) (hRange : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s) (hStep : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    QkGateSelection l X g block (pos + ev.toList.length) u :=
  gateSelectionStep h hRange hShape hStep hActual

theorem QkGateSelection.fragmentGuard {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} {block : Fin 4} {s : TState}
    (h : QkGateSelection l X g block pos s) (frag : Fin 8) (hPc : s.pc = qkPc block+frag.val)
    {j tag inst leader : Nat} (he : X.Elect (g,j) tag (2^32-1) inst leader)
    (hWinner : laneOf l g = leader) :
    s.regs (qkGuard block) = some (.pred true) := by
  have hGuard : ∀ b : Fin 4, (IssueBank.query b).guard = qkGuard b := by decide
  exact hGuard block ▸ gateSelectionGuard hX h frag hPc he hWinner

private theorem issueGuardCode (b : IssueBank) (f : Fin 8) :
    ∃ op, kernel.code[b.site f]? = some ⟨some (b.guard, false), op⟩ := by
  cases b with
  | query block =>
    have hg : ∀ j, IssueBank.guard (.query j) = qkGuard j := by decide
    exact ⟨_, hg block ▸ qkCode block f⟩
  | value block =>
    have hg : ∀ j, IssueBank.guard (.value j) = (pvSite j).guard := by decide
    have h := pvCode block f
    dsimp only at h
    exact ⟨_, hg block ▸ h⟩

private theorem issueIsElected {g : Nat} {b : IssueBank} {f : Fin 8} {past : List Event}
    {s : TState} {result : Option TState} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hFrame : GateFrame l g b past s)
    (he : EStep kernel Assumptions.all l g s ⟨b.site f,.tc (.mma d op accum mask)⟩ result) :
    ∃ inst leader, Election b inst leader ∈ past ∧ laneOf l g = leader := by
  have hs : s.pc = b.site f := (estep_source_pc he).symm
  obtain ⟨inst, leader, hMem, hPred⟩ := hFrame (hs.symm ▸ (issueInGate b f).1)
  refine ⟨inst, leader, hMem, ?_⟩
  by_contra hNe
  rw [beq_eq_false_iff_ne.mpr hNe] at hPred
  obtain ⟨tm, hOut, hFire⟩ := he
  by_cases hNormal : s.fault = none
  · obtain ⟨_, hCode⟩ := issueGuardCode b f
    simp only [out, hNormal, hs, hCode, guardHolds, readReg, hPred, pure, Except.pure, bind,
      Except.bind] at hOut
    cases hOut
  · obtain ⟨reason, hFault⟩ := Option.ne_none_iff_exists'.mp hNormal
    simp only [out, hFault, Out.ev.injEq] at hOut
    subst tm
    simp [Fires] at hFire

private theorem issueElectionInWalk {g : Nat} {b : IssueBank} {f : Fin 8} {events past : List Event}
    {visits : List Visit} {s : TState} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hw : Walk kernel Assumptions.all l g s events visits)
    (hRange : 1907 ≤ s.pc ∧ s.pc < 2768) (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hFrame : GateFrame l g b past s)
    (hIssue : (⟨b.site f,.tc (.mma d op accum mask)⟩ : Event) ∈ events) :
    ∃ inst leader, Election b inst leader ∈ past ++ events ∧ laneOf l g = leader := by
  induction hw generalizing past with
  | stop => simp at hIssue
  | @last s ev he =>
    have hEvent := List.mem_singleton.mp hIssue
    subst ev
    obtain ⟨inst, leader, hMem, hChosen⟩ := issueIsElected hFrame he
    exact ⟨inst, leader, List.mem_append_left _ hMem, hChosen⟩
  | @tau s u events visits hTau hw ih =>
    have hStep : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl, hTau⟩
    obtain ⟨hNext | hExit, hNextShape⟩ := mmaCutStep hRange.1 hRange.2 hStep hShape
    · exact ih hNext hNextShape (gateFramePreserved hRange hShape.1 hFrame hStep) hIssue
    · have hWrong := mmaEpilogueExitEvents (by simpa using hExit.1) hExit.2 (.inl rfl)
        hNextShape.2 hw _ hIssue
      change b.site f = 9205 at hWrong
      have hSite := (issueInGate b f).2.2
      omega
  | @ev s u ev events visits hEv hw ih =>
    rcases List.mem_cons.mp hIssue with hHere | hTail
    · subst ev
      obtain ⟨inst, leader, hMem, hChosen⟩ := issueIsElected hFrame hEv
      exact ⟨inst, leader, List.mem_append_left _ hMem, hChosen⟩
    · have hStep : WStep kernel Assumptions.all l g s (some ev) u := .inr ⟨ev, rfl, hEv⟩
      obtain ⟨hNext | hExit, hNextShape⟩ := mmaCutStep hRange.1 hRange.2 hStep hShape
      · have hNew := gateFramePreserved hRange hShape.1 hFrame hStep
        obtain ⟨inst, leader, hMem, hChosen⟩ := ih hNext hNextShape hNew hTail
        change Election b inst leader ∈ ev :: (past ++ events) at hMem
        refine ⟨inst, leader, ?_, hChosen⟩
        rcases List.mem_cons.mp hMem with hEq | hMem
        · exact List.mem_append_right _ (List.mem_cons.mpr (.inl hEq))
        · rcases List.mem_append.mp hMem with hOld | hRest
          · exact List.mem_append_left _ hOld
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hRest)
      · have hWrong := mmaEpilogueExitEvents (by simpa using hExit.1) hExit.2 (.inl rfl)
          hNextShape.2 hw _ hTail
        change b.site f = 9205 at hWrong
        have hSite := (issueInGate b f).2.2
        omega

private theorem issueElectionOfRecordedMma {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (b : IssueBank) (f : Fin 8) {g i d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (he : X.get (g,i) = some ⟨b.site f,.tc (.mma d op accum mask)⟩) :
    warpIndex l g = 12 ∧ ∃ j inst leader,
      X.Elect (g,j) b.gate (2^32-1) inst leader ∧ laneOf l g = leader := by
  have hSite := (issueInGate b f).2
  have hHint : b.site f ∉ registerHintSites := by simp [registerHintSites]; omega
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < b.site f; omega) hHint
  change roleBodyPc (warpIndex l g) (b.site f) at hRole
  have hWarp : warpIndex l g = 12 := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  refine ⟨hWarp, ?_⟩
  obtain ⟨origin, s, _, hIndex, hs, hw⟩ := initialMmaTrace hp hX he hSite.1 hSite.2
  have hMem : (⟨b.site f,.tc (.mma d op accum mask)⟩ : Event) ∈ (X.tr g).drop (origin+1) := by
    apply List.mem_of_getElem? (i := i-(origin+1))
    rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
  have hFrame : GateFrame l g b [] s := by
    intro hBad
    have hGate := issueGateLower b
    have hTooEarly := hBad.1
    rw [hs.1] at hTooEarly
    omega
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩, hs.2.2.2.2.1⟩
  obtain ⟨inst, leader, hElection, hChosen⟩ := issueElectionInWalk hw
    (by rw [hs.1]; decide) hShape hFrame hMem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_drop (by
    simpa only [List.nil_append] using hElection))
  exact ⟨j, inst, leader, hj, hChosen⟩

/-- Every real QK and PV fragment is issued by its warp's full-mask elected lane. -/
theorem mmaIssueElection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : X.MmaIssue i d op accum mask) :
    warpIndex l i.1 = 12 ∧ ∃ j site inst leader,
      X.Elect (i.1,j) site (2^32-1) inst leader ∧ laneOf l i.1 = leader := by
  obtain ⟨g,i⟩ := i
  rcases actualMmaInstruction hX hIssue with ⟨b,f,h⟩ | ⟨b,f,h⟩
  · obtain ⟨hw, j, inst, leader, he, hLane⟩ :=
      issueElectionOfRecordedMma hp hX (.query b) f h.decoded
    exact ⟨hw, j, _, inst, leader, he, hLane⟩
  · obtain ⟨hw, j, inst, leader, he, hLane⟩ :=
      issueElectionOfRecordedMma hp hX (.value b) f h.decoded
    exact ⟨hw, j, _, inst, leader, he, hLane⟩

/-- All MMA issues in a warp use the same lane under the election rule. -/
theorem mmaWarpIssuerUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    TcMma.WarpIssuerUnique l X := by
  rintro i j ⟨d,op,acc,mask,hi⟩ ⟨d',op',acc',mask',hj⟩ hWarp
  obtain ⟨_, k, site, inst, leader, hElection, hLane⟩ := mmaIssueElection hp hX hi
  obtain ⟨_, k', site', inst', leader', hElection', hLane'⟩ := mmaIssueElection hp hX hj
  exact selected_elect_thread_unique (e := (i.1, k)) (f := (j.1, k'))
    hX.elect hElection hElection' hWarp hLane hLane'

/-- The kernel has no Tensor Core shift instruction. -/
theorem noTensorShiftIssue {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {s : TcShift.Spec} :
    ¬ X.ShiftIssue i s := by
  rintro ⟨site, he⟩
  have hCode : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by decide +kernel
  exact no_kind_of_code hX tcShiftOp (fun k => ∃ spec, k = .tc (.shift spec))
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, h⟩ => fires_tcShift_op hf h) hCode he ⟨s, rfl⟩

end PTX.Kernels.TmlFa4Fwd.Thread

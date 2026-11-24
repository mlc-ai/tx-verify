-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
public import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Lemmas.Flow.CountWindow
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
import Lemmas.Flow.Tc
public import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.AsyncCopy PTX.Assumption Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

private def scoreSlot (stage packet : Fin 2) : Fin 4 :=
  ⟨2 * stage.val + packet.val, by have := stage.isLt; have := packet.isLt; omega⟩

private theorem beforeRecurringScore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X e cta stage spec rank) (packet : Fin 2)
    (block : Fin 4) (hStage : block.val % 2 = stage.val) (hRepeat : 2 ≤ block.val)
    (he : X.get e = some ⟨(commitSite (qkCommitSite block)).pc, .tc (.commit spec)⟩) :
    ∃ j source q acq scope, X.get (e.1,j) =
      some ⟨source, .wait (probabilityObject l cta stage packet) q true acq scope⟩ ∧
      Resumes kernel X (e.1,j) e ∧
      j < e.2 - 1 ∧
      (((X.tr e.1).take j).countP (fun ev => match ev.kind with
        | .wait _ _ true _ _ => ev.pc == probabilityPc (scoreSlot stage packet) false
        | _ => false)) =
        ElectOrd.siteOrdinal (fun pc => pc == probabilityScoreElection (scoreSlot stage packet))
          X e.1 (e.2 - 1) := by
  obtain ⟨hIndex, inst, leader, hElect, _⟩ :=
    scoreCommitLeader hp hX block (g := e.1) (index := e.2) he
  have hSite : (electSite (commitElection (qkCommitSite block))).pc =
      probabilityScoreElection (scoreSlot stage packet) := by
    fin_cases block <;> fin_cases stage <;> fin_cases packet <;>
      first | decide | contradiction
  rw [hSite] at hElect
  obtain ⟨j, hj, loc, q, acq, sc, hGet, hOrdinal⟩ :=
    probabilityWaitAtScoreElection hp hX (scoreSlot stage packet) hElect
  have hWaitPc (stage packet : Fin 2) :
      let pc := probabilityPc (scoreSlot stage packet) false
      pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] ∧
      fixedMmaWaitOffset pc = 96 + 8 * stage.val + 16 * packet.val := by
    fin_cases stage <;> fin_cases packet <;> decide
  obtain ⟨hf, hWe⟩ := hWaitPc stage packet
  have hLoc := mmaFixedWaitAddress hp hX hGet hf
  have hOwner := (scoreCommitActor hp hX hIssue).1
  rw [hOwner, hWe] at hLoc
  change loc = probabilityObject l cta stage packet at hLoc
  subst loc
  have hTrace : TraceBefore X (e.1,j) e := ⟨rfl, by omega, (List.getElem?_eq_some_iff.mp he).1⟩
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hGet
  refine ⟨j,_,q,acq,sc,hGet,⟨hTrace,?_⟩,hj,hOrdinal⟩
  simp only [hGet, Option.map_some, Kind.resume]
  exact ⟨_, exit, _, q, acq, sc, hGet, hSpin, hTrace⟩

private def openingCommitPc (stage : Fin 2) : Nat :=
  (commitSite (qkCommitSite ⟨stage.val, by have := stage.isLt; omega⟩)).pc

private theorem openingFloorCode (stage : Fin 2) :
    (kernel.code.drop (openingCommitPc stage + 1)).all
      (fun i => staysPastEvent (openingCommitPc stage + 1) i.op) = true := by
  fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem openingFloorSegments (stage : Fin 2) :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (openingCommitPc stage + 1 ≤ seg.stop)
      | none => false) = true := by
  fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem openingCommitNoLater {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g j k : Nat} {a b : TcCommit.Spec}
    (he : X.get (g,j) = some ⟨openingCommitPc stage, .tc (.commit a)⟩)
    (hf : X.get (g,k) = some ⟨openingCommitPc stage, .tc (.commit b)⟩) (hOrder : j < k) :
    False := by
  obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
  have hLen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨s, u, hStep, hTail⟩ := hRun.after_event he (by omega)
  obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source hStep
  have hPc : s.pc = openingCommitPc stage := (estep_source_pc hStep).symm
  have hExpected : ∃ base off, kernel.code[openingCommitPc stage]? =
      some ⟨none, .tcCommit .one base off none⟩ := by
    fin_cases stage
    · exact ⟨_, _, Flow.code_2208⟩
    · exact ⟨_, _, Flow.code_2270⟩
  obtain ⟨base, off, hExpected⟩ := hExpected
  rw [hPc, hExpected] at hCode
  obtain rfl := Option.some.inj hCode
  obtain rfl := fires_tcCommit hFire
  obtain ⟨_, hWalk⟩ := walkFromRun hTail
  have hMem : (⟨openingCommitPc stage, .tc (.commit b)⟩ : Event) ∈ (X.tr g).drop (j + 1) := by
    apply List.mem_of_getElem? (i := k - (j + 1))
    rw [List.getElem?_drop, Nat.add_sub_of_le (show j + 1 ≤ k by omega)]
    exact hf
  have hFloor := eventTailEvents (openingFloorCode stage) (openingFloorSegments stage)
    hWalk (show openingCommitPc stage + 1 ≤ (next s).pc by simp [next, hPc]) _ hMem
  change openingCommitPc stage + 1 ≤ openingCommitPc stage at hFloor
  omega

private theorem scoreCommitOfMark {l : Launch} {X : Execution} {cta : Nat}
    (stage : Fin 2) {e : EvId} {ev : Event} (he : X.get e = some ev)
    (hm : scoreCommitOn (scoreReadyObject l cta stage) ev = true) :
    ∃ s, ScoreCommit l X e cta stage s 0 := by
  obtain ⟨pc, kind⟩ := ev
  cases kind <;> simp [scoreCommitOn] at hm
  case tc op =>
    cases op <;> simp at hm
    exact ⟨_, ⟨_, he⟩, hm⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem openingScoreHasNoOrdinal {g j cta : Nat} (stage : Fin 2) {spec : TcCommit.Spec}
    (he : X.get (g,j) = some ⟨openingCommitPc stage, .tc (.commit spec)⟩) :
    scoreCommitOrdinal l X cta stage (g,j) = 0 := by
  apply List.countP_eq_zero.mpr
  intro ev hm hMark
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  have hLen := (List.getElem?_eq_some_iff.mp hk).1
  rw [List.length_take] at hLen
  have hBefore : k < j := by omega
  rw [List.getElem?_take_of_lt hBefore] at hk
  obtain ⟨s, hBox⟩ := scoreCommitOfMark stage (e := (g,k)) hk hMark
  obtain ⟨block, hStage, hEvent⟩ := scoreCommitSite hp hX hBox
  by_cases hInitial : block.val < 2
  · have hEq : (commitSite (qkCommitSite block)).pc = openingCommitPc stage := by
      fin_cases block <;> fin_cases stage <;> first | decide | contradiction
    rw [hEq] at hEvent
    exact openingCommitNoLater hX stage hEvent he hBefore
  · have hLate : openingCommitPc stage + 1 ≤ (commitSite (qkCommitSite block)).pc := by
      fin_cases block <;> fin_cases stage <;> first | decide | contradiction
    have hOrder := traceOrderOfPcFloor hX (openingFloorCode stage) (openingFloorSegments stage)
      he hEvent (Nat.lt_succ_self _) hLate
    omega

theorem positiveScoreCommitRepeats {e : EvId} {cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec}
    {rank : Fin 16} (he : ScoreCommit l X e cta stage spec rank)
    (hPos : 0 < scoreCommitOrdinal l X cta stage e) :
    ∃ block : Fin 4, block.val % 2 = stage.val ∧ 2 ≤ block.val ∧
      X.get e = some ⟨(commitSite (qkCommitSite block)).pc, .tc (.commit spec)⟩ := by
  obtain ⟨block, hStage, hGet⟩ := scoreCommitSite hp hX he
  have hRepeat : 2 ≤ block.val := by
    by_contra! hFirst
    have hEq : (commitSite (qkCommitSite block)).pc = openingCommitPc stage := by
      fin_cases block <;> fin_cases stage <;> first | decide | contradiction
    rw [hEq] at hGet
    obtain ⟨g,j⟩ := e
    have hz := openingScoreHasNoOrdinal hp hX (cta := cta) stage hGet
    omega
  exact ⟨block, hStage, hRepeat, hGet⟩

private theorem scoreBudgetAtElection {g j cta : Nat} (stage packet : Fin 2) :
    scoreCommitOrdinal l X cta stage (g,j) ≤ 1 + ElectOrd.siteOrdinal
      (fun pc => pc == probabilityScoreElection (scoreSlot stage packet)) X g (j - 1) := by
  classical
  let mark := scoreCommitOn (scoreReadyObject l cta stage)
  let election := ElectOrd.atSites
    (fun pc => pc == probabilityScoreElection (scoreSlot stage packet))
  let tr := X.tr g
  let later := (Finset.range j).filter (fun n =>
    (tr[n]?).any mark = true ∧ 1 ≤ (tr.take n).countP mark)
  let elections := (Finset.range (j - 1)).filter (fun n =>
    (tr[n]?).any election = true ∧ 0 ≤ (tr.take n).countP election)
  have hLater : later.card = (tr.take j).countP mark - 1 := card_window tr mark 1 j
  have hElections : elections.card = (tr.take (j - 1)).countP election := by
    exact (card_window tr election 0 (j - 1)).trans (Nat.sub_zero _)
  have hOrigin (k : Nat) (hk : k ∈ later) :
      0 < k ∧ (k - 1) ∈ elections := by
    obtain ⟨hk, hM, hOrd⟩ := Finset.mem_filter.mp hk
    cases hGet : tr[k]? with
    | none => simp [hGet] at hM
    | some ev =>
      have hP : mark ev = true := by simpa [hGet] using hM
      obtain ⟨spec,hCommit⟩ := scoreCommitOfMark stage (e := (g,k)) hGet hP
      obtain ⟨block, hStage, hRepeat, hRaw⟩ :=
        positiveScoreCommitRepeats hp hX hCommit
          (show 0 < scoreCommitOrdinal l X cta stage (g,k) from hOrd)
      obtain ⟨hk0, inst, leader, hElect, _⟩ := scoreCommitLeader hp hX block hRaw
      have hSite : (electSite (commitElection (qkCommitSite block))).pc =
          probabilityScoreElection (scoreSlot stage packet) := by
        fin_cases block <;> fin_cases stage <;> fin_cases packet <;> first | decide | contradiction
      have hLt := Finset.mem_range.mp hk
      refine ⟨hk0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, Nat.zero_le _⟩⟩
      change tr[k - 1]? = _ at hElect
      rw [hElect, hSite]
      simp [election, ElectOrd.atSites, isElectEv]
  have hCard : later.card ≤ elections.card := by
    apply Finset.card_le_card_of_injOn (fun k => k - 1)
    · exact fun k hk => (hOrigin k hk).2
    · intro x hx y hy he
      have hx' := (hOrigin x hx).1
      have hy' := (hOrigin y hy).1
      change x - 1 = y - 1 at he
      omega
  change scoreCommitOrdinal l X cta stage (g,j) ≤ 1 + (tr.take (j - 1)).countP election
  change (tr.take j).countP mark ≤ 1 + (tr.take (j - 1)).countP election
  omega

/-- At a score commit, the physical target count is bounded by the opening
commit and the earlier recurring gate elections. -/
theorem scoreCommitBudgetBeforeElection {g j cta : Nat} (stage packet : Fin 2) (slot : Fin 4)
    (hSlot : slot.val = 2 * stage.val + packet.val) :
    scoreCommitOrdinal l X cta stage (g,j) ≤ 1 + ElectOrd.siteOrdinal
      (fun pc => pc == probabilityScoreElection slot) X g (j - 1) := by
  have hSame : slot = scoreSlot stage packet := Fin.ext hSlot
  subst slot
  exact scoreBudgetAtElection hp hX stage packet

/-- Every prior repeated score commit has its own earlier probability-gate election. -/
theorem scoreCommitBudgetAtProbabilityGate {g j cta : Nat} (stage packet : Fin 2) (slot : Fin 4)
    (hSlot : slot.val = 2 * stage.val + packet.val) :
    scoreCommitOrdinal l X cta stage (g,j) ≤ 1 + ElectOrd.siteOrdinal
      (fun pc => pc == probabilityScoreElection slot) X g j := by
  have hSame : slot = scoreSlot stage packet := Fin.ext hSlot
  subst slot
  refine (scoreBudgetAtElection hp hX stage packet).trans (Nat.add_le_add_left ?_ 1)
  exact countP_take_mono _ _ (Nat.sub_le _ _)

/-- A recurring score commit is guarded by the preceding successful probability acquisition
of either packet. The count is the actual number of earlier score issues to its stage. -/
theorem scoreCommitPreviousProbability {e : EvId} {cta : Nat} {stage : Fin 2} {spec : TcCommit.Spec}
    {rank : Fin 16} (hIssue : ScoreCommit l X e cta stage spec rank) (packet : Fin 2)
    (hPos : 0 < scoreCommitOrdinal l X cta stage e) :
    let obj := probabilityObject l cta stage packet
    ∃ k ev q acq scope, X.get (e.1,k) = some ev ∧ ev.kind = .wait obj q true acq scope ∧
      okPolls obj ((X.tr e.1).take k) + 1 = scoreCommitOrdinal l X cta stage e ∧
      Resumes kernel X (e.1,k) e := by
  obtain ⟨g, j⟩ := e
  let obj := probabilityObject l cta stage packet
  let mark (ev : Event) : Bool :=
    match ev.kind with
    | .wait _ _ true _ _ => ev.pc == probabilityPc (scoreSlot stage packet) false
    | _ => false
  obtain ⟨block, hStage, hRepeat, hGet⟩ := positiveScoreCommitRepeats hp hX hIssue hPos
  obtain ⟨k, source, q, acq, scope, hPoll, hRes, _, hRel⟩ :=
    beforeRecurringScore hp hX hIssue packet block hStage hRepeat hGet
  have hBudget := scoreBudgetAtElection hp hX stage packet (g := g) (j := j) (cta := cta)
  have hOwner : g / l.block = cta := (scoreCommitActor hp hX hIssue).1
  have hCount (b : Nat) :
      ((X.tr g).take b).countP mark ≤ okPolls obj ((X.tr g).take b) := by
    apply List.countP_mono_left
    intro ev hMem hm
    obtain ⟨i, hEv⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
    obtain ⟨source, kind⟩ := ev
    cases kind <;> try cases hm
    case wait loc q ok acq scope =>
      cases ok <;> try cases hm
      have hRaw : source = probabilityPc (scoreSlot stage packet) false := beq_iff_eq.mp hm
      subst source
      have hWaitPc (stage packet : Fin 2) :
          let pc := probabilityPc (scoreSlot stage packet) false
          pc ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] ∧
          fixedMmaWaitOffset pc = 96 + 8 * stage.val + 16 * packet.val := by
        fin_cases stage <;> fin_cases packet <;> decide
      obtain ⟨hf, hEq⟩ := hWaitPc stage packet
      have hLoc := mmaFixedWaitAddress hp hX (g := g) (index := i) hEv hf
      rw [hOwner, hEq] at hLoc
      change loc = obj at hLoc
      rw [hLoc]
      simp [okPoll, sourceWaitSuccess]
  have hLt : k < j := hRes.1.2.1
  have hProgress := MbarRing.Poll.okPoll_get hPoll
  have hMono := MbarRing.Poll.okPolls_mono obj (X.tr g) (show k + 1 ≤ j by omega)
  have hPrefix := hCount k
  change ((X.tr g).take k).countP mark = ElectOrd.siteOrdinal
    (fun pc => pc == probabilityScoreElection (scoreSlot stage packet)) X g (j - 1) at hRel
  change okPolls obj ((X.tr g).take (k + 1)) = okPolls obj ((X.tr g).take k) + 1 at hProgress
  change okPolls obj ((X.tr g).take (k + 1)) ≤ okPolls obj ((X.tr g).take j) at hMono
  have hEnough : scoreCommitOrdinal l X cta stage (g,j) ≤ okPolls obj ((X.tr g).take j) := by
    omega
  let n := scoreCommitOrdinal l X cta stage (g,j) - 1
  obtain ⟨i, source, phase, acquire, sc, hi, hEv, hNth⟩ :=
    MbarRing.Poll.exists_nth (n := n) (show n + 1 ≤ okPolls obj ((X.tr g).take j) by
      dsimp only [n]
      omega)
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX hEv
  have hTrace : TraceBefore X (g,i) (g,j) := ⟨rfl, hi, (List.getElem?_eq_some_iff.mp hGet).1⟩
  refine ⟨i,_, phase, acquire, sc, hEv, rfl, ?_, hTrace, ?_⟩
  · rw [hNth]
    dsimp only [n]
    omega
  · simp only [hEv, Option.map_some, Kind.resume]
    exact ⟨source, exit, obj, phase, acquire, sc, hEv, hSpin, hTrace⟩

/-- Each earlier successful probability acquire guards the actual recurring score issue. -/
theorem scoreCommitProbabilityOfOrdinal {e : EvId} {cta n : Nat} {stage : Fin 2}
    {spec : TcCommit.Spec} {rank : Fin 16} (hIssue : ScoreCommit l X e cta stage spec rank)
    (packet : Fin 2) (hn : n < scoreCommitOrdinal l X cta stage e) :
    let obj := probabilityObject l cta stage packet
    ∃ k ev q acq scope, X.get (e.1,k) = some ev ∧ ev.kind = .wait obj q true acq scope ∧
      okPolls obj ((X.tr e.1).take k) = n ∧ Resumes kernel X (e.1,k) e := by
  obtain ⟨g,i⟩ := e
  let obj := probabilityObject l cta stage packet
  have hPos : 0 < scoreCommitOrdinal l X cta stage (g,i) := by omega
  obtain ⟨k, e, parity, acquire, waitScope, hGet, hKind, hCount, hResume⟩ :=
    scoreCommitPreviousProbability hp hX hIssue packet hPos
  have hKI : k < i := hResume.1.2.1
  have hMore : i < (X.tr g).length := hResume.1.2.2
  change okPolls obj ((X.tr g).take k) + 1 = _ at hCount
  change n < scoreCommitOrdinal l X cta stage (g,i) at hn
  have hMono := countP_take_mono (okPoll obj) (X.tr g) (i := k+1) (j := i) (by omega)
  have hMark : okPoll obj e = true := by simp [okPoll, sourceWaitSuccess, hKind, obj]
  change (X.tr g)[k]? = some e at hGet
  rw [List.take_add_one, hGet, Option.toList_some, List.countP_append,
    List.countP_singleton, ite_eq_left hMark] at hMono
  have hBudget : n+1 ≤ okPolls obj ((X.tr g).take i) := by
    change okPolls obj ((X.tr g).take k) + 1 ≤ okPolls obj ((X.tr g).take i) at hMono
    omega
  obtain ⟨pos, source, q, acq, scope, hPos, he, hN⟩ := MbarRing.Poll.exists_nth hBudget
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX he
  have ht : TraceBefore X (g,pos) (g,i) := ⟨rfl,hPos,hMore⟩
  refine ⟨pos,_,q,acq,scope,he,rfl,hN,ht,?_⟩
  simp only [he, Option.map_some, Kind.resume]
  exact ⟨source,exit,obj,q,acq,scope,he,hSpin,ht⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores

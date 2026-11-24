-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Lemmas.Flow.CountTake
import Lemmas.Flow.ContinuingEvent
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part116
public import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.EventFrame Prologue

private def creditPc (packet : Fin 2) : Fin 3 → Nat
  | 0 => if packet.val = 0 then 4847 else 4867
  | 1 => if packet.val = 0 then 6532 else 6552
  | _ => if packet.val = 0 then 7437 else 7457

private def scorePollPc : Fin 3 → Nat
  | 0 => 3425
  | 1 => 5109
  | _ => 6676

private def creditMark (packet : Fin 2) (round : Fin 3) (e : Event) : Bool :=
  e.pc == creditPc packet round

private def scorePollMark (round : Fin 3) (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => e.pc == scorePollPc round
  | _ => false

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem creditSites {g i source cta tx n : Nat} {rel : Bool} {scope : MbarScope}
    (stage packet : Fin 2) (hw : warpIndex l g < 8) (hs : warpIndex l g / 4 = stage.val)
    (he : X.get (g,i) = some ⟨source, .arrive (probabilityObject l cta stage packet)
      tx n rel scope⟩) :
    source ∈ [creditPc packet 0, creditPc packet 1, creditPc packet 2] := by
  have hOffset : 96 + 8 * stage.val + 16 * packet.val ∈ [96, 104, 112, 120] := by
    fin_cases stage <;> fin_cases packet <;> decide
  rcases actualProbabilityArrivalSite hp hX he hOffset rfl with ⟨q, rfl⟩ | hCorr
  · obtain ⟨_, _, _, _, _, hLoc⟩ := Softmax.probabilityArriveFacts hp hX q he
    have hAddr : l.sharedBase + (96 + 8 * stage.val + 16 * packet.val) = l.sharedBase +
        ((Softmax.probabilityArrivalSite q).offset + 8 * (warpIndex l g / 4)) :=
      congrArg Loc.addr hLoc
    have hWhich : (Softmax.probabilityArrivalSite q).offset = 96 + 16 * packet.val := by omega
    have hAll : ∀ (q : Fin 6) (packet : Fin 2),
        (Softmax.probabilityArrivalSite q).offset = 96 + 16 * packet.val →
        (Softmax.probabilityArrivalSite q).pc ∈
          [creditPc packet 0, creditPc packet 1, creditPc packet 2] := by decide
    exact hAll q packet hWhich
  · have hBad := (Correction.correctionProbabilityCredit hp hX he hCorr).2.2.2.2.1
    omega

omit hp hX in
private theorem countThree (mark : Fin 3 → Event → Bool) (xs : List Event)
    (hDisj : ∀ e i j, mark i e = true → mark j e = true → i = j) :
    xs.countP (fun e => mark 0 e || mark 1 e || mark 2 e) =
      xs.countP (mark 0) + xs.countP (mark 1) + xs.countP (mark 2) := by
  have h01 : ∀ e ∈ xs, ¬ (mark 0 e = true ∧ mark 1 e = true) := by
    intro e _ h
    exact (by decide : (0 : Fin 3) ≠ 1) (hDisj e 0 1 h.1 h.2)
  have h201 : ∀ e ∈ xs, ¬ ((mark 0 e || mark 1 e) = true ∧ mark 2 e = true) := by
    intro e _ h
    obtain ⟨hA, hB⟩ := h
    rcases Bool.or_eq_true_iff.mp hA with h | h
    · exact (by decide : (0 : Fin 3) ≠ 2) (hDisj e 0 2 h hB)
    · exact (by decide : (1 : Fin 3) ≠ 2) (hDisj e 1 2 h hB)
  rw [countP_or_disj h201, countP_or_disj h01]

private theorem scorePollOfProbabilityBudget {g j cta : Nat} (stage packet : Fin 2)
    (hw : warpIndex l g < 8) (hCta : g/l.block = cta) (hStage : warpIndex l g / 4 = stage.val)
    {event : Event} (hGet : X.get (g,j) = some event)
    (hRaw : let before := (X.tr g).take j
      before.countP (creditMark packet 0) + before.countP (creditMark packet 1) +
        before.countP (creditMark packet 2) + 1 ≤
          before.countP (scorePollMark 0) + before.countP (scorePollMark 1) +
            before.countP (scorePollMark 2)) :
    let obj := scoreReadyObject l cta stage
    ∃ k e q acq scope, X.get (g,k) = some e ∧ e.kind = .wait obj q true acq scope ∧
      okPolls obj ((X.tr g).take k) = probabilityOrdinal l X cta stage packet (g,j) ∧
      Resumes kernel X (g,k) (g,j) := by
  let obj := scoreReadyObject l cta stage
  let txObj := probabilityObject l cta stage packet
  let before := (X.tr g).take j
  change before.countP (creditMark packet 0) + before.countP (creditMark packet 1) +
    before.countP (creditMark packet 2) + 1 ≤
      before.countP (scorePollMark 0) + before.countP (scorePollMark 1) +
        before.countP (scorePollMark 2) at hRaw
  have hCreditDisj : ∀ e i j, creditMark packet i e = true → creditMark packet j e = true →
      i = j := by
    intro e i j ha hb
    have hn : creditPc packet i = creditPc packet j := (beq_iff_eq.mp ha).symm.trans
      (beq_iff_eq.mp hb)
    have hInj (packet : Fin 2) : Function.Injective (creditPc packet) := by
      fin_cases packet <;> decide
    exact hInj _ hn
  have hCount : probabilityOrdinal l X cta stage packet (g,j) ≤
      before.countP (creditMark packet 0) + before.countP (creditMark packet 1) +
        before.countP (creditMark packet 2) := by
    rw [← countThree _ _ hCreditDisj]
    apply List.countP_mono_left
    intro e hm ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hm)
    obtain ⟨src, kind⟩ := e
    cases kind <;> simp only [arrivesOn, sourceArrive, Bool.false_eq_true] at ha
    case arrive target bytes count rel scope =>
      have hLoc : target = txObj := of_decide_eq_true ha
      subst target
      have hC := creditSites hp hX stage packet hw hStage (g := g) (i := k) hk
      simpa [creditMark, Bool.or_assoc] using hC
  have hScoreDisj : ∀ e i j, scorePollMark i e = true → scorePollMark j e = true → i = j := by
    intro e i j ha hb
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp [scorePollMark] at ha hb
    rename_i _ _ ok _ _
    cases ok <;> simp at ha hb
    have hInj : Function.Injective scorePollPc := by decide
    exact hInj (ha.symm.trans hb)
  have hSuccess : before.countP (scorePollMark 0) + before.countP (scorePollMark 1) +
        before.countP (scorePollMark 2) ≤ okPolls obj before := by
    rw [← countThree _ _ hScoreDisj]
    apply List.countP_mono_left
    intro e hm hMark
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hm)
    obtain ⟨src, kind⟩ := e
    cases kind <;> simp [scorePollMark] at hMark
    rename_i target q ok acq sc
    cases ok <;> simp [scorePollPc] at hMark
    have hSite : src ∈ [3425, 5109, 6676] := by simpa [or_assoc] using hMark
    have hAddr := (Softmax.scoreReadyWaitStage hp hX (g := g) (index := k) hk hSite).2
    rw [hStage, hCta] at hAddr
    change target = obj at hAddr
    subst target
    simp [okPoll, sourceWaitSuccess]
  have hBudget : probabilityOrdinal l X cta stage packet (g,j) + 1 ≤ okPolls obj before := by
    omega
  obtain ⟨k, pc, q, acq, scope, hK, he, hNth⟩ := MbarRing.Poll.exists_nth hBudget
  obtain ⟨exit, hSpin⟩ := actualCanonicalPoll hX he
  have hTrace : TraceBefore X (g,k) (g,j) :=
    ⟨rfl, hK, (List.getElem?_eq_some_iff.mp hGet).1⟩
  refine ⟨k,_,q,acq,scope,he,rfl,hNth,hTrace,?_⟩
  simp only [he, Option.map_some, Kind.resume]
  exact ⟨pc, exit, obj, q, acq, scope, he, hSpin, hTrace⟩

/-- Each actual softmax probability credit has the successful score acquire of its local ordinal.
The result uses the real round history for each packet and includes the first credit. -/
theorem softmaxProbabilityCreditScorePoll {g j cta : Nat} (stage packet : Fin 2)
    (hw : warpIndex l g < 8) (hCredit : ProbabilityCredit l X (g,j) cta stage packet) :
    let obj := scoreReadyObject l cta stage
    ∃ k e q acq scope, X.get (g,k) = some e ∧ e.kind = .wait obj q true acq scope ∧
      okPolls obj ((X.tr g).take k) = probabilityOrdinal l X cta stage packet (g,j) ∧
      Resumes kernel X (g,k) (g,j) := by
  have hRole := probabilityCreditRole hp hX stage packet hCredit
  have hCta := hRole.1
  have hStage : warpIndex l g / 4 = stage.val := by
    rcases hRole.2 with h | h
    · exact h.2
    · have hNonsoft : 8 ≤ warpIndex l g := h.2.1
      omega
  obtain ⟨source, hGet⟩ := hCredit
  have hCreditAt := creditSites hp hX stage packet hw hStage hGet
  have hRaw := Softmax.actualProbabilityScoreBudget hp hX packet hGet
    (by fin_cases packet <;> exact hCreditAt)
  exact scorePollOfProbabilityBudget hp hX stage packet hw hCta hStage hGet hRaw

/-- The probability store itself already follows the successful score acquire
indexed by prior same-lane credits to its physical packet. -/
theorem softmaxProbabilityStoreScorePoll {g j address : Nat} {values : List Value} {shape : TcShape}
    (stage : Fin 2) (hw : warpIndex l g < 8) (hStage : warpIndex l g / 4 = stage.val)
    (round : Softmax.Round) (quarter : Fin 4)
    (hStore : X.get (g,j) = some
      ⟨Softmax.probabilityPc round quarter,.tc (.st address values shape)⟩) :
    let packet := (if quarter = 3 then 1 else 0 : Fin 2)
    let cta := g/l.block
    let obj := scoreReadyObject l cta stage
    ∃ k e q acq scope, X.get (g,k) = some e ∧ e.kind = .wait obj q true acq scope ∧
      okPolls obj ((X.tr g).take k) = probabilityOrdinal l X cta stage packet (g,j) ∧
      Resumes kernel X (g,k) (g,j) :=
  scorePollOfProbabilityBudget hp hX stage _ hw rfl hStage hStore
    (Softmax.actualProbabilityStoreScoreBudget hX round quarter hStore)

/-- An actual score load is guarded by the score observation named by its own
lane's prior packet-zero credits. -/
theorem softmaxScoreLoadScorePoll {g j address : Nat} {values : List Value} {shape : TcShape}
    (stage : Fin 2) (hw : warpIndex l g < 8) (hStage : warpIndex l g / 4 = stage.val)
    (round : Softmax.Round) (quarter : Fin 4)
    (hLoad : X.get (g,j) = some ⟨Softmax.scorePc round quarter,.tc (.ld address values shape)⟩) :
    let cta := g/l.block
    let obj := scoreReadyObject l cta stage
    ∃ k e q acq scope, X.get (g,k) = some e ∧ e.kind = .wait obj q true acq scope ∧
      okPolls obj ((X.tr g).take k) = probabilityOrdinal l X cta stage 0 (g,j) ∧
      Resumes kernel X (g,k) (g,j) :=
  scorePollOfProbabilityBudget hp hX stage 0 hw rfl hStage hLoad
    (Softmax.actualScoreLoadScoreBudget hX round quarter hLoad)

omit hp hX in
private theorem packetZeroArrivalKind {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g s e (some u))
    (hSite : Softmax.earlyProbabilityMark e = true) :
    ∃ loc tx count rel scope, e.kind = .arrive loc tx count rel scope := by
  have hPc := estep_source_pc he
  have hCases : s.pc = 4847 ∨ s.pc = 6532 ∨ s.pc = 7437 := by
    simpa [Softmax.earlyProbabilityMark,hPc] using hSite
  have hCode : ∃ base count dst, kernel.code[s.pc]? =
      some ⟨none,.mbarArrive base 96 (.imm 0) (.reg count) false true .cta (some dst)⟩ := by
    rcases hCases with hc | hc | hc
    · exact ⟨_,_,_,hc.symm ▸ Flow.code_4847⟩
    · exact ⟨_,_,_,hc.symm ▸ Flow.code_6532⟩
    · exact ⟨_,_,_,hc.symm ▸ Flow.code_7437⟩
  obtain ⟨base,count,dst,hCode⟩ := hCode
  obtain ⟨ins,hGet,_,hFire⟩ := PTX.EventFrame.estep_event_source he
  obtain rfl := Option.some.inj (hGet.symm.trans hCode)
  have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
  have hTx : readBits l g s 32 (.imm 0) = .ok 0#64 := rfl
  simp only [eventTmpl,tmaTmpl,widenMbarScope,hWide,hTx,bind,Except.bind,
    pure,Except.pure] at hFire
  cases hm : mbarLoc l g s base 96
  · simp [hm,ofExec,Fires] at hFire
  · cases hn : readBits l g s 32 (.reg count)
    · simp [hm,hn,ofExec,Fires] at hFire
    · simp only [hm,hn,ofExec,Fires] at hFire
      rw [hFire.1]
      exact ⟨_,_,_,_,_,rfl⟩

/-- The decoded early packet credits count exactly the actual stage-object notifications. -/
theorem earlyProbabilityCount {g j : Nat} (stage : Fin 2) (hw : warpIndex l g < 8)
    (hs : warpIndex l g/4 = stage.val) (hj : j < (X.tr g).length) :
    ((X.tr g).take j).countP Softmax.earlyProbabilityMark =
      probabilityOrdinal l X (g/l.block) stage 0 (g,j) := by
  let object := probabilityObject l (g/l.block) stage 0
  change _ = ((X.tr g).take j).countP (arrivesOn object)
  apply List.countP_congr
  intro e hm
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hm
  have hLt := (List.getElem?_eq_some_iff.mp hi).1
  have hiJ : i < j := hLt.trans_le (by simp)
  rw [List.getElem?_take_of_lt hiJ] at hi
  change X.get (g,i) = some e at hi
  constructor
  · intro hMark
    obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hi)
    obtain ⟨s,u,hStep,_⟩ := hRun.after_event hi (by omega)
    obtain ⟨loc,tx,n,rel,scope,hKind⟩ := packetZeroArrivalKind hStep hMark
    obtain ⟨site,kind⟩ := e
    change kind = _ at hKind
    subst kind
    have hSites : ∃ k : Fin 6, site = (Softmax.probabilityArrivalSite k).pc ∧
        (Softmax.probabilityArrivalSite k).offset = 96 := by
      have hh : site = 4847 ∨ site = 6532 ∨ site = 7437 := by
        simpa [Softmax.earlyProbabilityMark] using hMark
      rcases hh with rfl | rfl | rfl
      · exact ⟨0,rfl,rfl⟩
      · exact ⟨2,rfl,rfl⟩
      · exact ⟨4,rfl,rfl⟩
    obtain ⟨k,rfl,hOffset⟩ := hSites
    have hLoc := (Softmax.probabilityArriveFacts hp hX k hi).2.2.2.2.2
    rw [hOffset,hs] at hLoc
    have hObj : loc = object := hLoc.trans (by simp [object,probabilityObject])
    simp [arrivesOn,sourceArrive,hObj]
  · intro hArrive
    obtain ⟨site,kind⟩ := e
    cases kind <;> simp only [arrivesOn,sourceArrive,Bool.false_eq_true] at hArrive
    case arrive loc tx n rel scope =>
      have hLoc : loc = object := of_decide_eq_true hArrive
      subst loc
      have h := creditSites hp hX stage 0 hw hs hi
      simpa [Softmax.earlyProbabilityMark,creditPc] using h

end PTX.Kernels.TmlFa4Fwd.Thread.Scores

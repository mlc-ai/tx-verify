-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTmemStores
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
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
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Lemmas.Flow.ContinuingEvent
import Lemmas.Order.OrderWaits
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame

private def unguardedStoreWait : Instr → Bool
  | ⟨none, .tcWaitSt⟩ => true
  | _ => false

private def straightStoreWindow (ins : Instr) : Bool :=
  (ins.op.isLocal || Epilogue.ordinaryEvent ins.op) && !barOp ins.op &&
    match ins.op with
    | .bra .. | .brx .. => false
    | _ => true

private def storeWindow (lo wait : Nat) : Bool :=
  ((kernel.code.drop lo).take (wait+1-lo)).all straightStoreWindow &&
    (kernel.code[wait]?.map unguardedStoreWait == some true) &&
    !(Assumptions.swExp2Sites.any (fun pc => lo ≤ pc && pc ≤ wait))

/-- A store followed by the explicit wait of its probability or rescale window. -/
@[no_expose] def ExplicitWaitStore (X : Execution) (i : EvId) : Prop :=
  ∃ site lo wait address values shape, lo ≤ site ∧ site < wait ∧ storeWindow lo wait = true ∧
    X.get i = some ⟨site, .tc (.st address values shape)⟩

private def probabilityWindowStart (round : Softmax.Round) (last : Bool) : Nat :=
  Softmax.probabilityPc round (if last then 3 else 0)

private theorem probabilityStoreWindows (round : Softmax.Round) (last : Bool) :
    storeWindow (probabilityWindowStart round last) (Softmax.probabilityWaitPc round last) = true :=
  by cases round <;> cases last <;> decide +kernel

private theorem probabilityWindowBounds (round : Softmax.Round) : ∀ q : Fin 4,
    probabilityWindowStart round (decide (q = 3)) ≤ Softmax.probabilityPc round q ∧
      Softmax.probabilityPc round q < Softmax.probabilityWaitPc round (decide (q = 3)) := by
  cases round <;> decide

theorem ExplicitWaitStore.probability {X : Execution} {i : EvId} {address : Nat}
    {values : List Value} {shape : TcShape} (round : Softmax.Round) (quarter : Fin 4)
    (he : X.get i = some ⟨Softmax.probabilityPc round quarter, .tc (.st address values shape)⟩) :
    ExplicitWaitStore X i := by
  let last := decide (quarter = 3)
  have h := probabilityWindowBounds round quarter
  exact ⟨_, _, _, _, _, _, h.1, h.2, probabilityStoreWindows round last, he⟩

private def rescaleWait (stage : Fin 2) : Nat := 8221 + 219 * stage.val

private theorem rescaleStoreWindows (stage : Fin 2) :
    storeWindow (TmlFa4Fwd.Correction.rescaleStorePc stage 0) (rescaleWait stage) = true := by
  fin_cases stage <;> decide +kernel

theorem ExplicitWaitStore.rescale {X : Execution} {i : EvId} {address : Nat}
    {values : List Value} {shape : TcShape} (stage : Fin 2) (chunk : Fin 8)
    (he : X.get i = some
      ⟨TmlFa4Fwd.Correction.rescaleStorePc stage chunk, .tc (.st address values shape)⟩) :
    ExplicitWaitStore X i := by
  have hLo : TmlFa4Fwd.Correction.rescaleStorePc stage 0 ≤
      TmlFa4Fwd.Correction.rescaleStorePc stage chunk := by
    simp [TmlFa4Fwd.Correction.rescaleStorePc]
  have hHi : TmlFa4Fwd.Correction.rescaleStorePc stage chunk < rescaleWait stage := by
    have hChunk := chunk.isLt
    unfold rescaleWait TmlFa4Fwd.Correction.rescaleStorePc
    omega
  exact ⟨_, _, _, _, _, _, hLo, hHi, rescaleStoreWindows stage, he⟩

private theorem storeWaitCode {lo wait : Nat} (h : storeWindow lo wait = true) :
    kernel.code[wait]? = some ⟨none, .tcWaitSt⟩ := by
  simp only [storeWindow, Bool.and_eq_true] at h
  obtain ⟨⟨guard, op⟩, hc, hs⟩ := Option.map_eq_some_iff.mp (beq_iff_eq.mp h.1.2)
  cases guard <;> cases op <;> simp [unguardedStoreWait] at hs hc
  exact hc

private theorem storeWindowCode {lo wait pc : Nat} {ins : Instr} (h : storeWindow lo wait = true)
    (hLo : lo ≤ pc) (hHi : pc ≤ wait) (hc : kernel.code[pc]? = some ins) :
    straightStoreWindow ins = true := by
  simp only [storeWindow, Bool.and_eq_true] at h
  apply List.all_eq_true.mp h.1.1 ins
  apply List.mem_of_getElem? (i := pc-lo)
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]

private theorem storeWindowTau {l : Launch} {g lo wait : Nat} {s u : TState}
    (h : storeWindow lo wait = true) (hLo : lo ≤ s.pc) (hHi : s.pc ≤ wait)
    (ht : Tau kernel Assumptions.all l g s u) : lo ≤ u.pc ∧ u.pc ≤ wait := by
  obtain ⟨ins, hc, _, hExec⟩ := Softmax.tauScoreSource ht
  have hStrict : s.pc < wait := by
    by_contra! heq
    have hAt : s.pc = wait := by omega
    rw [hAt, storeWaitCode h] at hc
    obtain rfl := Option.some.inj hc.symm
    rcases hExec with ⟨_, hg⟩ | ⟨_, hl, _⟩
    · cases hg
    · cases hl
  rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
  · change lo ≤ s.pc+1 ∧ s.pc+1 ≤ wait
    omega
  rcases Softmax.scoreExecLocal hLocal with hFrame | ⟨_, hSite, _, _⟩
  · have hn := hFrame.pc
    have hAudit := storeWindowCode h hLo hHi hc
    cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hn
    case bra | brx => simp [straightStoreWindow, ho] at hAudit
    all_goals omega
  · have hNone := (Bool.and_eq_true_iff.mp h).2
    have hSome : Assumptions.swExp2Sites.any (fun pc => lo ≤ pc && pc ≤ wait) = true :=
      List.any_eq_true.mpr ⟨_, hSite, by simp [hLo, hHi]⟩
    rw [hSome] at hNone
    cases hNone

private theorem storeWindowEvent {p : Params} {l : Launch} {m : Mem0} {g lo wait : Nat}
    {s u : TState} {e : Event} (hp : Pre p l m) (h : storeWindow lo wait = true)
    (hLo : lo ≤ s.pc) (hHi : s.pc ≤ wait)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    e.kind = .tc .waitSt ∨ (lo ≤ u.pc ∧ u.pc ≤ wait) := by
  obtain ⟨ins, hc, hLocal, hFire⟩ := estep_event_source he
  by_cases hAt : s.pc = wait
  · rw [hAt, storeWaitCode h] at hc
    obtain rfl := Option.some.inj hc.symm
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    simp only [eventTmpl, tcTmpl, hBlock, ofExec, pure, Except.pure, ↓reduceIte] at hFire
    exact .inl (congrArg Event.kind hFire.1)
  have hAudit := storeWindowCode h hLo hHi hc
  simp only [straightStoreWindow, Bool.and_eq_true, hLocal, Bool.false_or] at hAudit
  have hProgress := callbackFrame_fires (Epilogue.ordinaryEventFrame hAudit.1.1) hFire
  exact .inr (by rcases hProgress with heq | heq <;> omega)

private theorem storeWindowTrace {p : Params} {l : Launch} {m : Mem0} {g lo wait : Nat}
    {s u : TState} {events : List Event} (hp : Pre p l m) (h : storeWindow lo wait = true)
    (hr : TraceReach kernel Assumptions.all l g s events u) (hLo : lo ≤ s.pc) (hHi : s.pc ≤ wait) :
    (∃ e ∈ events, e.kind = .tc .waitSt) ∨ (lo ≤ u.pc ∧ u.pc ≤ wait) := by
  induction hr with
  | refl => exact .inr ⟨hLo,hHi⟩
  | tau ht _ ih =>
    obtain ⟨hl,hh⟩ := storeWindowTau h hLo hHi ht
    exact ih hl hh
  | event he _ ih =>
    rcases storeWindowEvent hp h hLo hHi he with hd | ⟨hl,hh⟩
    · exact .inl ⟨_, by simp, hd⟩
    · rcases ih hl hh with ⟨e, hIn, hw⟩ | hBounds
      · exact .inl ⟨e, List.mem_cons_of_mem _ hIn, hw⟩
      · exact .inr hBounds

private theorem storeWaitBetween {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index finish site lo wait address : Nat} {values : List Value} {shape : TcShape}
    {later : Event} (hLo : lo ≤ site) (hHi : site < wait) (hWindow : storeWindow lo wait = true)
    (he : X.get (g,index) = some ⟨site,.tc (.st address values shape)⟩)
    (hLater : X.get (g,finish) = some later) (hAfter : index < finish)
    (hOutside : ¬ (lo ≤ later.pc ∧ later.pc ≤ wait)) :
    ∃ k, (∃ tag, X.get (g,k) = some ⟨tag,.tc .waitSt⟩) ∧
      index < k ∧ po X (g,k) (g,finish) := by
  have hLength : finish < (X.tr g).length := PTX.len_of_get hLater
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s,u,hStep,hTail⟩ := hr.after_event he (by omega)
  have hs : s.pc = site := (estep_source_pc hStep).symm
  have hU : lo ≤ u.pc ∧ u.pc ≤ wait := by
    rcases storeWindowEvent hp hWindow (by omega) (by omega) hStep with hBad | hBounds
    · cases hBad
    · exact hBounds
  let stop := finish-(index+1)
  have hTarget : ((X.tr g).drop (index+1))[stop]? = some later := by
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega : index+1 ≤ finish)]
    exact hLater
  obtain ⟨v,_,hReach,hNext⟩ := hTail.before_event hTarget
  rcases storeWindowTrace hp hWindow hReach hU.1 hU.2 with ⟨e,hMem,hKind⟩ | ⟨hFloor,hLimit⟩
  · obtain ⟨k,hIndex⟩ := List.mem_iff_getElem?.mp hMem
    have hLt : k < stop := by
      have hLen := (List.getElem?_eq_some_iff.mp hIndex).1
      simp only [List.length_take,Nat.lt_min] at hLen
      omega
    rw [List.getElem?_take_of_lt hLt,List.getElem?_drop] at hIndex
    obtain ⟨tag,kind⟩ := e
    cases hKind
    let waitIndex := index+1+k
    have hWait : X.get (g,waitIndex) = some ⟨tag,.tc .waitSt⟩ := hIndex
    exact ⟨waitIndex,⟨tag,hWait⟩,by dsimp [waitIndex]; omega,
      po_of_source_not_access rfl (by dsimp [waitIndex]; omega) hLength (by rw [hWait]; rfl)⟩
  · have hPc : later.pc = v.pc := estep_source_pc hNext
    exact (hOutside (hPc.symm ▸ ⟨hFloor,hLimit⟩)).elim

/-- The ordinary correction store of a physical output rescale stage. -/
@[no_expose] def OutputRescaleStore (X : Execution) (store : EvId) (stage : Fin 2) : Prop :=
  ∃ (chunk : Fin 8) (address : Nat) (values : List Value) (shape : TcShape),
    X.get store = some ⟨Correction.rescaleStorePc stage chunk,.tc (.st address values shape)⟩

/-- The actual decoded instruction issuing this rescale store. -/
theorem OutputRescaleStore.decoded {X : Execution} {store : EvId} {stage : Fin 2}
    (h : OutputRescaleStore X store stage) :
    ∃ (chunk : Fin 8) (address : Nat) (values : List Value) (shape : TcShape),
      X.get store = some ⟨Correction.rescaleStorePc stage chunk,.tc (.st address values shape)⟩ :=
  h

/-- Record a realized correction rescale store of the decoded stage. -/
theorem OutputRescaleStore.ofDecoded {X : Execution} {store : EvId} (stage : Fin 2)
    (chunk : Fin 8) {address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get store = some
      ⟨Correction.rescaleStorePc stage chunk,.tc (.st address values shape)⟩) :
    OutputRescaleStore X store stage := ⟨chunk,address,values,shape,he⟩

/-- The correction lane's first probability credit at the end of the rescale window. -/
@[no_expose] def OutputRescaleCredit (X : Execution) (credit : EvId) (stage : Fin 2) : Prop :=
  ∃ loc tx units release scope,
    X.get credit = some ⟨8223+219*stage.val,.arrive loc tx units release scope⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The decoded credit contributes one unit to the stage's early probability packet. -/
theorem OutputRescaleCredit.probability {credit : EvId} {stage : Fin 2}
    (h : OutputRescaleCredit X credit stage) :
    Scores.ProbabilityCredit l X credit (credit.1/l.block) stage 0 := by
  obtain ⟨g,index⟩ := credit
  obtain ⟨loc,tx,units,release,scope,he⟩ := h
  have hSite : 8223+219*stage.val ∈ [7752,7754,8223,8442,8759,9055] := by
    fin_cases stage <;> decide
  obtain ⟨rfl,rfl,rfl,rfl,_,_⟩ := Correction.correctionProbabilityCredit hp hX he hSite
  have hMem : 8223+219*stage.val ∈ [7752,7754,7987,8223,8224,8442,8443,8464,8468,
      8759,8760,8764,9055,9056] := by fin_cases stage <;> decide
  have hLoc := Correction.correctionArriveAddressExact hp hX he hMem
  have hSame : loc = Scores.probabilityObject l (g/l.block) stage 0 := by
    rw [hLoc]
    fin_cases stage <;> rfl
  exact ⟨_,hSame ▸ he⟩

/-- A later joint probability credit on the correction lane follows the rescale store wait. -/
theorem outputRescaleDoneThroughJointCredit {store credit consumer : EvId} (stage : Fin 2)
    (hStore : OutputRescaleStore X store stage)
    (hCredit : Scores.ProbabilityCredit l X credit (store.1/l.block) stage 0)
    (hBefore : TraceBefore X store credit) (hConsumers : baseCausality l X credit consumer) :
    TcMma.StoreDoneBefore l X store consumer := by
  obtain ⟨g,index⟩ := store
  obtain ⟨h,finish⟩ := credit
  have hLane : g = h := hBefore.1
  subst h
  obtain ⟨chunk,address,vals,shape,he⟩ := hStore
  obtain ⟨source,hr⟩ := hCredit
  have hChunk := chunk.isLt
  have hLo : Correction.rescaleStorePc stage 0 ≤ Correction.rescaleStorePc stage chunk := by
    simp [Correction.rescaleStorePc]
  have hHi : Correction.rescaleStorePc stage chunk < rescaleWait stage := by
    unfold rescaleWait Correction.rescaleStorePc
    omega
  have hOff : 96+8*stage.val+16*(0 : Fin 2).val ∈ [96,104,112,120] := by
    fin_cases stage <;> decide
  have hSite := actualProbabilityArrivalSite hp hX hr hOff rfl
  have hOutside : ¬ (Correction.rescaleStorePc stage 0 ≤ source ∧ source ≤ rescaleWait stage) := by
    rcases hSite with ⟨q,rfl⟩ | hSites
    · fin_cases stage <;> fin_cases q <;> decide
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hSites
      rcases hSites with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases stage <;> decide
  obtain ⟨k,hWait,hAfter,hPo⟩ := storeWaitBetween hp hX hLo hHi (rescaleStoreWindows stage)
    he hr hBefore.2.1 hOutside
  exact ⟨⟨address,vals,shape,_,he⟩,.inl ⟨(g,k),hWait,rfl,hAfter,
    .inl ((Relation.TransGen.single (.inl hPo)).trans hConsumers)⟩⟩

omit hp hX in
/-- The first three stores of a softmax probability visit publish the joint packet. -/
@[no_expose] def EarlyProbabilityStore (X : Execution) (store : EvId) : Prop :=
  ∃ (round : Softmax.Round) (quarter : Fin 4) (address : Nat) (values : List Value)
    (shape : TcShape), quarter.val < 3 ∧
      X.get store = some ⟨Softmax.probabilityPc round quarter,.tc (.st address values shape)⟩

omit hp hX in
/-- The decoded early packet store in an actual trace. -/
theorem EarlyProbabilityStore.decoded {X : Execution} {store : EvId}
    (h : EarlyProbabilityStore X store) :
    ∃ (round : Softmax.Round) (quarter : Fin 4) (address : Nat) (values : List Value)
      (shape : TcShape), quarter.val < 3 ∧
        X.get store = some ⟨Softmax.probabilityPc round quarter,.tc (.st address values shape)⟩ :=
  h

omit hp hX in
/-- Record a realized store in the first three quarters. -/
theorem EarlyProbabilityStore.ofDecoded {X : Execution} {store : EvId}
    (round : Softmax.Round) (quarter : Fin 4) {address : Nat} {values : List Value}
    {shape : TcShape} (hEarly : quarter.val < 3)
    (he : X.get store = some
      ⟨Softmax.probabilityPc round quarter,.tc (.st address values shape)⟩) :
    EarlyProbabilityStore X store :=
  ⟨round,quarter,address,values,shape,hEarly,he⟩

/-- An actual early probability store finishes before a later joint credit of its lane. -/
theorem earlyProbabilityDoneThroughCredit (stage : Fin 2) {store credit consumer : EvId}
    (hStore : EarlyProbabilityStore X store)
    (hCredit : Scores.ProbabilityCredit l X credit (store.1/l.block) stage 0)
    (hBefore : TraceBefore X store credit) (hConsumers : baseCausality l X credit consumer) :
    TcMma.StoreDoneBefore l X store consumer := by
  obtain ⟨g,index⟩ := store
  obtain ⟨h,finish⟩ := credit
  have hLane : g = h := hBefore.1
  subst h
  obtain ⟨round,quarter,address,values,shape,hEarly,he⟩ := hStore
  obtain ⟨source,hGet⟩ := hCredit
  have hSite := actualProbabilityArrivalSite hp hX hGet
    (show 96+8*stage.val+16*(0 : Fin 2).val ∈ [96,104,112,120] by fin_cases stage <;> decide) rfl
  have hOutside : ¬ (probabilityWindowStart round false ≤ source ∧
      source ≤ Softmax.probabilityWaitPc round false) := by
    rcases hSite with ⟨arrival,rfl⟩ | hSites
    · cases round <;> fin_cases arrival <;> decide
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hSites
      rcases hSites with rfl | rfl | rfl | rfl | rfl | rfl <;> cases round <;> decide
  have hQ : quarter ≠ 3 := fun h => by subst quarter; exact (Nat.lt_irrefl 3) hEarly
  have hWindow := probabilityWindowBounds round quarter
  rw [decide_eq_false hQ] at hWindow
  obtain ⟨k,hWait,hAfter,hPo⟩ := storeWaitBetween hp hX hWindow.1 hWindow.2
    (probabilityStoreWindows round false) he hGet hBefore.2.1 hOutside
  exact ⟨⟨address,values,shape,_,he⟩,.inl ⟨(g,k),hWait,rfl,hAfter,
    .inl ((Relation.TransGen.single (.inl hPo)).trans hConsumers)⟩⟩

/-- Crossing the tail publication's warp rendezvous requires the actual tail-store wait. -/
theorem probabilityTailWaitBeforeWarpBarrier {g i j address mask inst : Nat} {values : List Value}
    {shape : TcShape} (round barrierRound : Softmax.Round)
    (he : X.get (g,i) = some ⟨Softmax.probabilityPc round 3,.tc (.st address values shape)⟩)
    (hBar : X.get (g,j) = some ⟨Softmax.probabilityWaitPc barrierRound true+1,.warpBar mask inst⟩)
    (hBefore : i < j) :
    ∃ w, (∃ site, X.get (g,w) = some ⟨site,.tc .waitSt⟩) ∧ i < w ∧ w < j := by
  have hWindow := probabilityWindowBounds round 3
  have hOutside : ¬ (probabilityWindowStart round true ≤
      Softmax.probabilityWaitPc barrierRound true+1 ∧
      Softmax.probabilityWaitPc barrierRound true+1 ≤ Softmax.probabilityWaitPc round true) := by
    cases round <;> cases barrierRound <;> decide
  obtain ⟨w,hWait,hAfter,hOrder⟩ := storeWaitBetween hp hX hWindow.1 hWindow.2
    (probabilityStoreWindows round true) he hBar hBefore hOutside
  exact ⟨w,hWait,hAfter,hOrder.2.1⟩

/-- An actual probability or rescale store completes before release in its CTA. -/
theorem explicitStoreCompletedBeforeRelease {i d : EvId} (hScope : i.1 / l.block = d.1 / l.block)
    (hStore : ExplicitWaitStore X i) (hd : Deallocation X d) :
    TcMma.WaitBefore l X .waitSt i d := by
  obtain ⟨g,index⟩ := i
  obtain ⟨site, lo, wait, _, _, _, hLo, hHi, hWindow, he⟩ := hStore
  have hData : TensorDataEvent X (g,index) := ⟨_, he, .inl rfl⟩
  obtain ⟨finish, mode, hAfter, hFinal⟩ :=
    (tensorDataFinalArrivalBeforeDeallocation hp hX hScope hData hd).1
  obtain ⟨source, _, hFinalGet⟩ := hFinal.decoded
  have hLength : finish < (X.tr g).length := PTX.len_of_get hFinalGet
  obtain ⟨_, hr⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s,u,hStep,hTail⟩ := hr.after_event he (by omega)
  have hs : s.pc = site := (estep_source_pc hStep).symm
  have hU : lo ≤ u.pc ∧ u.pc ≤ wait := by
    rcases storeWindowEvent hp hWindow (by omega) (by omega) hStep with hBad | hBounds
    · cases hBad
    · exact hBounds
  let stop := finish-(index+1)
  have hTerm : ((X.tr g).drop (index+1))[stop]? = some ⟨source, .bar 2 (some 416) mode⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega : index+1 ≤ finish)]
    exact hFinalGet
  obtain ⟨v, _, hReach, hExit⟩ := hTail.before_event hTerm
  rcases storeWindowTrace hp hWindow hReach hU.1 hU.2 with ⟨e, hm, hk⟩ | ⟨hFloor,hLimit⟩
  · obtain ⟨k, hIndex⟩ := List.mem_iff_getElem?.mp hm
    have hLt : k < stop := by
      have hLen := (List.getElem?_eq_some_iff.mp hIndex).1
      simp only [List.length_take, Nat.lt_min] at hLen
      omega
    rw [List.getElem?_take_of_lt hLt, List.getElem?_drop] at hIndex
    obtain ⟨waitSite, kind⟩ := e
    cases hk
    have hWait : X.get (g,index+1+k) = some ⟨waitSite, .tc .waitSt⟩ := hIndex
    exact ⟨_, ⟨waitSite,hWait⟩, rfl, by omega,
      .inl (tensorDataBeforeDeallocation hp hX hScope ⟨_, hWait, .inl rfl⟩ hd)⟩
  · have hv : source = v.pc := estep_source_pc hExit
    rcases get_source hX hFinalGet with ⟨_, hf⟩ | ⟨_, _, _, _, hc, hf⟩
    · cases hf
    have hBar := fires_bar_op hf rfl
    rw [hv] at hc
    have hAudit := storeWindowCode hWindow hFloor hLimit hc
    simp [straightStoreWindow, hBar] at hAudit

/-- Every actual Tensor Memory store in the releasing CTA has completed. -/
theorem tensorStoreCompletedBeforeRelease {i d : EvId} {address : Nat} {values : List Value}
    {shape : TcShape} (hScope : i.1 / l.block = d.1 / l.block)
    (hStore : X.TSt i address values shape) (hd : Deallocation X d) :
    TcMma.WaitBefore l X .waitSt i d := by
  obtain ⟨_, he⟩ := hStore
  apply explicitStoreCompletedBeforeRelease hp hX hScope _ hd
  rcases tensorStoreSite hX he with ⟨round, quarter, rfl⟩ | ⟨stage, chunk, rfl⟩
  · exact ExplicitWaitStore.probability round quarter he
  · exact ExplicitWaitStore.rescale stage chunk he

end PTX.Kernels.TmlFa4Fwd.Thread

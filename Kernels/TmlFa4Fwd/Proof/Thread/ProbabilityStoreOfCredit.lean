-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstPack
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
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
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.TmemTailProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Execution.EventFrameBase
import Lemmas.Flow.WaitAcquire
import Lemmas.Flow.EventCont
import Lemmas.Flow.Next
import Lemmas.Flow.NotWarpBar
public import Lemmas.Order.WarpBarOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Softmax Prologue

private def publicationSite : Softmax.Round → Nat
  | .first => (probabilityArrivalSite 0).pc
  | .biased => (probabilityArrivalSite 2).pc
  | .unbiased => (probabilityArrivalSite 4).pc

private def endSite (round : Softmax.Round) (quarter : Fin 4) : Nat :=
  if quarter = 3 then Softmax.probabilityWaitPc round true+1 else publicationSite round

private def PassedStore (round : Softmax.Round) (quarter : Fin 4) (pc : Nat) : Prop :=
  Softmax.probabilityPc round quarter < pc ∧ pc ≤ endSite round quarter

private instance (round : Softmax.Round) (quarter : Fin 4) (pc : Nat) :
    Decidable (PassedStore round quarter pc) :=
  inferInstanceAs (Decidable (_ < _ ∧ _ ≤ _))

private def entersPublication (round : Softmax.Round) (quarter : Fin 4) (site : Nat)
    (ins : Instr) : Bool :=
  match ins.op with
  | .bra target _ => !decide (PassedStore round quarter target) ||
      decide (PassedStore round quarter site)
  | .brx .. => false
  | _ => true

private theorem publicationIngressAt (round : Softmax.Round) (quarter : Fin 4) {pc : Nat}
    {ins : Instr} (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some ins) :
    entersPublication round quarter pc ins = true := by
  let code := ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103
  have h : code.all (fun (ins,pc) => entersPublication round quarter pc ins) = true := by
    cases round <;> fin_cases quarter <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h (ins,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

private theorem softmaxReturningOpcode {pc : Nat} {i : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some i)
    (hl : i.op.isLocal = false) : Epilogue.ordinaryEvent i.op = true := by
  let code := (kernel.code.drop 3103).take (7742-3103)
  have h : code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hMember : i ∈ code := by
    apply List.mem_of_getElem? (i := pc-3103)
    dsimp only [code]
    have hN : pc-3103 < 7742-3103 := by omega
    rw [List.getElem?_take_of_lt hN,List.getElem?_drop,Nat.add_sub_of_le hLo,hc]
  simpa [hl] using List.all_eq_true.mp h i hMember

private def outsidePublications (site : Nat) : Bool :=
  decide ((site ≤ 4826 ∨ 4858 < site) ∧ (site ≤ 6508 ∨ 6543 < site) ∧
    (site ≤ 7416 ∨ 7448 < site))

set_option maxRecDepth 100000 in
private theorem segmentStopsOutsidePublications :
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | some seg => outsidePublications seg.stop
      | none => false) = true := by kernel_rfl

private theorem segmentOutsidePublication (round : Softmax.Round) (quarter : Fin 4)
    {pc : Nat} {segment : SegMatch CuteSlot}
    (hMem : pc ∈ Assumptions.swExp2Sites) (hSeg : cuteExp2.matchAt kernel pc = some segment) :
    ¬ PassedStore round quarter segment.stop := by
  have hCheck := List.all_eq_true.mp segmentStopsOutsidePublications pc hMem
  rw [hSeg] at hCheck
  have h : outsidePublications segment.stop = true := hCheck
  simp only [outsidePublications,decide_eq_true_eq] at h
  intro hIn
  obtain ⟨hl,hh⟩ := hIn
  have limits : ∀ r : Softmax.Round, ∀ q : Fin 4,
      match r with
      | .first => 4826 ≤ Softmax.probabilityPc r q ∧ endSite r q ≤ 4858
      | .biased => 6508 ≤ Softmax.probabilityPc r q ∧ endSite r q ≤ 6543
      | .unbiased => 7416 ≤ Softmax.probabilityPc r q ∧ endSite r q ≤ 7448 := by
    intro r q
    cases r <;> fin_cases q <;> decide
  have hLimits := limits round quarter
  cases round with
  | first => rcases h.1 with hm | hm <;> have := hLimits.1 <;> have := hLimits.2 <;> omega
  | biased => rcases h.2.1 with hm | hm <;> have := hLimits.1 <;> have := hLimits.2 <;> omega
  | unbiased => rcases h.2.2 with hm | hm <;> have := hLimits.1 <;> have := hLimits.2 <;> omega

private theorem returningCoreStore {l : Launch} {g : Nat} {s u : TState}
    {e : Event} {dst : Nat} {values : List Opnd} {site : Nat}
    (hFire : Fires site (tcTmpl l g s (.tcSt dst values .s32x32b)) e (some u)) :
    ∃ addr words, e.kind = .tc (.st addr words .s32x32b) := by
  have ofExecStore (f : Exec Tmpl) (hAll : AllOk
      (fun tm => ∃ addr words t, tm = Tmpl.tc (.st addr words .s32x32b) t) f)
      (hf : Fires site (ofExec f) e (some u)) :
      ∃ addr words, e.kind = .tc (.st addr words .s32x32b) := by
    cases f with
    | error => cases hf.2
    | ok tm =>
      obtain ⟨addr,words,_,rfl⟩ := hAll
      exact ⟨addr,words,congrArg Event.kind hf.1⟩
  rw [tcTmpl_tcSt_plain (by intro q h; cases h)] at hFire
  apply ofExecStore _ _ hFire
  repeat' first | (apply allOk_bind; intro) | (apply allOk_ite)
  all_goals exact ⟨_,_,_,rfl⟩

private theorem publishStoreOnAdvance {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (round : Softmax.Round) (quarter : Fin 4)
    (hAt : s.pc = Softmax.probabilityPc round quarter) (hNext : u.pc = s.pc+1)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ addr words, e = ⟨Softmax.probabilityPc round quarter,.tc (.st addr words .s32x32b)⟩ := by
  obtain ⟨_,_,hc⟩ := Softmax.probabilityCode round quarter
  obtain ⟨ins,hCode,_,hf⟩ := estep_event_source he
  rw [hAt,hc] at hCode
  obtain rfl := Option.some.inj hCode.symm
  have hStore : ∃ addr words, e.kind = .tc (.st addr words .s32x32b) := by
    simp only [eventTmpl,tcStTmpl] at hf
    split at hf
    · split at hf
      · split at hf
        · have hSame := congrArg TState.pc (Option.some.inj hf.2)
          dsimp only at hSame
          omega
        · cases hf.2
      · exact returningCoreStore hf
    · exact returningCoreStore hf
  obtain ⟨addr,words,hKind⟩ := hStore
  have hSite := (estep_source_pc he).trans hAt
  obtain ⟨actualSite,kind⟩ := e
  change actualSite = _ at hSite
  change kind = _ at hKind
  exact ⟨addr,words,by rw [hSite,hKind]⟩

private def probabilityPublicationQuiet (op : Op) : Bool :=
  match op with
  | .mbarWait .. | .mbarArrive .. => false
  | .warp warp => warp.kind != .barWarp
  | _ => true

private theorem probabilityPublicationQuietCode (round : Softmax.Round) (quarter : Fin 4)
    {pc : Nat} {ins : Instr} (hLo : Softmax.probabilityPc round quarter ≤ pc)
    (hHi : pc < endSite round quarter) (hc : kernel.code[pc]? = some ins) :
    probabilityPublicationQuiet ins.op = true := by
  let start := Softmax.probabilityPc round quarter
  let code := (kernel.code.drop start).take (endSite round quarter-start)
  have h : code.all (fun i => probabilityPublicationQuiet i.op) = true := by
    cases round <;> fin_cases quarter <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp h ins
  apply List.mem_of_getElem? (i := pc-start)
  dsimp only [code,start]
  rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hc]

private theorem probabilityPublicationQuietEvent {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (round : Softmax.Round) (quarter : Fin 4)
    (hLo : Softmax.probabilityPc round quarter ≤ s.pc) (hHi : s.pc < endSite round quarter)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∀ loc, okPoll loc e = false ∧ arrivesOn loc e = false ∧
      Execution.isWarpBar e = false := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  have hQuiet := probabilityPublicationQuietCode round quarter hLo hHi hCode
  intro loc
  refine ⟨okPoll_notWait ?_,?_,?_⟩
  · intro m parity ok acquire scope hKind
    obtain ⟨_,_,_,_,_,hOp,_⟩ := fires_wait_flags hFire hKind
    rw [hOp] at hQuiet
    cases hQuiet
  · unfold arrivesOn sourceArrive
    split
    next m tx count rel scope hKind =>
      obtain ⟨_,_,_,_,_,_,_,hOp,_⟩ := fires_arrive_flags hFire hKind
      rw [hOp] at hQuiet
      cases hQuiet
    next => rfl
  · have hNoBar := fires_notWarpBar_op (fun w ho => by
      rw [ho] at hQuiet
      simpa [probabilityPublicationQuiet] using hQuiet) hFire
    obtain ⟨site,kind⟩ := e
    cases kind <;> try rfl
    rename_i mask inst
    exact (hNoBar mask inst rfl).elim

private theorem probabilityPublicationAdvances {l : Launch} {g : Nat} {s u : TState}
    {e : Event} (round : Softmax.Round) (quarter : Fin 4)
    (hSite : s.pc = endSite round quarter)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc+1 := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  by_cases hTail : quarter = 3
  · have hBar : kernel.code[s.pc]? =
      some ⟨none,.warp ⟨.barWarp,none,[],[],some (.imm (-1))⟩⟩ := by
      rw [hSite,endSite,ite_eq_left hTail]
      cases round
      · exact Flow.code_4858
      · exact Flow.code_6543
      · exact Flow.code_7448
    obtain rfl := Option.some.inj (hCode.symm.trans hBar)
    exact congrArg TState.pc (fires_next (by trivial) hFire)
  · have hArrival : ∃ base count state, kernel.code[s.pc]? =
        some ⟨none,.mbarArrive base 96 (.imm 0) (.reg count) false true .cta (some state)⟩ := by
      rw [hSite,endSite,ite_eq_right hTail]
      cases round
      · exact ⟨_,_,_,Flow.code_4847⟩
      · exact ⟨_,_,_,Flow.code_6532⟩
      · exact ⟨_,_,_,Flow.code_7437⟩
    obtain ⟨_,_,_,hArrival⟩ := hArrival
    obtain rfl := Option.some.inj (hCode.symm.trans hArrival)
    exact congrArg TState.pc (fires_arrive_state hFire).1

private def PublicationCursor (X : Execution) (g store cut : Nat) : Prop :=
  warpBars X g store = warpBars X g cut ∧
    ∀ loc, okPolls loc ((X.tr g).take store) = okPolls loc ((X.tr g).take cut) ∧
      ((X.tr g).take store).countP (arrivesOn loc) = ((X.tr g).take cut).countP (arrivesOn loc)

private def PublicationRegion (X : Execution) (g : Nat) (round : Softmax.Round)
    (quarter : Fin 4) (store cut : Nat) : Prop :=
  ∀ j e, store < j → j < cut → X.get (g,j) = some e → PassedStore round quarter e.pc

private def StorePassed (X : Execution) (g : Nat) (round : Softmax.Round) (quarter : Fin 4)
    (pos : Nat) (s : TState) : Prop :=
  PassedStore round quarter s.pc →
    ∃ k < pos, ∃ addr vals,
      X.get (g,k) = some ⟨Softmax.probabilityPc round quarter,.tc (.st addr vals .s32x32b)⟩ ∧
      PublicationCursor X g k pos ∧ PublicationRegion X g round quarter k pos

private theorem advanceStoreSeen {l : Launch} {X : Execution} {g pos : Nat}
    {s u : TState} {ev : Option Event} (round : Softmax.Round) (quarter : Fin 4)
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hGet : ∀ e, ev = some e → X.get (g,pos) = some e)
    (hHave : StorePassed X g round quarter pos s) :
    StorePassed X g round quarter (pos+ev.toList.length) u := by
  intro hNew
  have finish (prior : Nat) (hPrev : PublicationCursor X g prior pos)
      (hQuiet : ∀ loc e, ev = some e →
        okPoll loc e = false ∧ arrivesOn loc e = false ∧ Execution.isWarpBar e = false) :
      PublicationCursor X g prior (pos+ev.toList.length) := by
    cases ev with
    | none => exact hPrev
    | some e =>
      have hAt : (X.tr g)[pos]? = some e := hGet e rfl
      unfold PublicationCursor warpBars at hPrev ⊢
      rw [show (some e).toList.length = 1 by rfl,List.take_add_one,hAt,Option.toList_some]
      refine ⟨?_,?_⟩
      · simpa [List.countP_append,(hQuiet ⟨.shared,0,0⟩ e rfl).2.2] using hPrev.1
      · intro loc
        obtain ⟨hWait,hCredit⟩ := hPrev.2 loc
        obtain ⟨hQWait,hQCredit,_⟩ := hQuiet loc e rfl
        exact ⟨by simpa [okPolls_snoc,hQWait] using hWait,
          by simpa [List.countP_append,hQCredit] using hCredit⟩
  have lift (hPrev : PassedStore round quarter s.pc)
      (hQuiet : ∀ loc e, ev = some e →
        okPoll loc e = false ∧ arrivesOn loc e = false ∧ Execution.isWarpBar e = false) :
      ∃ k < pos+ev.toList.length, ∃ addr vals,
        X.get (g,k) = some ⟨Softmax.probabilityPc round quarter,.tc (.st addr vals .s32x32b)⟩ ∧
        PublicationCursor X g k (pos+ev.toList.length) ∧
        PublicationRegion X g round quarter k (pos+ev.toList.length) := by
    obtain ⟨k,hK,addr,vals,hStore,hCursor,hRegion⟩ := hHave hPrev
    refine ⟨k,lt_of_lt_of_le hK (Nat.le_add_right ..),addr,vals,hStore,finish k hCursor hQuiet,?_⟩
    intro j f hKj hJ hGetJ
    by_cases hLt : j < pos
    · exact hRegion j f hKj hLt hGetJ
    rcases hStep with ⟨rfl,_⟩ | ⟨e,rfl,he⟩
    · simp at hJ
      omega
    · have hEq : j = pos := by simp at hJ; omega
      subst j
      obtain rfl := Option.some.inj ((hGet e rfl).symm.trans hGetJ)
      exact (estep_source_pc he).symm ▸ hPrev
  have hFall (hPc : u.pc = s.pc+1) :
      PassedStore round quarter s.pc ∨ s.pc = Softmax.probabilityPc round quarter := by
    have := hNew.1
    have := hNew.2
    by_cases hHead : s.pc = Softmax.probabilityPc round quarter
    · exact .inr hHead
    · exact .inl ⟨by omega,by omega⟩
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have noEvent (loc : Loc) (e : Event) (h : none = some e) :
        okPoll loc e = false ∧ arrivesOn loc e = false ∧ Execution.isWarpBar e = false := by cases h
    obtain ⟨ins,hCode,_,hLocal⟩ := tauScoreSource ht
    have hHead : s.pc ≠ Softmax.probabilityPc round quarter := by
      intro hPc
      obtain ⟨_,_,hStore⟩ := Softmax.probabilityCode round quarter
      rw [hPc,hStore] at hCode
      obtain rfl := Option.some.inj hCode.symm
      rcases hLocal with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
      · cases hGuard
      · cases hLocal
    rcases hLocal with ⟨rfl,_⟩ | ⟨_,_,hl⟩
    · exact lift ((hFall rfl).resolve_right hHead) noEvent
    rcases scoreExecLocal hl with hLocal | ⟨seg,hSite,hMatch,hSeg⟩
    · have hPc := hLocal.pc
      have hAudit := publicationIngressAt round quarter hLo hHi hCode
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra target uniform =>
        exact lift (by simpa [entersPublication,hOp,hPc ▸ hNew] using hAudit) noEvent
      case brx => simp [entersPublication,hOp] at hAudit
      all_goals exact lift ((hFall hPc).resolve_right hHead) noEvent
    · have hPc := (scoreSegmentFrame hSeg).1
      exact (segmentOutsidePublication round quarter hSite hMatch (hPc ▸ hNew)).elim
  · obtain ⟨ins,hCode,hLocal,hFire⟩ := estep_event_source he
    have hOrd := softmaxReturningOpcode hLo hHi hCode hLocal
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrd) hFire with hSame | hNext
    · have hPrev := hSame ▸ hNew
      have hLimit := hPrev.2
      by_cases hEnd : s.pc = endSite round quarter
      · have hAfter := probabilityPublicationAdvances round quarter hEnd he
        omega
      · exact lift hPrev (fun loc f h => Option.some.inj h ▸
          probabilityPublicationQuietEvent round quarter hPrev.1.le (by omega) he loc)
    have hLimit := hNew.2
    have hHi : s.pc < endSite round quarter := by omega
    rcases hFall hNext with hPrev | hHead
    · exact lift hPrev (fun loc f h => Option.some.inj h ▸
        probabilityPublicationQuietEvent round quarter hPrev.1.le hHi he loc)
    obtain ⟨addr,vals,hStore⟩ := publishStoreOnAdvance round quarter hHead hNext he
    refine ⟨pos,by simp,addr,vals,hStore ▸ hGet e rfl,
      finish pos ⟨rfl,fun _ => ⟨rfl,rfl⟩⟩ ?_,?_⟩
    · exact fun loc f h => Option.some.inj h ▸
        probabilityPublicationQuietEvent round quarter hHead.ge hHi he loc
    · intro j f hAfter hBefore hGet
      simp at hBefore
      omega

section
variable {p : Params} {l : Launch}

/-- The actual publication cut has been preceded by the corresponding store of its lane. -/
private theorem probabilityStoreBeforePublication {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (round : Softmax.Round) (quarter : Fin 4)
    {g pos : Nat} {e : Event} (he : X.get (g,pos) = some e) (hEnd : e.pc = endSite round quarter) :
    ∃ k < pos, ∃ addr vals,
      X.get (g,k) = some ⟨Softmax.probabilityPc round quarter,.tc (.st addr vals .s32x32b)⟩ ∧
      PublicationCursor X g k pos ∧ PublicationRegion X g round quarter k pos := by
  have bounds : 3420 ≤ endSite round quarter ∧ endSite round quarter < 7742 ∧
      PassedStore round quarter (endSite round quarter) ∧
      ¬ PassedStore round quarter 3103 := by
    cases round <;> fin_cases quarter <;> decide
  have hLo : 3420 ≤ e.pc := hEnd.symm ▸ bounds.1
  have hHi : e.pc < 7742 := hEnd.symm ▸ bounds.2.1
  obtain ⟨s,_,hFrame,hStep⟩ := softmaxRoleReplayAt hp hX he hLo hHi
    (StorePassed X g round quarter)
    (fun _ _ _ hAt hInside => (bounds.2.2.2 (hAt.1 ▸ hInside)).elim)
    (fun hLo hHi _ hInv hStep hActual =>
      advanceStoreSeen round quarter hLo hHi hStep hActual hInv)
  have hSite : s.pc = endSite round quarter := (estep_source_pc hStep).symm.trans hEnd
  exact hFrame (hSite.symm ▸ bounds.2.2.1)

private theorem earlyPublicationOfCredit {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j cta : Nat} {stage : Fin 2}
    (hWarp : warpIndex l g < 8) (hCredit : ProbabilityCredit l X (g,j) cta stage 0) :
    ∃ round : Softmax.Round,
      X.get (g,j) = some ⟨publicationSite round,
        .arrive (probabilityObject l cta stage 0) 0 1 true .cta⟩ := by
  obtain ⟨source,hGet⟩ := hCredit
  have hOff : 96+8*stage.val ∈ ([96,104,112,120] : List Nat) := by fin_cases stage <;> decide
  rcases actualProbabilityArrivalSite hp hX hGet hOff rfl with ⟨slot,hSlot⟩ | hCorr
  · rw [hSlot] at hGet
    obtain ⟨_,_,_,_,_,hAddr⟩ := Softmax.probabilityArriveFacts hp hX slot hGet
    have hA : l.sharedBase+(96+8*stage.val) =
        l.sharedBase+((probabilityArrivalSite slot).offset+8*(warpIndex l g/4)) :=
      congrArg Loc.addr hAddr
    have hLimit : stage.val < 2 := stage.isLt
    have hEven : (probabilityArrivalSite slot).offset = 96 := by
      have audit : ∀ s : Fin 6, (probabilityArrivalSite s).offset = 96 ∨
          (probabilityArrivalSite s).offset = 112 := by decide
      rcases audit slot with h | h
      · exact h
      · omega
    have matchSite : ∀ s : Fin 6, (probabilityArrivalSite s).offset = 96 →
        ∃ r : Softmax.Round, (probabilityArrivalSite s).pc = publicationSite r := by
      intro s
      fin_cases s <;> intro h
      · exact ⟨.first,rfl⟩
      · cases h
      · exact ⟨.biased,rfl⟩
      · cases h
      · exact ⟨.unbiased,rfl⟩
      · cases h
    obtain ⟨round,hTag⟩ := matchSite slot hEven
    exact ⟨round,hTag ▸ hGet⟩
  · have hCorrRole := Correction.correctionProbabilityCredit hp hX hGet hCorr
    omega

private theorem probabilityStoreCellFromActual {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (round : Softmax.Round) (quarter : Fin 4)
    (word : Fin 16) {g k cta : Nat} {stage : Fin 2} {addr : Nat} {vals : List Value}
    (he : X.get (g,k) = some ⟨Softmax.probabilityPc round quarter,.tc (.st addr vals .s32x32b)⟩)
    (hCta : g/l.block = cta) (hBank : warpIndex l g/4 = stage.val) :
    TcMma.StoreCell l X (g,k)
      ⟨cta,laneBase l g+laneOf l g,probabilityColumn stage+16*quarter.val+word.val⟩ := by
  obtain ⟨w,hWarp,hAddr,hLen,_⟩ := probabilityStoreAddress hp hX round quarter he
  have hStage : stageOf w = stage := by
    apply Fin.ext
    change w.val/4 = stage.val
    rw [hWarp]
    exact hBank
  rw [hStage] at hAddr
  refine ⟨addr,vals,.s32x32b,word.val,⟨_,he⟩,hLen.symm ▸ word.isLt,?_⟩
  have hCol : probabilityColumn stage+16*quarter.val < 512 := by
    have hLimit := probabilityColumn_range stage
    have hScore := scoreColumn_range stage
    have := quarter.isLt
    omega
  rw [hAddr,probabilityAddress,tcDataCell_warp32 l g word.val hCol,hCta]

private theorem probabilityQuarterOutsidePublication (round other : Softmax.Round)
    (quarter : Fin 4) : ¬ PassedStore round quarter (probabilityPc other quarter) := by
  cases round <;> cases other <;> fin_cases quarter <;> decide

private theorem rivalProbabilityStoreOfQuarter {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j cta : Nat} {stage : Fin 2} (quarter : Fin 4)
    (word : Fin 16) (hBank : warpIndex l g/4 = stage.val)
    (hRival : TcMma.StoreCell l X (g,j) ⟨cta,laneBase l g+laneOf l g,
      probabilityColumn stage+16*quarter.val+word.val⟩) :
    ∃ round address values shape, X.get (g,j) =
      some ⟨probabilityPc round quarter,.tc (.st address values shape)⟩ := by
  obtain ⟨address,values,shape,index,⟨pc,hStore⟩,hIndex,hCell⟩ := hRival
  rcases tensorStoreSite hX hStore with ⟨rival,q,rfl⟩ | ⟨other,chunk,rfl⟩
  · obtain ⟨w,hWarp,rfl,hSize,rfl⟩ := probabilityStoreAddress hp hX rival q hStore
    have hStage : stageOf w = stage := Fin.ext (by change w.val/4 = stage.val; rw [hWarp,hBank])
    rw [hStage] at hCell
    rw [hSize] at hIndex
    have hEnd := probabilityColumn_range stage
    have hScore := scoreColumn_range stage
    have hQuarter := q.isLt
    have hCol : probabilityColumn stage + 16*q.val < 512 := by omega
    unfold probabilityAddress at hCell
    rw [tcDataCell_warp32 l g index hCol] at hCell
    have hColumn := congrArg TcMma.Cell.column hCell
    change probabilityColumn stage+16*quarter.val+word.val =
      probabilityColumn stage+16*q.val+index at hColumn
    have hWord := word.isLt
    have hQ : q = quarter := Fin.ext (by omega)
    exact ⟨rival,_,_,_,hQ ▸ hStore⟩
  · have hIssuer := correctionStoreWarpGroup hp hX other chunk hStore
    change g%l.block/128 = 2 at hIssuer
    unfold warpIndex at hBank
    have := stage.isLt
    omega

private theorem probabilityRivalOutsidePublication {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g k cut j : Nat} (round : Softmax.Round)
    (quarter : Fin 4) (word : Fin 16) (hRegion : PublicationRegion X g round quarter k cut)
    (hBefore : k < j) {cta : Nat} {stage : Fin 2} (hBank : warpIndex l g/4 = stage.val)
    (hRival : TcMma.StoreCell l X (g,j) ⟨cta,laneBase l g+laneOf l g,
      probabilityColumn stage+16*quarter.val+word.val⟩) : cut ≤ j := by
  by_contra! hAfter
  obtain ⟨rival,_,_,_,hStore⟩ := rivalProbabilityStoreOfQuarter hp hX quarter word hBank hRival
  exact probabilityQuarterOutsidePublication round rival quarter
    (hRegion j _ hBefore hAfter hStore)

/-- There is no other store of this quarter before the visit's publication
event on the producing lane. -/
@[no_expose] def ProbabilityStoreVisitSuffix (X : Execution) (g : Nat)
    (quarter : Fin 4) (store cut : Nat) : Prop :=
  ∀ (round : Softmax.Round) (j address : Nat) (values : List Value) (shape : TcShape),
    store < j → j < cut →
    X.get (g,j) ≠ some ⟨Softmax.probabilityPc round quarter,.tc (.st address values shape)⟩

/-- Check a recorded interval for another issue of its probability quarter. -/
theorem ProbabilityStoreVisitSuffix.ofEvents {X : Execution} {g start store cut : Nat}
    (quarter : Fin 4) (events : List Event)
    (hEvents : ∀ k (hk : k < events.length), X.get (g,start+k) = some events[k])
    (hStart : start ≤ store+1) (hStop : cut ≤ start+events.length)
    (hOther : ∀ (k : Nat) (hk : k < events.length), store < start+k → start+k < cut →
      ∀ (round : Softmax.Round) (address : Nat) (values : List Value) (shape : TcShape),
        events[k] ≠ ⟨Softmax.probabilityPc round quarter,.tc (.st address values shape)⟩) :
    ProbabilityStoreVisitSuffix X g quarter store cut := by
  intro round j address values shape hJ hCut he
  have hk : j-start < events.length := by omega
  have hPos : start+(j-start) = j := by omega
  have hEvent := hEvents (j-start) hk
  rw [hPos,he] at hEvent
  exact hOther (j-start) hk (hPos.symm ▸ hJ) (hPos.symm ▸ hCut) round address values shape
    (Option.some.inj hEvent).symm

/-- A later store of the same probability cell belongs to a later score visit
when the earlier store and its publication have the observed visit suffix. -/
theorem ProbabilityStoreVisitSuffix.laterCellScoreCount {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g store cut rival : Nat} (round : Softmax.Round)
    (quarter : Fin 4) (word : Fin 16) {stage : Fin 2} (hBank : warpIndex l g/4 = stage.val)
    (hSuffix : ProbabilityStoreVisitSuffix X g quarter store cut) {e : Event}
    (hEnd : X.get (g,cut) = some e) (hSite : e.pc = probabilityPublicationEnd round quarter)
    (hBefore : store < cut) (hAfter : store < rival)
    (hRival : TcMma.StoreCell l X (g,rival) ⟨g/l.block,laneBase l g+laneOf l g,
      probabilityColumn stage+16*quarter.val+word.val⟩) :
    let object := scoreReadyObject l (g/l.block) stage
    okPolls object ((X.tr g).take store) < okPolls object ((X.tr g).take rival) := by
  obtain ⟨later,address,values,shape,hLater⟩ :=
    rivalProbabilityStoreOfQuarter hp hX quarter word hBank hRival
  have hNot : ¬ rival < cut := fun h =>
    hSuffix later rival address values shape hAfter h hLater
  have hStrict : cut < rival := by
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hNot) with h | h
    · subst rival
      have hs := congrArg Event.pc (Option.some.inj (hEnd.symm.trans hLater))
      have hDiff : probabilityPublicationEnd round quarter ≠ probabilityPc later quarter := by
        cases round <;> cases later <;> fin_cases quarter <;> decide
      exact (hDiff (hSite.symm.trans hs)).elim
    · exact h
  have hRank := (countP_take_mono Softmax.scoreAcquireMark (X.tr g) (Nat.le_of_lt hBefore)).trans_lt
    (probabilityStoreAfterPublicationHasNewWait hX later round quarter hEnd hSite hLater hStrict)
  have hW : warpIndex l g < 8 := by have := stage.isLt; omega
  have hMark : Softmax.scoreAcquireMark = Softmax.phaseAcquired true := by
    funext e
    rw [Softmax.scoreReadyMarkKind]
    rfl
  rw [hMark,scoreCount (j := store) hp hX stage hW rfl hBank,
    scoreCount (j := rival) hp hX stage hW rfl hBank] at hRank
  exact hRank
end

/-- An actual probability word belongs to a closed visit on its producing lane.
Further stores to the same word by that lane belong to later score visits. -/
structure PublishedProbabilityWord (l : Launch) (X : Execution) (store : EvId)
    (cell : TcMma.Cell) (stage : Fin 2) : Prop where
  cellWritten : TcMma.StoreCell l X store cell
  footprint : TensorStoreFootprint l store cell (.probability stage)
  later : ∀ (other : EvId), other.1 = store.1 → store.2 < other.2 →
    TcMma.StoreCell l X other cell →
    okPolls (scoreReadyObject l (store.1/l.block) stage) ((X.tr store.1).take store.2) <
      okPolls (scoreReadyObject l (store.1/l.block) stage) ((X.tr other.1).take other.2)

/-- The actual packed quarters of one producing lane and score visit. -/
def ObservedProbabilityTile (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (visit : Nat) (weights : Nat → ℝ) : Prop :=
  ∀ (quarter : Fin 4) (word : Fin 16), ∃ store : Nat,
    PublishedProbabilityWord l X (g,store)
      (tcDataCell l g .s32x32b (probabilityAddress l g stage quarter) word.val) stage ∧
    okPolls (scoreReadyObject l (g/l.block) stage) ((X.tr g).take store) = visit+1 ∧
    X.TSt (g,store) (probabilityAddress l g stage quarter)
      ((List.range 16).map (probabilityWord (fun i => weights (32*quarter.val+i)))) .s32x32b

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- The recorded closing event makes any word in this observed quarter a
published probability word on its lane. -/
theorem ProbabilityStoreVisitSuffix.publishedWord (hX : Consistent l kernel Assumptions.all m X)
    {g store cut address : Nat} {values : List Value} (round : Softmax.Round) (quarter : Fin 4)
    (word : Fin 16) {stage : Fin 2} (hBank : warpIndex l g/4 = stage.val)
    (hSuffix : ProbabilityStoreVisitSuffix X g quarter store cut)
    (hStore : X.get (g,store) = some
      ⟨probabilityPc round quarter,.tc (.st address values .s32x32b)⟩) {e : Event}
    (hEnd : X.get (g,cut) = some e) (hSite : e.pc = probabilityPublicationEnd round quarter)
    (hBefore : store < cut) :
    PublishedProbabilityWord l X (g,store) ⟨g/l.block,laneBase l g+laneOf l g,
      probabilityColumn stage+16*quarter.val+word.val⟩ stage := by
  refine ⟨probabilityStoreCellFromActual hp hX round quarter word hStore rfl hBank,?_,?_⟩
  · refine ⟨rfl,?_,?_,?_,?_⟩
    · change laneBase l g + laneOf l g = Correction.rowOf l g
      unfold laneBase laneOf Correction.rowOf
      omega
    · simp only [TensorStoreTile.columns]
      omega
    · simp only [TensorStoreTile.columns]
      have hQ := quarter.isLt
      have hW := word.isLt
      omega
    · simp only [TensorStoreTile.warpGroup]
      unfold warpIndex at hBank
      omega
  · rintro ⟨other,j⟩ hLane hAfter hOther
    change other = g at hLane
    subst other
    exact hSuffix.laterCellScoreCount hp hX round quarter word hBank hEnd hSite hBefore hAfter
      hOther

/-- A softmax lane's posted early credit witnesses all the words of the first
three probability quarters on that lane, in any consistent prefix. -/
theorem earlyProbabilityCellBeforeCreditAtVisit (hX : Consistent l kernel Assumptions.all m X)
    {credit : EvId} {cta : Nat} {stage : Fin 2} (hSoft : warpIndex l credit.1 < 8)
    (hCredit : ProbabilityCredit l X credit cta stage 0) (quarter : Fin 3) (word : Fin 16) :
    ∃ store, EarlyProbabilityStore X store ∧ TraceBefore X store credit ∧
      TcMma.StoreCell l X store ⟨cta,laneBase l credit.1+laneOf l credit.1,
        probabilityColumn stage+16*quarter.val+word.val⟩ ∧
      probabilityOrdinal l X cta stage 0 store = probabilityOrdinal l X cta stage 0 credit ∧
      okPolls (scoreReadyObject l cta stage) ((X.tr store.1).take store.2) =
        okPolls (scoreReadyObject l cta stage) ((X.tr credit.1).take credit.2) ∧
      (∀ j, store.2 < j → TcMma.StoreCell l X (credit.1,j)
        ⟨cta,laneBase l credit.1+laneOf l credit.1,
          probabilityColumn stage+16*quarter.val+word.val⟩ →
        probabilityOrdinal l X cta stage 0 credit <
          probabilityOrdinal l X cta stage 0 (credit.1,j)) := by
  obtain ⟨g,j⟩ := credit
  obtain ⟨round,hCreditGet⟩ := earlyPublicationOfCredit hp hX hSoft hCredit
  let q : Fin 4 := ⟨quarter.val,quarter.isLt.trans (by decide)⟩
  have hQ : q ≠ 3 := fun h => by
    have hVal := congrArg Fin.val h
    exact (Nat.ne_of_lt quarter.isLt) hVal
  obtain ⟨k,hK,addr,vals,hStore,hCursor,hRegion⟩ :=
    probabilityStoreBeforePublication hp hX round q hCreditGet (by simp [endSite,hQ])
  obtain ⟨hCta,hRole⟩ := probabilityCreditRole hp hX stage 0 hCredit
  have hBank : warpIndex l g/4 = stage.val := by
    rcases hRole with h | ⟨_,hLo,_⟩
    · exact h.2
    · omega
  refine ⟨(g,k),EarlyProbabilityStore.ofDecoded round q quarter.isLt hStore,
    ⟨rfl,hK,len_of_get hCreditGet⟩,
    probabilityStoreCellFromActual hp hX round q word hStore hCta hBank,
    (hCursor.2 (probabilityObject l cta stage 0)).2,
    (hCursor.2 (scoreReadyObject l cta stage)).1,?_⟩
  intro later hOlder hRival
  have hAfter := probabilityRivalOutsidePublication hp hX round q word hRegion hOlder hBank hRival
  have hStrict : j < later := by
    rcases Nat.eq_or_lt_of_le hAfter with rfl | hStrict
    · obtain ⟨_,_,_,_,⟨_,hBad⟩,_,_⟩ := hRival
      cases congrArg Event.kind (Option.some.inj (hCreditGet.symm.trans hBad))
    · exact hStrict
  let object := probabilityObject l cta stage 0
  have hGet : (X.tr g)[j]? = _ := hCreditGet
  have hMarker : arrivesOn object
      ⟨publicationSite round,.arrive object 0 1 true .cta⟩ = true := by
    simp [arrivesOn,sourceArrive]
  have hCount := countP_take_mono (arrivesOn object) (X.tr g) hStrict
  rw [List.take_add_one,hGet,Option.toList_some,List.countP_append,List.countP_singleton,
    ite_eq_left hMarker] at hCount
  exact hCount

/-- The tail credit witnesses the completed last-quarter store of any lane in
its warp. The actual rendezvous orders the producer's store wait with that credit. -/
theorem tailProbabilityCellDoneThroughCreditAtVisit (hX : Consistent l kernel Assumptions.all m X)
    {credit consumer : EvId} {g cta : Nat} {stage : Fin 2} (hWarp : SameWarp l g credit.1)
    (hCredit : ProbabilityCredit l X credit cta stage 1)
    (hConsumer : baseCausality l X credit consumer) (word : Fin 16) :
    ∃ store,
      TcMma.StoreCell l X store ⟨cta,laneBase l g+laneOf l g,
        probabilityColumn stage+48+word.val⟩ ∧ TcMma.StoreDoneBefore l X store consumer ∧
      store.1 = g ∧
      probabilityOrdinal l X cta stage 1 credit ≤ warpBars X store.1 store.2 ∧
      (∀ j, store.2 < j → TcMma.StoreCell l X (g,j)
        ⟨cta,laneBase l g+laneOf l g,probabilityColumn stage+48+word.val⟩ →
        probabilityOrdinal l X cta stage 1 credit < warpBars X g j) := by
  obtain ⟨h,j⟩ := credit
  obtain ⟨bar,_,hBar,hSender,hOrdinal⟩ := tailCreditOrdinalLeBarrier hp hX stage hCredit
  obtain ⟨peer,hPartner⟩ :=
    WarpBar.partner hX (sameWarp_symm hWarp) hSender (allLanesInTailMask l g)
  have hWarpCount : warpBars X h bar = warpBars X g peer :=
    WarpBar.ordinal_eq hX (sameWarp_symm hWarp)
      (fun _ _ _ he => actualFullWarpBarrier hX he ▸ allLanesInTailMask l g)
      (fun _ _ _ he => actualFullWarpBarrier hX he ▸ allLanesInTailMask l h) hPartner
  have hPeer := hPartner
  obtain ⟨_,_,_,source,hGet⟩ := hPeer
  have hSite := warpBarrierSite hX hGet
  have hRound : ∃ r : Softmax.Round, source = Softmax.probabilityWaitPc r true+1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
    rcases hSite with rfl | rfl | rfl
    · exact ⟨.first,rfl⟩
    · exact ⟨.biased,rfl⟩
    · exact ⟨.unbiased,rfl⟩
  obtain ⟨ownRound,rfl⟩ := hRound
  obtain ⟨k,hK,addr,vals,hStore,hCursor,hRegion⟩ :=
    probabilityStoreBeforePublication hp hX ownRound 3 hGet (by simp [endSite])
  have hStoreBefore := probabilityTailWaitBeforeWarpBarrier hp hX ownRound ownRound hStore hGet hK
  obtain ⟨wait,hWait,hBeforeWait,hWaitBeforeBar⟩ := hStoreBefore
  have hCr := hCredit
  obtain ⟨_,hCreditGet⟩ := hCr
  have hCausal := WarpBar.sync hWarp hPartner.symm hWaitBeforeBar
    (by omega : bar < j) (len_of_get hCreditGet)
  obtain ⟨hOwner,hRole⟩ := probabilityCreditRole hp hX stage 1 hCredit
  have hBank : warpIndex l g/4 = stage.val := by
    rw [show warpIndex l g = warpIndex l h from hWarp.2]
    rcases hRole with h | ⟨hFalse,_,_⟩
    · exact h.2
    · cases hFalse
  have hCell := probabilityStoreCellFromActual hp hX ownRound 3 word hStore
    (hWarp.1.2.2.trans hOwner) hBank
  have hDone : TcMma.StoreDoneBefore l X (g,k) consumer :=
    ⟨⟨addr,vals,.s32x32b,_,hStore⟩,
      .inl ⟨(g,wait),hWait,rfl,hBeforeWait,.inl (hCausal.trans hConsumer)⟩⟩
  refine ⟨(g,k),hCell,hDone,rfl,(hWarpCount.trans hCursor.1.symm) ▸ hOrdinal,?_⟩
  intro later hOlder hRival
  have hAsQuarter : (3 : Fin 4).val = 3 := rfl
  have hLatest := probabilityRivalOutsidePublication hp hX ownRound 3 word hRegion hOlder hBank
    (by simpa only [hAsQuarter] using hRival)
  have ⟨mask,inst,_,hOwn⟩ := hPartner
  have hStrict : peer < later := by
    rcases Nat.eq_or_lt_of_le hLatest with rfl | hStrict
    · obtain ⟨_,_,_,_,⟨_,hBad⟩,_,_⟩ := hRival
      obtain ⟨_,hOwn⟩ := hOwn
      cases congrArg Event.kind (Option.some.inj (hOwn.symm.trans hBad))
    · exact hStrict
  have hCount := countP_take_mono Execution.isWarpBar (X.tr g) hStrict
  change warpBars X g (peer+1) ≤ warpBars X g later at hCount
  rw [WarpBar.warpBars_succ hOwn,← hWarpCount] at hCount
  change probabilityOrdinal l X cta stage 1 (h,j) ≤ warpBars X h bar at hOrdinal
  omega

end

/-- An MMA issue is not an ordinary thread memory access. -/
theorem mmaIsNotOrdinaryAccess {X : Execution} {i : EvId} {dst : Nat}
    {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i dst op acc mask) : (X.get i).bind Event.acc = none := by
  obtain ⟨_,he⟩ := hi
  rw [he]
  rfl

end PTX.Kernels.TmlFa4Fwd.Thread.Scores

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopLocal
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Kernels.TmlFa4Fwd.Proof.MmaElect
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

private def electedAt (r : Round) : Nat := probabilityWaitPc r true + 2
private def creditAt (r : Round) : Nat := (signalSite (tailPublication r)).pc

private def interior (r : Round) (pc : Nat) : Prop := electedAt r < pc ∧ pc ≤ creditAt r

private instance (r : Round) (pc : Nat) : Decidable (interior r pc) :=
  inferInstanceAs (Decidable (electedAt r < pc ∧ pc ≤ creditAt r))

private def opensAt (r : Round) : Op :=
  .warp ⟨.elect, none, [some (tailElectLane r), some (tailElectPred r)], [], some (.imm (-1))⟩

private theorem openedByElection (r : Round) :
    kernel.code[electedAt r]? = some ⟨none, opensAt r⟩ := by
  cases r
  · exact Flow.code_4859
  · exact Flow.code_6544
  · exact Flow.code_7449

private def branchSafe (r : Round) (i : Instr) : Bool :=
  match i.op with
  | .bra dst _ => !decide (interior r dst)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem branchAvoidsInterior (r : Round) : kernel.code.all (branchSafe r) = true := by
  cases r <;> kernel_rfl

private theorem segmentAvoidsInterior (r : Round) {site : Nat} {m : SegMatch CuteSlot}
    (hs : site ∈ Assumptions.swExp2Sites)
    (hm : cuteExp2.matchAt kernel site = some m) : ¬ interior r m.stop := by
  have hAudit : Assumptions.swExp2Sites.all (fun start =>
      match cuteExp2.matchAt kernel start with
      | some u => !decide (interior r u.stop)
      | none => false) = true := by
    cases r <;> set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAudit site hs
  simpa [hm] using h

private def negatesElection (r : Round) : Op :=
  .int ⟨.not, .pred, false, [some (tailElectPred r + 1)], [.reg (tailElectPred r)]⟩

private theorem negateCode (r : Round) :
    kernel.code[electedAt r + 1]? = some ⟨none, negatesElection r⟩ := by
  cases r
  · exact Flow.code_4860
  · exact Flow.code_6545
  · exact Flow.code_7450

private theorem bypassCode (r : Round) :
    kernel.code[electedAt r + 2]? =
      some ⟨some (tailElectPred r+1,false), .bra (creditAt r + 1) false⟩ := by
  cases r
  · exact Flow.code_4861
  · exact Flow.code_6546
  · exact Flow.code_7451

private theorem nonleaderBypass {l : Launch} {g : Nat} {s : TState} (r : Round)
    (hp : s.pc = electedAt r + 1) (hf : s.fault = none)
    (hr : s.regs (tailElectPred r) = some (.pred false)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧ u.pc = creditAt r + 1 := by
  let t := next (setReg s (tailElectPred r+1) (.pred true))
  have hc : kernel.code[s.pc]? = some ⟨none, negatesElection r⟩ := hp.symm ▸ negateCode r
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hp]; cases r <;> decide
  have ht : Tau kernel Assumptions.all l g s t := by
    apply tauStep_iff.mp
    rw [Assumptions.tauStep_all_eq_nil (L := l) (g := g) hOff hc rfl]
    have hExec : execLocalA [] l g s (negatesElection r) = .ok t := by
      unfold negatesElection
      rw [execLocalA_nil, execLocal_int rfl]
      simp [execInt, DType.width, readPred, hr, readReg, t, bind, Except.bind, pure, Except.pure]
    simp only [tauStep, out, hf, hc, guardHolds, pure, Except.pure,
      show (negatesElection r).isLocal = true from rfl, ↓reduceIte, hExec]
  have hPc : t.pc = electedAt r + 2 := by simp [t, next, setReg, hp, Nat.add_assoc]
  have hF : t.fault = none := by simpa [t, next, setReg] using hf
  have hReg : t.regs (tailElectPred r+1) = some (.pred true) := by simp [t, next, setReg]
  have hCode := hPc.symm ▸ bypassCode r
  have hOff' : t.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; cases r <;> decide
  let u := {t with pc := creditAt r + 1}
  have hb : Tau kernel Assumptions.all l g t u := by
    apply tauStep_iff.mp
    rw [Assumptions.tauStep_all_eq_nil (L := l) (g := g) hOff' hCode rfl]
    simp [tauStep, out, hF, hCode, guardHolds, readReg, hReg, bind, Except.bind, pure,
      Except.pure, execLocalA_nil, execLocal, execBranch, Op.isLocal, Op.rule, u]
  exact ⟨u, (Relation.ReflTransGen.single ht).tail hb, rfl⟩

private theorem tailBeforeCreditLocal (r : Round) {pc : Nat} {ins : Instr}
    (hPc : interior r pc) (hEnd : pc ≠ creditAt r)
    (hCode : kernel.code[pc]? = some ins) : ins.op.isLocal = true := by
  have audit : ((kernel.code.drop (electedAt r+1)).take (creditAt r-(electedAt r+1))).all
      (fun i => i.op.isLocal) = true := by cases r <;> kernel_rfl
  apply List.all_eq_true.mp audit ins
  apply List.mem_of_getElem? (i := pc-(electedAt r+1))
  unfold interior at hPc
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le (by omega)]

private theorem tailCreditAdvances {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (r : Round) (hPc : s.pc = creditAt r)
    (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc+1 := by
  have code : ∃ (base count word : Nat) (offset : Int), kernel.code[creditAt r]? =
      some ⟨none,.mbarArrive base offset (.imm 0) (.reg count) false true .cta (some word)⟩ := by
    cases r
    · exact ⟨_,_,_,_,Flow.code_4867⟩
    · exact ⟨_,_,_,_,Flow.code_6552⟩
    · exact ⟨_,_,_,_,Flow.code_7457⟩
  obtain ⟨base,count,word,offset,hExpected⟩ := code
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hPc,hExpected] at hCode
  obtain rfl := Option.some.inj hCode
  have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
  have hZero : readBits l g s 32 (.imm 0) = .ok 0#64 := rfl
  simp only [eventTmpl,hWide,widenMbarScope,tmaTmpl,hZero,bind,Except.bind,pure,Except.pure]
    at hFire
  cases hm : mbarLoc l g s base offset with
  | error f => simp [hm,ofExec,Fires] at hFire
  | ok loc =>
    cases hCount : readBits l g s 32 (.reg count) with
    | error f => simp [hm,hCount,ofExec,Fires] at hFire
    | ok n =>
      simp only [hm,hCount,ofExec,Fires] at hFire
      obtain ⟨_,hu⟩ := hFire
      obtain rfl := Option.some.inj hu
      rfl

private def Gate (l : Launch) (g : Nat) (r : Round) (s : TState) (prior : List Event) : Prop :=
  interior r s.pc →
    (∃ pre inst, prior = pre ++ [⟨electedAt r, .elect (2^32-1) inst (laneOf l g)⟩]) ∨
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧ u.pc = creditAt r + 1

private theorem gateTau {l : Launch} {g : Nat} {s u : TState} {xs : List Event}
    (r : Round) (hGate : Gate l g r s xs) (ht : Tau kernel Assumptions.all l g s u) :
    Gate l g r u xs := by
  intro hu
  obtain ⟨i, hc, _, hExec⟩ := tauScoreSource ht
  have hStep : u.pc = s.pc + 1 := by
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, he⟩
    · rfl
    rcases scoreExecLocal he with hFrame | ⟨seg, hs, hm, hRun⟩
    · have h := List.all_eq_true.mp (branchAvoidsInterior r) i (List.mem_of_getElem? hc)
      have hPc := hFrame.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni =>
        rw [hPc] at hu
        simp [branchSafe, ho, hu] at h
      case brx => simp [branchSafe, ho] at h
      all_goals exact hPc
    · exact (segmentAvoidsInterior r hs hm ((scoreSegmentFrame hRun).1 ▸ hu)).elim
  have hNe : s.pc ≠ electedAt r := by
    intro hP
    rw [hP, openedByElection] at hc
    cases hc
    rcases hExec with ⟨rfl, hn⟩ | ⟨_, hN, _⟩
    · cases hn
    · cases hN
  obtain hFound | ⟨exit, hPath, hExit⟩ := hGate
    ⟨by have := hu.1; omega, by have := hu.2; omega⟩
  · exact .inl hFound
  · rcases Relation.ReflTransGen.cases_head hPath with rfl | ⟨v, hTau, hRest⟩
    · have := hu.2
      omega
    · obtain rfl := tau_det ht hTau
      exact .inr ⟨exit, hRest, hExit⟩

private theorem gateEvent {l : Launch} {g : Nat} {s u : TState} {e : Event} {xs : List Event}
    (r : Round) (_hGate : Gate l g r s xs) (he : EStep kernel Assumptions.all l g s e (some u)) :
    Gate l g r u (xs ++ [e]) := by
  intro hu
  obtain ⟨i, hc, hl, hFire⟩ := estep_event_source he
  by_cases hs : interior r s.pc
  · by_cases hAt : s.pc = creditAt r
    · have hNext := tailCreditAdvances r hAt he
      have hWithin := hu.2
      omega
    · exact (Bool.false_ne_true (hl.symm.trans (tailBeforeCreditLocal r hs hAt hc))).elim
  have hAudited : kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true :=
    by decide +kernel
  have hCheck := List.all_eq_true.mp hAudited i (List.mem_of_getElem? hc)
  have hFrame : ReturnedFrame s.pc (eventTmpl Assumptions.all l g s i.op) :=
    Epilogue.ordinaryEventFrame (by simpa only [hl, Bool.false_or] using hCheck)
  have hPc : s.pc = electedAt r := by
    rcases callbackFrame_fires hFrame hFire with hSame | hNext
    · exact (hs (hSame ▸ hu)).elim
    · unfold interior at hu hs
      omega
  rw [hPc, openedByElection] at hc
  obtain rfl := Option.some.inj hc.symm
  change Fires s.pc (eventTmpl Assumptions.all l g s (opensAt r)) e (some u) at hFire
  unfold opensAt at hFire
  have hAll := fires_elect_mask (bits := BitVec.ofNat 64 (2^32-1)) rfl hFire
  obtain ⟨_, inst, leader, hE, hU⟩ := fires_elect hFire
  have hFull : e = ⟨electedAt r, .elect (2^32-1) inst leader⟩ := by
    rcases hAll with ⟨i', lead', hf⟩ | ⟨f, hf⟩
    · obtain ⟨_, rfl, rfl⟩ := Kind.elect.inj (congrArg Event.kind (hE.symm.trans hf))
      rwa [hPc] at hf
    · cases congrArg Event.kind (hE.symm.trans hf)
  by_cases hLane : laneOf l g = leader
  · exact .inl ⟨xs,inst,congrArg (fun k => xs ++ [k]) (hLane ▸ hFull)⟩
  · have hHealthy : s.fault = none := by
      obtain ⟨tm, hOut, hF⟩ := he
      cases h : s.fault with
      | none => rfl
      | some err =>
        simp only [out, h, Out.ev.injEq] at hOut
        subst tm
        cases hF.2
    refine .inr (nonleaderBypass r ?_ ?_ ?_)
    · rw [hU]
      exact congrArg (· + 1) hPc
    · simpa [hU, next, setReg] using hHealthy
    · have hNo : (laneOf l g == leader) = false := beq_eq_false_iff_ne.mpr hLane
      simp [hU, next, setReg, hNo]

private theorem gateReach {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (r : Round) (hr : TraceReach kernel Assumptions.all l g s es u) {xs : List Event}
    (hGate : Gate l g r s xs) : Gate l g r u (xs ++ es) := by
  induction hr generalizing xs with
  | refl => simpa only [List.append_nil] using hGate
  | tau ht _ ih => exact ih (gateTau r hGate ht)
  | @event s t u es e ht _ ih =>
    simpa only [List.append_assoc, List.singleton_append] using ih (gateEvent r hGate ht)

/-- Neither tail loop nor the first tail can issue a probability credit without its full-warp
election selecting the current lane. -/
theorem tailCreditImmediateElection {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (r : Round) {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hSite : e.pc = (signalSite (tailPublication r)).pc) :
    0 < j ∧ ∃ inst,
      X.Elect (g,j-1) (probabilityWaitPc r true+2) (2^32-1) inst (laneOf l g) := by
  obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s, _, hReach, hStep⟩ := hRun.before_event he
  have hGate := gateReach r hReach (xs := []) (fun hu => by
    have hNeg : ¬ interior r ({} : TState).pc := by cases r <;> decide
    exact (hNeg hu).elim)
  have hS : s.pc = creditAt r := (estep_source_pc hStep).symm.trans hSite
  have hHere : interior r s.pc := by rw [hS]; cases r <;> decide
  rcases hGate hHere with ⟨prior,inst,hSplit⟩ | ⟨u, hPath, hEnd⟩
  · simp only [List.nil_append] at hSplit
    have hLen := congrArg List.length hSplit
    simp only [List.length_take,List.length_append,List.length_singleton,
      Nat.min_eq_left (len_of_get he).le] at hLen
    refine ⟨by omega,inst,?_⟩
    change (X.tr g)[j-1]? = _
    have hk : j-1 < j := by omega
    rw [← List.getElem?_take_of_lt hk,hSplit,
      show j-1 = prior.length by omega,List.getElem?_append_right le_rfl,Nat.sub_self]
    rfl
  · rcases Relation.ReflTransGen.cases_head hPath with rfl | ⟨t,ht,_⟩
    · omega
    · exact (not_tau_of_stops (stops_of_estep hStep) ht).elim

end PTX.Kernels.TmlFa4Fwd.Softmax

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.AsyncCopy Prologue Softmax

/-- An elected tail credit records its round's election before the release. -/
theorem tailCreditImmediateElectionBefore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {e : EvId}
    {cta : Nat} (stage : Fin 2) (hCredit : ProbabilityCredit l X e cta stage 1) :
    ∃ round : Round, 0 < e.2 ∧ ∃ inst,
      X.Elect (e.1,e.2-1) (probabilityWaitPc round true+2) (2^32-1) inst (laneOf l e.1) := by
  obtain ⟨g,j⟩ := e
  obtain ⟨_, hRole⟩ := probabilityCreditRole hp hX stage 1 hCredit
  have hStage : warpIndex l g / 4 = stage.val := by
    rcases hRole with h | h
    · exact h.2
    · have hFalse : (1 : Fin 2).val = 0 := h.1
      cases hFalse
  obtain ⟨source, he⟩ := hCredit
  have hOff : 112 + 8 * stage.val ∈ [96, 104, 112, 120] := by fin_cases stage <;> decide
  have he' : X.get (g,j) =
      some ⟨source,
        .arrive ⟨.shared, cta, l.sharedBase + (112 + 8 * stage.val)⟩ 0 1 true .cta⟩ := by
    simpa [probabilityObject, Nat.add_left_comm, Nat.add_assoc, Nat.add_comm] using he
  rcases actualProbabilityArrivalSite hp hX he' hOff rfl with ⟨site, rfl⟩ | hCorr
  · have hLoc := (probabilityArriveFacts hp hX site he').2.2.2.2.2
    have hAddr : l.sharedBase + (112 + 8 * stage.val) =
        l.sharedBase + ((probabilityArrivalSite site).offset + 8 * (warpIndex l g / 4)) :=
      congrArg Loc.addr hLoc
    have hPacket : (probabilityArrivalSite site).offset = 112 := by omega
    have hClass : ∀ site : Fin 6, (probabilityArrivalSite site).offset = 112 →
        ∃ round : Softmax.Round, (probabilityArrivalSite site).pc =
          (signalSite (tailPublication round)).pc := by
      intro i hi
      fin_cases i
      all_goals first
        | exact ⟨.first, rfl⟩
        | exact ⟨.biased, rfl⟩
        | exact ⟨.unbiased, rfl⟩
        | cases hi
    obtain ⟨round, hSite⟩ := hClass site hPacket
    obtain ⟨hk,inst,hx⟩ := tailCreditImmediateElection hX round (j := j) he' hSite
    exact ⟨round,hk,inst,hx⟩
  · have hLoc := Correction.correctionArriveAddressExact hp hX he' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCorr ⊢
      tauto)
    have hAddress : l.sharedBase + (112 + 8 * stage.val) =
      l.sharedBase + Correction.correctionArriveOffset source := congrArg Loc.addr hLoc
    have hCandidates : ∀ source ∈ [7752, 7754, 8223, 8442, 8759, 9055],
        Correction.correctionArriveOffset source = 96 ∨
          Correction.correctionArriveOffset source = 104 := by decide
    have h := hCandidates source hCorr
    omega

/-- A tail credit has its same-round election earlier in the issuing trace. -/
theorem tailCreditElectionBefore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {e : EvId}
    {cta : Nat} (stage : Fin 2) (hCredit : ProbabilityCredit l X e cta stage 1) :
    ∃ round : Round, ∃ k < e.2, ∃ inst,
      X.Elect (e.1,k) (probabilityWaitPc round true+2) (2^32-1) inst (laneOf l e.1) := by
  obtain ⟨round,hPos,inst,hElect⟩ := tailCreditImmediateElectionBefore hp hX stage hCredit
  exact ⟨round,e.2-1,by omega,inst,hElect⟩

/-- Tail probability credits of one warp are issued by a stable elected lane, across rounds. -/
theorem tailProbabilityCreditSameIssuer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e f : EvId} {cta : Nat} {stage : Fin 2} (hw : SameWarp l e.1 f.1)
    (he : ProbabilityCredit l X e cta stage 1) (hf : ProbabilityCredit l X f cta stage 1) :
    e.1 = f.1 := by
  obtain ⟨_,_,_,_,hx⟩ := tailCreditElectionBefore hp hX stage he
  obtain ⟨_,_,_,_,hy⟩ := tailCreditElectionBefore hp hX stage hf
  exact sameWarp_eq_of_lane_eq hw (Mma.sameLeader hX hw hx hy)

end PTX.Kernels.TmlFa4Fwd.Thread.Scores

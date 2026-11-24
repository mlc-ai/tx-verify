-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorAbi
public import Kernels.TmlFa4Fwd.Proof.MmaQkBroadcast
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
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
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.Final
import Lemmas.Flow.Retry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Epilogue

private def openingBoundary : Fin 3 → Nat
  | 0 => 1935
  | 1 => 2148
  | 2 => 2109

private theorem openingBoundaryAudit : ∀ k : Fin 3,
    let floor := openingBoundary k
    (kernel.code.drop floor).all (fun i => Thread.staysPastEvent floor i.op) = true ∧
      Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
        | some seg => decide (floor ≤ seg.stop)
        | none => false) = true := by decide +kernel

private theorem openingFloor {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (k : Fin 3) (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : openingBoundary k ≤ s.pc) : openingBoundary k ≤ u.pc := by
  have hAudit := openingBoundaryAudit k
  induction h with
  | refl => exact hs
  | tau ht _ ih =>
    exact ih (Thread.eventTailStepOfAudit hAudit.1 hAudit.2 hs (.inl ⟨rfl,ht⟩))
  | event he _ ih =>
    exact ih (Thread.eventTailStepOfAudit hAudit.1 hAudit.2 hs (.inr ⟨_,rfl,he⟩))

private def openingBankRegs := [1178,9632,2535] ++ (List.range 8).map (9624+·)

private theorem openingBankFrame {l : Launch} {g r : Nat} {s u : TState} {es : List Event}
    (h : TraceReach kernel Assumptions.all l g s es u)
    (hs : 1935 ≤ s.pc) (hu : u.pc < 2148) (hr : r ∈ openingBankRegs) :
    u.regs r = s.regs r := by
  have hKeep {a b : TState} {e : Option Event} (hLo : 1935 ≤ a.pc) (hHi : a.pc < 2148)
      (he : WStep kernel Assumptions.all l g a e b) : b.regs r = a.regs r := by
    apply mmaStepReg (by omega) (by omega) _ he
    intro ins hc
    have hAll : ((kernel.code.drop 1935).take (2148-1935)).all
        (fun i => openingBankRegs.all fun r => !(mmaWrites i.op).contains r) = true := by
      decide +kernel
    have hGet : ((kernel.code.drop 1935).take (2148-1935))[a.pc-1935]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hc]
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hAll ins (List.mem_of_getElem? hGet)) r hr
  have hLo {a b : TState} {e : Option Event} (hp : 1935 ≤ a.pc)
      (hStep : WStep kernel Assumptions.all l g a e b) : 1935 ≤ b.pc :=
    Thread.eventTailStepOfAudit (openingBoundaryAudit 0).1 (openingBoundaryAudit 0).2 hp hStep
  induction h with
  | refl => rfl
  | @tau a b u es he ht ih =>
    have hHi : a.pc < 2148 := by
      by_contra! hBad
      exact Nat.not_le_of_lt hu (openingFloor 1 (.tau he ht) hBad)
    exact (ih (hLo hs (.inl ⟨rfl,he⟩)) hu).trans (hKeep hs hHi (.inl ⟨rfl,he⟩))
  | @event a b u es e he ht ih =>
    have hHi : a.pc < 2148 := by
      by_contra! hBad
      exact Nat.not_le_of_lt hu (openingFloor 1 (.event he ht) hBad)
    exact (ih (hLo hs (.inr ⟨_,rfl,he⟩)) hu).trans (hKeep hs hHi (.inr ⟨_,rfl,he⟩))

private theorem Run.openingLastSource {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} {e : Event}
    (hr : Run kernel Assumptions.all l g s (es++[e]) (some u)) :
    ∃ t, TraceReach kernel Assumptions.all l g s es t ∧
      EStep kernel Assumptions.all l g t e (some u) := by
  induction es generalizing s with
  | nil =>
    cases hr with
    | step hLocal hEvent hRest =>
      cases hRest
      exact ⟨_,TraceReach.of_local hLocal,hEvent⟩
  | cons head tail ih =>
    change Run kernel Assumptions.all l g s (head :: (tail++[e])) (some u) at hr
    generalize hRem : tail++[e] = rem at hr
    cases hr with
    | step hLocal hEvent hRest =>
      obtain ⟨t,hReach,he⟩ := ih (hRem.symm ▸ hRest)
      exact ⟨t,(TraceReach.of_local hLocal).append (.event hEvent hReach),he⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The ordinal-zero K acquire is the initial slot-zero instruction in the issuing lane. -/
theorem openingKeyDecoded (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hPoll : Thread.Mma.ReadyPoll l X g index 0 0 true .cta)
    (hRank : (Thread.Mma.atPrefix l X g index).kvAcquires 0 = 0) :
    X.get (g,index) = some ⟨2145,.wait ⟨.shared,g/l.block,l.sharedBase+32⟩ 0 true true .cta⟩ := by
  have hUse := hPoll.exactOccurrence hp hX hw
  dsimp only at hUse
  have hCount := Thread.Mma.readyUsesAtPrefix hp hX hg hw index
  have hZero : (((X.tr g).take index).filterMap readyEvent).length = 0 := by omega
  obtain ⟨pc,he,hSite⟩ := hPoll.useSite hp hX hw
  rw [hZero] at hSite
  have hPc : pc = 2145 := by
    rcases hSite with ⟨rfl,_⟩ | ⟨_,hl,_⟩ | ⟨_,h⟩
    · rfl
    · cases hl
    · cases h
  exact hPc ▸ he

/-- A recorded opening key acquire returns to the exact broadcast cursor. The launch
descriptor setup and the address and parity frames all use the same recorded lane prefix. -/
theorem openedKeyLaneCursor (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g index : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hPoll : Thread.Mma.ReadyPoll l X g index 0 0 true .cta)
    (hRank : (Thread.Mma.atPrefix l X g index).kvAcquires 0 = 0) :
    ∃ after ready ending,
      Run kernel Assumptions.all l g {} ((X.tr g).take (index+1)) (some after) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (index+1)) ending ∧
      after.pc = 2146 ∧ Tau kernel Assumptions.all l g after ready ∧
      At ready 2148 (firstQKBroadcastFacts l) := by
  let ev : Event := ⟨2145,.wait ⟨.shared,g/l.block,l.sharedBase+32⟩ 0 true true .cta⟩
  have hGet : X.get (g,index) = some ev := openingKeyDecoded hp hMax.1 hg hw hPoll hRank
  obtain ⟨initial,ending,flag,hInitial,_,hAt,hPast,_⟩ :=
    schedulerAbiAtDescriptorWithOrdinal hp hMax hg hw
  let n := descriptorShufflePos (laneOf l g)+1
  have hFirst : n ≤ index := by
    have hOrder := Thread.traceOrderOfPcFloor hMax.1 (floor := 1917) (by decide +kernel)
      (by decide +kernel) hInitial hGet (show 1916 < 1917 by decide) (show 1917 ≤ 2145 by decide)
    exact hOrder
  obtain ⟨last,hRun⟩ := hMax.1.thr g hg
  let taken := (X.tr g).take (index+1)
  have hSplit := List.take_append_drop (index+1) (X.tr g)
  obtain ⟨o,hPrefix⟩ := (hSplit.symm ▸ hRun : Run kernel Assumptions.all l g {}
    (taken++(X.tr g).drop (index+1)) last).prefix
  change Run kernel Assumptions.all l g {} taken o at hPrefix
  have hGetList : (X.tr g)[index]? = some ev := hGet
  have hPrefixEq : taken = (X.tr g).take index ++ [ev] := by
    dsimp only [taken]
    rw [List.take_add_one,hGetList]
    rfl
  obtain ⟨after,rfl⟩ : ∃ t, o = some t := by
    cases o with
    | some t => exact ⟨t,rfl⟩
    | none =>
      have hLast := run_last_not_wait (hPrefixEq ▸ hPrefix) 2145
        (⟨.shared,g/l.block,l.sharedBase+32⟩ : Loc) 0 true true .cta
      exact (hLast (by simp [ev])).elim
  have hTail := hPrefix.after_returned_prefix (hSplit.symm ▸ hRun)
  have hInitSplit := List.take_append_drop n taken
  rw [List.take_take,Nat.min_eq_left (show n ≤ index+1 by omega)] at hInitSplit
  have hBetween := hPast.after_returned_prefix (hInitSplit.symm ▸ hPrefix)
  have hBetweenEq : taken.drop n = ((X.tr g).take index).drop n ++ [ev] := by
    rw [hPrefixEq,List.drop_append_of_le_length]
    simp only [List.length_take]
    have hI : index < (X.tr g).length := len_of_get hGet
    exact le_min hFirst (hFirst.trans hI.le)
  have hNonempty : taken.drop n ≠ [] := by rw [hBetweenEq]; simp
  obtain ⟨bank,hCore,hBank⟩ := startupQRegistersCore hp g initial
    (hAt.mono ⟨hAt.2.2.2.2.1,trivial⟩)
  have hTau := localRun (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) hCore
  have hBankRun := hBetween.after_local_nonempty (run_rtg hTau) hNonempty
  obtain ⟨source,hReach,hEvent⟩ := Run.openingLastSource (hBetweenEq ▸ hBankRun)
  obtain ⟨ins,hDecoded,_,hFire⟩ := estep_event_source hEvent
  have hSite : source.pc = 2145 := (estep_source_pc hEvent).symm
  rw [hSite,Flow.code_2145] at hDecoded
  obtain rfl := Option.some.inj hDecoded.symm
  obtain ⟨target,parity,ok,scope,hShape,hAfter⟩ := fires_wait hFire
  have hOk : ok = true := (Kind.wait.inj (congrArg Event.kind hShape)).2.2.1.symm
  subst ok
  have hPc : after.pc = 2146 := by rw [hAfter]; change source.pc+1 = 2146; omega
  have hSuccess : after.regs 9635 = some (.pred true) := by rw [hAfter]; simp [next,setReg]
  have hClean : after.fault = none := by
    rw [hAfter]
    change source.fault = none
    cases h : source.fault with
    | none => rfl
    | some fault =>
      obtain ⟨tmpl,hOut,hFired⟩ := hEvent
      rw [show out kernel Assumptions.all l g source = .ev (.ub fault) by simp [out,h]] at hOut
      obtain rfl := Out.ev.inj hOut.symm
      cases hFired.2
  have hTrace := hReach.append (.event hEvent (.refl _))
  have hUpper {a : TState} {events : List Event}
      (h : TraceReach kernel Assumptions.all l g a events after) : a.pc < 2768 := by
    by_contra! hBad
    have hBound : openingBoundary 1 ≤ a.pc := by change 2148 ≤ a.pc; omega
    have h := openingFloor 1 h hBound
    change 2148 ≤ after.pc at h
    omega
  let roots := [1062,2535,6495,1178]
  have hStable {r : Nat} (hr : r ∈ roots) : bank.regs r = initial.regs r :=
    schedulerLocalFrame (lo := 1917) (len := 18) (by
      set_option maxRecDepth 100000 in kernel_rfl) (by
      set_option maxRecDepth 100000 in kernel_rfl) hCore hAt.1.ge (by rw [hAt.1]) hr
  have hLoc := holds_mem hAt.2.2.2.2 (show (2535,b32 l.sharedBase) ∈ _ by
    simp [entryFacts,startupFacts])
  have hMma := holds_mem hAt.2.2.2.2 (show (1062,b32 12) ∈ _ by
    simp [entryFacts,startupFacts])
  have hBar := holds_mem hAt.2.2.2.2
    (show (6495,b32 (l.sharedBase+144)) ∈ _ by simp [entryFacts,startupFacts])
  have hCache := holds_mem hAt.2.2.2.2
    (show (1178,b32 (l.sharedBase+68608)) ∈ _ by simp [entryFacts,startupFacts])
  have hs := (hStable (by decide : 2535 ∈ roots)).trans hLoc
  have hm := (hStable (by decide : 1062 ∈ roots)).trans hMma
  obtain ⟨hSub,hAcc,hScore,hQuery⟩ := openingBarriersOfTrace hp
    (hBank.mono ⟨hm,hs,(hStable (by decide : 6495 ∈ roots)).trans hBar,trivial⟩)
    hTrace hPc hUpper
  have hParity := openingParityOfTrace hp (hBank.mono ⟨hm,hs,trivial⟩) hTrace hPc hUpper
  have hKeep {r} (hr : r ∈ openingBankRegs) : after.regs r = bank.regs r :=
    openingBankFrame hTrace hBank.1.ge (by rw [hPc]; decide) hr
  have hWords : Holds after.regs (qDescriptorFacts l 1) := by
    apply holdsSchedulerFrame hBank.2.2.2.2.2.2.2 (regs := openingBankRegs)
      (fun r hr => hKeep hr)
    intro pair hm
    unfold qDescriptorFacts at hm
    obtain ⟨step,_,rfl⟩ := List.mem_map.mp hm
    exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr step.isLt))
  have hReady : At after 2146 ((9635,.pred true) :: firstQKBroadcastFacts l) :=
    ⟨hPc,hSub,hAcc,hClean,hSuccess,
      (hKeep (by decide : 1178 ∈ openingBankRegs)).trans
        ((hStable (by decide : 1178 ∈ roots)).trans hCache),
      (hKeep (by decide : 9632 ∈ openingBankRegs)).trans hBank.2.2.2.2.2.1,
      hParity,hScore,hQuery,(hKeep (by decide : 2535 ∈ openingBankRegs)).trans hs,hWords⟩
  obtain ⟨u,hLocal,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2146 true hReady hSuccess (by simp)
  have hOne := localRun (n := 1) (by decide) (by decide) hReady.1 rfl hLocal
  have hReturned : Tau kernel Assumptions.all l g after u := by
    apply tauStep_iff.mp
    cases h : tauStep kernel Assumptions.all l g after with
    | none =>
      simp only [run,h,Option.bind_none] at hOne
      cases hOne
    | some b =>
      simp only [run,h,Option.bind_some,Option.some.injEq] at hOne
      exact congrArg some hOne
  exact ⟨after,u,last,hPrefix,hTail,hPc,hReturned,hU.mono hU.2.2.2.2.2⟩

/-- The selected opening metadata cursor carries the collective ordinals of its actual lane. -/
def OpeningMetadataCounts (l : Launch) (X : Execution) (g shuffles votes : Nat) : Prop :=
  ∃ pos t u,
    u.pc = 2109 ∧ Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
    ((X.tr g).take pos).countP Execution.isShfl = shuffles ∧
    ((X.tr g).take pos).countP isFullWarpVote = votes

private def openingLoadsOrWaits (i : Instr) : Bool :=
  i.op.isLocal || match i.op with
    | .mem a => a.kind == .load && !a.nc && a.ext == .same
    | .mbarWait .. => true
    | _ => false

private theorem openingLoadsOrWaitsAudit :
    ((kernel.code.drop 2109).take (2148-2109)).all openingLoadsOrWaits = true := by
  decide +kernel

private theorem openingNeitherCollective {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 2109 ≤ s.pc) (hHi : s.pc < 2148)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    Execution.isShfl e = false ∧ isFullWarpVote e = false := by
  obtain ⟨ins,hCode,hLocal,hFire⟩ := estep_event_source he
  have hc : ((kernel.code.drop 2109).take (2148-2109))[s.pc-2109]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo,hCode]
  have ha := List.all_eq_true.mp openingLoadsOrWaitsAudit ins (List.mem_of_getElem? hc)
  unfold openingLoadsOrWaits at ha
  rw [hLocal,Bool.false_or] at ha
  generalize hOp : ins.op = op at ha hFire
  clear hOp hCode hc he hLocal ins
  cases op <;> simp only [Bool.false_eq_true] at ha
  case mem a =>
    have hm : a.kind = .load ∧ a.nc = false ∧ a.ext = .same := by
      simpa [and_assoc] using ha
    obtain ⟨_,_,rfl,_⟩ := fires_load hm.1 hm.2.1 hFire hm.2.2
    exact ⟨rfl,rfl⟩
  case mbarWait =>
    obtain ⟨_,_,_,_,rfl,_⟩ := fires_wait hFire
    exact ⟨rfl,rfl⟩

private theorem openingNoCollectives {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u)
    (hs : 2109 ≤ s.pc) (hu : u.pc < 2148) :
    events.countP Execution.isShfl = 0 ∧ events.countP isFullWarpVote = 0 := by
  have hLower {a b : TState} {e : Option Event} (ha : 2109 ≤ a.pc)
      (hStep : WStep kernel Assumptions.all l g a e b) : 2109 ≤ b.pc :=
    Thread.eventTailStepOfAudit (openingBoundaryAudit 2).1 (openingBoundaryAudit 2).2 ha hStep
  induction h with
  | refl => exact ⟨rfl,rfl⟩
  | tau hStep _ ih => exact ih (hLower hs (.inl ⟨rfl,hStep⟩)) hu
  | @event a b z es e he hRest ih =>
    have hHi : a.pc < 2148 := by
      by_contra! hBad
      exact Nat.not_le_of_lt hu (openingFloor 1 (.event he hRest) hBad)
    obtain ⟨hS,hV⟩ := openingNeitherCollective hs hHi he
    have hh := ih (hLower hs (.inr ⟨_,rfl,he⟩)) hu
    simpa only [List.countP_cons,hS,hV,Bool.false_eq_true,ite_false,Nat.add_zero] using hh

private theorem countsAtOpeningKey {l : Launch} {X : Execution}
    {g index shuffles votes : Nat} {after ready : TState}
    (hMeta : OpeningMetadataCounts l X g shuffles votes)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (index+1)) (some after))
    (hPc : after.pc = 2146) (hStep : Tau kernel Assumptions.all l g after ready)
    (hReady : ready.pc = 2148) (hBound : index+1 ≤ (X.tr g).length) :
    ((X.tr g).take (index+1)).countP Execution.isShfl = shuffles ∧
      ((X.tr g).take (index+1)).countP isFullWarpVote = votes := by
  obtain ⟨pos,t,u,hu,ht,hLocal,hS,hV⟩ := hMeta
  have hBefore : pos ≤ index := by
    by_contra! hAfter
    have hSplit := List.take_append_drop (index+1) ((X.tr g).take pos)
    rw [List.take_take,Nat.min_eq_left (show index+1 ≤ pos by omega)] at hSplit
    have walk := (hPast.after_returned_prefix (hSplit.symm ▸ ht)).returning_reach.append
      (TraceReach.of_local hLocal)
    have hCannot {final : TState} {events : List Event}
        (h : TraceReach kernel Assumptions.all l g after events final)
        (hFinal : final.pc = 2109) : False := by
      cases h with
      | refl => omega
      | @tau a b final es ht hTail =>
        have hSame : b = ready := Out.tau.inj (ht.symm.trans hStep)
        subst b
        have h := openingFloor 1 hTail (show 2148 ≤ ready.pc by omega)
        change 2148 ≤ final.pc at h
        omega
      | event he _ => exact not_tau_of_stops (stops_of_estep he) hStep
    exact hCannot walk hu
  have hSplit := List.take_append_drop pos ((X.tr g).take (index+1))
  rw [List.take_take,Nat.min_eq_left (show pos ≤ index+1 by omega)] at hSplit
  have hs : ((X.tr g).take (index+1)).drop pos ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [List.length_drop,List.length_take,Nat.min_eq_left hBound]
    omega
  have hTail := ht.after_returned_prefix (hSplit.symm ▸ hPast)
  obtain ⟨hs',hv'⟩ := openingNoCollectives (hTail.after_local_nonempty hLocal hs).returning_reach
    hu.ge (by omega)
  constructor
  · rw [← hSplit,List.countP_append,hS,hs',Nat.add_zero]
  · rw [← hSplit,List.countP_append,hV,hv',Nat.add_zero]

/-- All opening K returns in the MMA warp form one actual broadcast checkpoint.
The two collective ordinals are inherited from each lane's selected metadata cursor. -/
theorem openingQKWarpOfAcquires (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hMeta : ∀ lane < 32, OpeningMetadataCounts l X (warpLane l g lane) shuffles votes)
    (hK : ∀ lane < 32, ∃ j, Thread.Mma.ReadyPoll l X (warpLane l g lane) j 0 0 true .cta ∧
      (Thread.Mma.atPrefix l X (warpLane l g lane) j).kvAcquires 0 = 0) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 2148 (fun _ => firstQKBroadcastFacts l)
      shuffles votes ends) := by
  classical
  let data (i : Fin 32) := Classical.choose (hK i.val i.isLt)
  have hwLane (i : Fin 32) := (Step.sameWarp_lane (lane := i.val)
    (show l.block%32 = 0 by rw [hp.block]) hg i.isLt).1
  have hLane (i : Fin 32) := openedKeyLaneCursor hp hMax (hwLane i).1.2.1
    ((hwLane i).2.symm.trans hw)
    (Classical.choose_spec (hK i.val i.isLt)).1
    (Classical.choose_spec (hK i.val i.isLt)).2
  choose after ready last hPast hTail hPc hStep hAt using hLane
  have hGet (i : Fin 32) := openingKeyDecoded hp hMax.1 (hwLane i).1.2.1
    ((hwLane i).2.symm.trans hw) (Classical.choose_spec (hK i.val i.isLt)).1
    (Classical.choose_spec (hK i.val i.isLt)).2
  have hCounts (i : Fin 32) : _ :=
    countsAtOpeningKey (hMeta i.val i.isLt) (hPast i) (hPc i) (hStep i) (hAt i).1
      (len_of_get (hGet i))
  let getLane (lane : Nat) : Fin 32 := ⟨lane%32,Nat.mod_lt _ (by decide)⟩
  have hGetLane (lane : Nat) (hl : lane < 32) : getLane lane = ⟨lane,hl⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hl)
  refine ⟨fun lane => last (getLane lane),⟨?_⟩⟩
  refine ⟨⟨fun lane => data (getLane lane)+1,fun lane => after (getLane lane),
      fun lane => ready (getLane lane),⟨?_,?_⟩,?_,?_,?_⟩,
    ?_,?_,?_,?_⟩
  · intro lane hl
    rw [hGetLane lane hl]
    exact (hCounts ⟨lane,hl⟩).1
  · intro lane hl
    rw [hGetLane lane hl]
    exact (hCounts ⟨lane,hl⟩).2
  · intro lane hl
    rw [hGetLane lane hl]
    exact hTail ⟨lane,hl⟩
  · intro lane hl
    rw [hGetLane lane hl]
    exact Relation.ReflTransGen.single (hStep ⟨lane,hl⟩)
  · intro lane hl
    rw [hGetLane lane hl]
    exact hAt ⟨lane,hl⟩
  · intro lane _
    exact Nat.succ_pos _
  · intro lane hl
    change data (getLane lane)+1 ≤ (X.tr (warpLane l g lane)).length
    rw [hGetLane lane hl]
    exact len_of_get (hGet ⟨lane,hl⟩)
  · intro lane hl hLast
    change data (getLane lane)+1 = (X.tr (warpLane l g lane)).length at hLast
    rw [hGetLane lane hl] at hLast
    exact releasedIfLast (hGet ⟨lane,hl⟩) (by intro h; cases h) hLast
  · intro lane hl
    change Run kernel Assumptions.all l (warpLane l g lane) {}
      ((X.tr (warpLane l g lane)).take (data (getLane lane)+1)) (some (after (getLane lane)))
    rw [hGetLane lane hl]
    exact hPast ⟨lane,hl⟩

end PTX.Kernels.TmlFa4Fwd.Mma

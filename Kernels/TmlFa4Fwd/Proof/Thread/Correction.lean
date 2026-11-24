-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BarrierCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
public import Kernels.TmlFa4Fwd.Proof.CorrectionNamedBarrierIds
public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseIssuer
public import Kernels.TmlFa4Fwd.Proof.FirstStatsOrdinal
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow Prologue

/-- Which occurrence of the correction protocol a lane is performing. -/
inductive CorrectionRound where
  | initial
  | rescale
  | terminal
deriving DecidableEq

/-- Role-local observations exposed to the synchronization and output proofs. -/
inductive CorrectionAction where
  | statsWait (round : CorrectionRound) (stage : Fin 2)
  | statsCredit (stage : Fin 2)
  | accumulatorCredit (round : CorrectionRound) (stage : Fin 2)
  | accumulatorAcquire (stage : Fin 2)
  | outputAcquire (stage : Fin 2)
  | outputFence (stage : Fin 2)
  | outputReady (stage : Fin 2)
  | lseStore (stage : Fin 2)
deriving DecidableEq

/-- Counts and last role-local observation at the next event boundary. -/
structure CorrectionState where
  count : CorrectionAction → Nat := fun _ => 0
  barrier : Nat → Nat := fun _ => 0
  latest : Option CorrectionAction := none

private def correctionStatsPc (round : CorrectionRound) (stage : Fin 2) : Nat :=
  match round with
  | .initial => if stage.val = 0 then 7985 else 7988
  | .rescale => Correction.statsBarrierPc stage true
  | .terminal => Correction.statsBarrierPc stage false

private def correctionAccumulatorCreditPc (round : CorrectionRound) (stage : Fin 2) : Nat :=
  match round with
  | .initial => if stage.val = 0 then 7752 else 7754
  | .rescale => if stage.val = 0 then 8223 else 8442
  | .terminal => Correction.outputFencePc stage + 1

private def correctionReadyPc (stage : Fin 2) : Nat := Correction.outputFencePc stage + 2

private def correctionRoundSites (site : CorrectionRound → Fin 2 → Nat)
    (act : CorrectionRound → Fin 2 → CorrectionAction) : List (Nat × CorrectionAction) :=
  [ (site .initial 0, act .initial 0), (site .initial 1, act .initial 1),
    (site .rescale 0, act .rescale 0), (site .rescale 1, act .rescale 1),
    (site .terminal 0, act .terminal 0), (site .terminal 1, act .terminal 1) ]

private def correctionStatsCreditSites : List (Nat × CorrectionAction) :=
  [ (7987, .statsCredit 0), (8224, .statsCredit 1), (8443, .statsCredit 0),
    (8464, .statsCredit 1), (8468, .statsCredit 0), (8764, .statsCredit 1) ]

private def correctionSites : List (Nat × CorrectionAction) :=
  correctionRoundSites correctionStatsPc .statsWait ++ correctionStatsCreditSites ++
    correctionRoundSites correctionAccumulatorCreditPc .accumulatorCredit ++
    [ (correctionReadyPc 0, .outputReady 0), (correctionReadyPc 1, .outputReady 1),
      (Correction.outputFencePc 0, .outputFence 0),
      (Correction.outputFencePc 1, .outputFence 1),
      (8473, .accumulatorAcquire 0), (8769, .accumulatorAcquire 1),
      (8476, .outputAcquire 0), (8772, .outputAcquire 1), (9201, .outputAcquire 1),
      (9073, .lseStore 0), (9082, .lseStore 1) ]

private def correctionAccepts : CorrectionAction → Kind → Bool
  | .statsWait .., .bar _ (some 64) .sync => true
  | .statsCredit _, .arrive _ 0 _ true .cta => true
  | .accumulatorCredit .., .arrive _ 0 _ true .cta => true
  | .outputReady _, .arrive _ 0 1 true .cta => true
  | .outputFence _, .fenceProxy (.async (some (.shared .cta))) none => true
  | .accumulatorAcquire _, .wait _ _ true true .cta => true
  | .outputAcquire _, .wait _ _ true true .cta => true
  | .lseStore _, .wr _ _ => true
  | _, _ => false

/-- Decodes the observable role action of an event. -/
@[no_expose] def correctionAction (e : Event) : Option CorrectionAction :=
  (List.lookup e.pc correctionSites).filter (fun a => correctionAccepts a e.kind)

/-- The two startup arrivals mark the joint accumulator credit of their stage. -/
theorem correctionInitialAccumulatorObservation (stage : Fin 2)
    (target : Loc) (source : Nat)
    (h : source = if stage.val = 0 then 7752 else 7754) :
    correctionAction ⟨source, .arrive target 0 1 true .cta⟩ =
      some (.accumulatorCredit .initial stage) := by
  fin_cases stage <;> rw [h] <;> rfl

private theorem correctionAction_inv {e : Event} {a : CorrectionAction}
    (ha : correctionAction e = some a) :
    (e.pc, a) ∈ correctionSites ∧ correctionAccepts a e.kind = true := by
  unfold correctionAction at ha
  obtain ⟨hFind, hKind⟩ := Option.filter_eq_some_iff.mp ha
  obtain ⟨xs, ys, hList, _⟩ := List.lookup_eq_some_iff.mp hFind
  exact ⟨by rw [hList]; simp, hKind⟩

/-- Credit observations and their decoded source sites agree on the stage. -/
theorem correctionStatsCreditObservation {e : Event} (stage : Fin 2)
    {target : Loc} {n : Nat} (hk : e.kind = .arrive target 0 n true .cta) :
    correctionAction e = some (.statsCredit stage) ↔
      e.pc ∈ (if stage.val = 0 then [7987, 8443, 8468] else [8224, 8464, 8764]) := by
  constructor
  · intro h
    have hTable := (correctionAction_inv h).1
    fin_cases stage <;>
      simpa [correctionSites, correctionRoundSites, correctionStatsCreditSites] using hTable
  · intro h
    fin_cases stage <;> simp at h
    all_goals
      rcases h with hc | hc | hc <;>
        simp [correctionAction, hk, hc, correctionAccepts] <;> rfl

private theorem statsAccepted {k : Kind} {round : CorrectionRound} {stage : Fin 2}
    (h : correctionAccepts (.statsWait round stage) k = true) :
    ∃ id, k = .bar id (some 64) .sync := by
  unfold correctionAccepts at h
  split at h <;> first | exact ⟨_, rfl⟩ | contradiction

private theorem readyAccepted {k : Kind} {stage : Fin 2}
    (h : correctionAccepts (.outputReady stage) k = true) :
    ∃ target, k = .arrive target 0 1 true .cta := by
  unfold correctionAccepts at h
  split at h <;> first | exact ⟨_, rfl⟩ | contradiction

private theorem statsCreditAccepted {k : Kind} {stage : Fin 2}
    (h : correctionAccepts (.statsCredit stage) k = true) :
    ∃ target n, k = .arrive target 0 n true .cta := by
  unfold correctionAccepts at h
  split at h <;> first | exact ⟨_, _, rfl⟩ | contradiction

/-- A credit observation carries a releasing ordinary arrival. -/
theorem correctionStatsCreditKind {e : Event} {stage : Fin 2}
    (ha : correctionAction e = some (.statsCredit stage)) :
    ∃ target n, e.kind = .arrive target 0 n true .cta :=
  statsCreditAccepted (correctionAction_inv ha).2

/-- Only observations used by the correction protocol change the abstract state. -/
def correctionAdvance (s : CorrectionState) (e : Event) : CorrectionState :=
  let next := { s with barrier := advanceBarrierCursor s.barrier e }
  match correctionAction e with
  | none => next
  | some a =>
    { next with
      count := fun b => s.count b + if b = a then 1 else 0
      latest := some a }

/-- Sound state machine for a correction lane. -/
noncomputable def correctionMachine (l : Launch) (g : Nat) : Machine kernel Assumptions.all l g :=
  observationMachine l g ({} : CorrectionState) correctionAdvance

theorem correctionSound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    (correctionMachine l g).Sound :=
  observationSound hp g _ correctionAdvance

/-- The state immediately before a correction-lane event. -/
def correctionBefore (X : Execution) (i : EvId) : CorrectionState :=
  ((X.tr i.1).take i.2).foldl correctionAdvance {}

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

@[simp] theorem correctionAdvance_count (s : CorrectionState) (e : Event)
    (a : CorrectionAction) :
    (correctionAdvance s e).count a = s.count a + if correctionAction e = some a then 1 else 0 := by
  unfold correctionAdvance
  cases h : correctionAction e with
  | none => simp
  | some b => simp [eq_comm]

private theorem correctionFoldCount (es : List Event) (s : CorrectionState)
    (a : CorrectionAction) :
    (es.foldl correctionAdvance s).count a =
      s.count a + es.countP (fun e => decide (correctionAction e = some a)) := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, correctionAdvance_count, List.countP_cons]
    by_cases h : correctionAction e = some a <;> simp [h, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- The state counts preceding observations of each correction protocol action. -/
theorem correctionBefore_count (X : Execution) (i : EvId) (a : CorrectionAction) :
    (correctionBefore X i).count a =
      ((X.tr i.1).take i.2).countP (fun e => decide (correctionAction e = some a)) := by
  simpa [correctionBefore] using correctionFoldCount ((X.tr i.1).take i.2) {} a

/-- The barrier cursor agrees with the consistency model's arrival ordinal. -/
theorem correctionBarrierOrdinal (X : Execution) (i : EvId) (id : Nat) :
    (correctionBefore X i).barrier id =
      ((X.tr i.1).take i.2).countP (Execution.isBarId id) := by
  simp only [correctionBefore]
  simpa using foldBarrierCursor CorrectionState.barrier correctionAdvance
    (fun s e => by unfold correctionAdvance; cases correctionAction e <;> rfl)
    ((X.tr i.1).take i.2) {} id

private theorem statsLookup (e : Event) (round : CorrectionRound) (stage : Fin 2)
    (h : (e.pc, .statsWait round stage) ∈ correctionSites) :
    e.pc = correctionStatsPc round stage := by
  cases round <;> fin_cases stage <;>
    simpa [correctionSites, correctionRoundSites, correctionStatsCreditSites] using h

private theorem statsSiteMember (round : CorrectionRound) (stage : Fin 2) :
    correctionStatsPc round stage ∈ Correction.correctionStatsSites stage := by
  cases round <;> fin_cases stage <;> decide

/-- Every observed statistics wait is in the active correction body. -/
theorem correctionStatsWaitSiteBounds {e : Event} {round : CorrectionRound} {stage : Fin 2}
    (ha : correctionAction e = some (.statsWait round stage)) : 7980 ≤ e.pc ∧ e.pc < 9201 := by
  rw [statsLookup e round stage (correctionAction_inv ha).1]
  cases round <;> fin_cases stage <;> decide

/-- A rescale wait uses the decoded recurring rendezvous of its stage. -/
theorem correctionRescaleWaitSite {e : Event} {stage : Fin 2}
    (ha : correctionAction e = some (.statsWait .rescale stage)) :
    e.pc = Correction.statsBarrierPc stage true :=
  statsLookup e .rescale stage (correctionAction_inv ha).1

/-- The terminal wait uses the decoded end-of-loop rendezvous of its stage. -/
theorem correctionTerminalWaitSite {e : Event} {stage : Fin 2}
    (ha : correctionAction e = some (.statsWait .terminal stage)) :
    e.pc = Correction.statsBarrierPc stage false :=
  statsLookup e .terminal stage (correctionAction_inv ha).1

/-- A statistics wait uses the barrier of its observed stage and the issuing correction warp. -/
theorem correctionStatsWait (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} {round : CorrectionRound} {stage : Fin 2} (he : X.get i = some e)
    (ha : correctionAction e = some (.statsWait round stage)) :
    e.kind = .bar (Correction.statsBarrierId l i.1 stage) (some 64) .sync := by
  obtain ⟨hSite, hValid⟩ := correctionAction_inv ha
  obtain ⟨id, hk⟩ := statsAccepted hValid
  have hPc := statsLookup e round stage hSite
  have ee : e = ⟨e.pc, .bar id (some 64) .sync⟩ := by
    obtain ⟨pc, k⟩ := e
    change k = _ at hk
    subst k
    rfl
  have he' := he.trans (congrArg some ee)
  have hId := Correction.actualCorrectionStatsBarrierId hp hX stage
    (hPc.symm ▸ statsSiteMember round stage) he'
  rw [hk, hId]

/-- The indexed event is a correction statistics wait of the specified round and stage. -/
def CorrectionWaits (X : Execution) (i : EvId) (round : CorrectionRound) (stage : Fin 2) : Prop :=
  ∃ e, X.get i = some e ∧ correctionAction e = some (.statsWait round stage)

/-- Two observations of one correction round and stage use one instruction. -/
theorem CorrectionWaits.sameStation {X : Execution} {i j : EvId}
    {round : CorrectionRound} {stage : Fin 2} {e f : Event}
    (he : X.get i = some e) (hf : X.get j = some f)
    (hi : CorrectionWaits X i round stage) (hj : CorrectionWaits X j round stage) :
    e.pc = f.pc := by
  obtain ⟨_, hi, ha⟩ := hi
  obtain ⟨_, hj, hb⟩ := hj
  cases Option.some.inj (hi.symm.trans he)
  cases Option.some.inj (hj.symm.trans hf)
  exact (statsLookup _ round stage (correctionAction_inv ha).1).trans
    (statsLookup _ round stage (correctionAction_inv hb).1).symm

/-- The initial statistics rendezvous decodes to its correction stage. -/
theorem initialWaitObservation {X : Execution} {i : EvId} {id : Nat} (stage : Fin 2)
    (he : X.get i = some
      ⟨if stage.val = 0 then 7985 else 7988, .bar id (some 64) .sync⟩) :
    CorrectionWaits X i .initial stage :=
  ⟨_, he, by fin_cases stage <;> rfl⟩

/-- A rescale statistics rendezvous decodes to its correction stage. -/
theorem rescaleWaitObservation {X : Execution} {i : EvId} {id : Nat} (stage : Fin 2)
    (he : X.get i = some ⟨Correction.statsBarrierPc stage true, .bar id (some 64) .sync⟩) :
    CorrectionWaits X i .rescale stage :=
  ⟨_, he, by fin_cases stage <;> rfl⟩

/-- A terminal statistics rendezvous decodes to the same stage in the correction machine. -/
theorem terminalWaitObservation {X : Execution} {i : EvId} {id : Nat} (stage : Fin 2)
    (he : X.get i = some ⟨Correction.statsBarrierPc stage false, .bar id (some 64) .sync⟩) :
    CorrectionWaits X i .terminal stage :=
  ⟨_, he, by fin_cases stage <;> rfl⟩

/-- The observed wait advances the correction machine's cursor for its round and stage. -/
theorem correctionWaits (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {round : CorrectionRound} {stage : Fin 2} (h : CorrectionWaits X i round stage) :
    let action := CorrectionAction.statsWait round stage
    let before := correctionBefore X i
    ∃ after, Transition (correctionMachine l i.1) X i.2
      (.bar (Correction.statsBarrierId l i.1 stage) (some 64) .sync) before after ∧
        after.count action = before.count action + 1 ∧ after.latest = some action := by
  obtain ⟨e, he, ha⟩ := h
  refine ⟨correctionAdvance _ e,
    ⟨e, he, correctionStatsWait hp hX he ha, observationAfter .., rfl⟩, ?_, ?_⟩
  · simp [ha]
  · simp [correctionAdvance, ha]

/-- An initial correction wait joins the first generation for its stage. -/
theorem correctionInitialWaitOrdinal (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage : Fin 2} {members : Finset Nat} (h : CorrectionWaits X i .initial stage)
    (hSources : NamedBar.Sources l X (some 64) members (Correction.statsBarrierId l i.1 stage)) :
    (correctionBefore X i).barrier (Correction.statsBarrierId l i.1 stage) = 0 := by
  rw [correctionBarrierOrdinal]
  obtain ⟨e, he, ha⟩ := h
  have hPc := statsLookup e .initial stage (correctionAction_inv ha).1
  have hKind := correctionStatsWait hp hX he ha
  have ee : e = ⟨correctionStatsPc .initial stage,
      .bar (Correction.statsBarrierId l i.1 stage) (some 64) .sync⟩ := by
    obtain ⟨pc, k⟩ := e
    change pc = _ at hPc
    change k = _ at hKind
    rw [hPc, hKind]
  exact firstCorrectionStatsOrdinal hp hX stage (he.trans (congrArg some ee)) hSources

private theorem readyLookup (e : Event) (stage : Fin 2)
    (h : (e.pc, .outputReady stage) ∈ correctionSites) :
    e.pc = correctionReadyPc stage := by
  fin_cases stage <;>
    simpa [correctionSites, correctionRoundSites, correctionStatsCreditSites] using h

/-- Each output-ready notification targets the epilogue's object for that stage. -/
theorem correctionOutputReady (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} {stage : Fin 2} (he : X.get i = some e)
    (ha : correctionAction e = some (.outputReady stage)) :
    e.kind = .arrive (Epilogue.readyLoc l i.1 stage) 0 1 true .cta := by
  obtain ⟨hSite, hValid⟩ := correctionAction_inv ha
  obtain ⟨target, hk⟩ := readyAccepted hValid
  have hPc := readyLookup e stage hSite
  have ee : e = ⟨correctionReadyPc stage, .arrive target 0 1 true .cta⟩ := by
    obtain ⟨pc, k⟩ := e
    change k = _ at hk
    change pc = _ at hPc
    rw [hk, hPc]
  have he' := he.trans (congrArg some ee)
  have hLoc := Correction.correctionArriveAddressExact hp hX he' (by fin_cases stage <;> decide)
  rw [hk, hLoc]
  fin_cases stage <;> rfl

/-- The indicated event publishes a finalized output stage to writeback. -/
def CorrectionReady (X : Execution) (i : EvId) (stage : Fin 2) : Prop :=
  ∃ e, X.get i = some e ∧ correctionAction e = some (.outputReady stage)

/-- The role's ready observation identifies the decoded arrival and the ready object. -/
theorem CorrectionReady.decoded (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage : Fin 2} (h : CorrectionReady X i stage) :
    X.get i = some ⟨Correction.outputFencePc stage + 2,
      .arrive (Epilogue.readyLoc l i.1 stage) 0 1 true .cta⟩ := by
  obtain ⟨e, he, ha⟩ := h
  have hSite := readyLookup e stage (correctionAction_inv ha).1
  have hKind := correctionOutputReady hp hX he ha
  obtain ⟨pc, kind⟩ := e
  change pc = _ at hSite
  change kind = _ at hKind
  simpa only [hKind, hSite, correctionReadyPc] using he

/-- An actual arrival at a ready site comes from a correction lane and publishes that stage. -/
theorem CorrectionReady.ofActualArrival (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} (stage : Fin 2) {target : Loc}
    {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨Correction.outputFencePc stage + 2, .arrive target tx n rel scope⟩) :
    CorrectionReady X i stage ∧ 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
  obtain ⟨g, j⟩ := i
  have hs : Correction.outputFencePc stage + 2 = 8760 ∨
      Correction.outputFencePc stage + 2 = 9056 := by fin_cases stage <;> decide
  obtain ⟨rfl, rfl, rfl, rfl, hLo, hHi⟩ := Correction.correctionReadyOperands hp hX he hs
  refine ⟨⟨_, he, ?_⟩, hLo, hHi⟩
  fin_cases stage <;> rfl

private theorem lseWriteSource {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bytes : List Byte}
    (hw : X.Writes i a bytes) (hg : a.loc.space = .global) :
    ∃ pc ∈ lseStoreSites, X.get i = some ⟨pc, .wr a bytes⟩ := by
  have hIntent : X.Intent (.thread i) a true := .inr (.inl ⟨bytes, hw, rfl⟩)
  rcases globalWriteIntentSources hX hIntent hg with
    ⟨j, site, bs, hj, hSite, he⟩ | ⟨_, _, _, _, _, _, _, hj, _⟩
  · cases hj
    obtain ⟨pc, hf⟩ := hw
    have hEvent := Option.some.inj (hf.symm.trans he)
    have hBytes := (Kind.wr.inj (congrArg Event.kind hEvent)).2
    exact ⟨site, hSite, hBytes.symm ▸ he⟩
  · cases hj

/-- A correction LSE write updates one four-byte word of the packed result. -/
theorem lseWriteShape (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {a : Acc} {bytes : List Byte} (hw : X.Writes i a bytes) (hg : a.loc.space = .global) :
    ∃ row < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc row head ∧ a.size = 4 := by
  obtain ⟨pc, hs, he⟩ := lseWriteSource hX hw hg
  exact Correction.lseStoreSpecs hp hX i pc a bytes hs he

/-- A recorded synchronization on a statistics resource is a correction wait for its stage. -/
theorem correctionWaitOfStatisticsSync (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {id : Nat} {count : Option Nat}
    (hId : 3 ≤ id ∧ id < 11) (hSync : BarrierArrival X i id count .sync) :
    ∃ stage round, CorrectionWaits X i round stage ∧
      id = Correction.statsBarrierId l i.1 stage := by
  obtain ⟨⟨site, kind⟩, hGet, hKind⟩ := hSync
  change kind = _ at hKind
  subst kind
  have hCount : count = some 64 := by
    have h := actualNamedBarrierCountById hp hX hGet
    simpa [countOfBarrierId, hId.2, show id ≠ 0 by omega, show id ≠ 2 by omega] using h
  subst count
  obtain ⟨hSite, hNamedCount, hMode, _, _⟩ := actualNamedBarrier hp hX hGet
  rcases count64StatsSites hSite hNamedCount.symm with hScore | ⟨stage, hCorrection⟩
  · simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at hScore
    rcases hScore with rfl | rfl | rfl | rfl <;> cases hMode
  · have hExact := Correction.actualCorrectionStatsBarrierId hp hX stage hCorrection hGet
    refine ⟨stage, ?_⟩
    fin_cases stage <;> simp [Correction.correctionStatsSites] at hCorrection
    all_goals
      rcases hCorrection with rfl | rfl | rfl
      · exact ⟨.initial, ⟨_, hGet, rfl⟩, hExact⟩
      · exact ⟨.rescale, ⟨_, hGet, rfl⟩, hExact⟩
      · exact ⟨.terminal, ⟨_, hGet, rfl⟩, hExact⟩

end PTX.Kernels.TmlFa4Fwd.Thread

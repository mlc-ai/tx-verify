-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Snoc.SnocObjectHistory
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Tmem.TmemPairExtend
public import Lemmas.Snoc.SnocResourceWaiting
public import Lemmas.Snoc.SnocMemory
public import Lemmas.Snoc.SnocOrder
public import Lemmas.Tcgen05.TcExtend
public import Lemmas.Snoc.SnocObjectPreserve

@[expose] public section

/-! Appending an ordinary event preserves every execution-metadata obligation.

A kind is *plain* when it is no collective, register-pool request, CLC issue, tensor
transfer, bulk wait, tensor-core operation, releasing arrival or releasing write. Its
own metadata is then empty. Appending it only makes the thread's previous last event
non-final, so the remaining premises say that this previous event, if it is a cluster
barrier, register request or paired-TMEM wait, has already been released. -/

namespace PTX
open AsyncCopy MBarrier
noncomputable section

/-- Event kinds that change no collective, register-pool, CLC-issue, tensor, bulk-wait or
tensor-core history. -/
def Kind.Quiet : Kind → Prop
  | .setMaxReg .. | .warpBar .. | .elect .. | .vote .. | .voteMode .. | .redux .. | .match_ ..
  | .activemask .. | .cluster .. | .clcIssue ..
  | .tensorIssue .. | .tensorStore .. | .bulkWait .. | .tc .. => False
  | _ => True

/-- Quiet kinds that are also no barrier, `fence.sc`, releasing arrival or releasing write, so
that they add no causality edge into existing events and leave the Fence-SC order of `X`
complete. -/
def Kind.Plain : Kind → Prop
  | .setMaxReg .. | .warpBar .. | .elect .. | .vote .. | .voteMode .. | .redux .. | .match_ ..
  | .activemask .. | .bar .. | .cluster .. | .clcIssue ..
  | .tensorIssue .. | .tensorStore .. | .bulkWait .. | .tc .. => False
  | .fence .sc _ => False
  | .arrive _ _ _ release _ => release = false
  | .wr a _ => a.release = false
  | _ => True

section
variable {L : Launch} {A : List Assumption} {K : Kernel} {mem0 : Mem0} {X : Execution}
  {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- If a cancellation request exists, thread `g`'s cluster has been launched: the condition for
`g`'s first event (OBJ-CLC-ORIGIN). -/
def Step.Launched (L : Launch) (Z : Execution) (g : Nat) : Prop :=
  (∃ i s ts, Z.ClcIssue i s ts) → Z.clcState.owner (L.clusterOfCta (g / L.block)) = some .launched

/-- The thread's previous last event, if it blocks, has been released. -/
structure LastReleased (L : Launch) (X : Execution) (g : Nat) : Prop where
  cluster : ∀ pc op, X.get (g, (X.tr g).length - 1) = some ⟨pc, .cluster op⟩ →
    ClusterRecorded L X (g, (X.tr g).length - 1)
  setMaxNReg : ∀ pc inc n inst, SetMaxNReg.Request X (g, (X.tr g).length - 1) pc inc n inst →
    Ready L X (g, (X.tr g).length - 1)
  tmemPair : ∀ pc grp dst act, X.get (g, (X.tr g).length - 1) =
    some ⟨pc, .tc (.resource grp dst act)⟩ → Ready L X (g, (X.tr g).length - 1)

/-- A previous last event that is neither a cluster barrier, a register request nor a
paired-TMEM operation needs no release. -/
theorem LastReleased.of_kind
    (h : ∀ q, X.get (g, (X.tr g).length - 1) = some q →
      (∀ op, q.kind ≠ .cluster op) ∧ (∀ inc n inst, q.kind ≠ .setMaxReg inc n inst) ∧
      ∀ k, q.kind ≠ .tc k) :
    LastReleased L X g := by
  refine ⟨fun pc op hq => ((h _ hq).1 op rfl).elim, fun pc inc n inst hq => ?_, ?_⟩
  · exact ((h _ hq).2.1 inc n inst rfl).elim
  · intro pc grp dst act hq
    exact ((h _ hq).2.2 _ rfl).elim

private theorem Kind.quiet_cases (hp : e.kind.Quiet) :
    (∀ inc n inst, e.kind ≠ .setMaxReg inc n inst) ∧ (∀ mask inst, e.kind ≠ .warpBar mask inst) ∧
    (∀ mask inst leader, e.kind ≠ .elect mask inst leader) ∧
    (∀ op, e.kind ≠ .cluster op) ∧ (∀ s ts, e.kind ≠ .clcIssue s ts) ∧
    (∀ m s, e.kind ≠ .tensorIssue m s) ∧ (∀ m s, e.kind ≠ .tensorStore m s) ∧
    (∀ mode n, e.kind ≠ .bulkWait mode n) ∧ (∀ k, e.kind ≠ .tc k) ∧
    (∀ m a b, e.kind ≠ .vote m a b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> rw [h] at hp <;>
    exact hp

theorem Kind.Plain.quiet {k : Kind} (hp : k.Plain) : k.Quiet := by
  cases k <;> simp_all [Kind.Plain, Kind.Quiet]

theorem Kind.Plain.not_fenceSc {k : Kind} (hp : k.Plain) (s : MbarScope) : k ≠ .fence .sc s := by
  rintro rfl; exact hp

theorem Kind.Quiet.warpValue {k : Kind} (hp : k.Quiet) : k.warpValue = false := by
  cases k <;> simp_all [Kind.Quiet, Kind.warpValue]

theorem Kind.Quiet.laneValue {k : Kind} (hp : k.Quiet) : k.laneValue = false := by
  cases k <;> simp_all [Kind.Quiet, Kind.laneValue]

private theorem Kind.plain_cases (hp : e.kind.Plain) :
    (∀ inc n inst, e.kind ≠ .setMaxReg inc n inst) ∧ (∀ mask inst, e.kind ≠ .warpBar mask inst) ∧
    (∀ mask inst leader, e.kind ≠ .elect mask inst leader) ∧ (∀ id count mode,
        e.kind ≠ .bar id count mode) ∧
    (∀ op, e.kind ≠ .cluster op) ∧ (∀ s ts, e.kind ≠ .clcIssue s ts) ∧
    (∀ m s, e.kind ≠ .tensorIssue m s) ∧ (∀ m s, e.kind ≠ .tensorStore m s) ∧
    (∀ mode n, e.kind ≠ .bulkWait mode n) ∧
    (∀ m tx count sc, e.kind ≠ .arrive m tx count true sc) ∧
    (∀ a bs, e.kind = .wr a bs → a.release = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (intro h; rw [h] at hp; exact hp)
    | (intro h; rw [h] at hp; simp [Kind.Plain] at hp)
    | (rename_i h; rw [h] at hp; exact hp)

/-- Appending a quiet event preserves all non-memory execution obligations, given the values of
the lane collectives (which an appended exit may constrain), the tensor-core read obligation and
the Fence-SC order, which depend on the causality the event adds, the allocation result rule,
which constrains a store after a recorded allocation, atomicity, which an appended
read-modify-write constrains, the matrix instances, which an appended matrix event may complete,
and the reduction values, which an appended linear copy may constrain. -/
theorem ExtensionObligations.snoc_quiet_of (hX : Consistent L K A mem0 X) (hp : e.kind.Quiet)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hvote : VoteOk L (X.snoc g e r)) (hwv : WarpValueOk L (X.snoc g e r))
    (hres : Tmem.Pair.ResultOk L (X.snoc g e r))
    (hread : TcMma.ReadOk L A (X.snoc g e r))
    (hatomic : AtomicOk L (X.snoc g e r))
    (hfence : FenceScOk L (X.snoc g e r) (baseCausality L (X.snoc g e r)))
    (hmatrix : MatrixOk L A (X.snoc g e r)) (hreduce : TensorStore.ReduceOk A (X.snoc g e r)) :
    ExtensionObligations L A (X.snoc g e r) := by
  obtain ⟨-, hwb, hel, -, hci, -, -, -, -, -⟩ := Kind.quiet_cases hp
  have le : X.le (X.snoc g e r) := le_snoc
  have hissue (i : EvId) (s : Clc.Spec) (ts : List Nat) :
      (X.snoc g e r).ClcIssue i s ts ↔ X.ClcIssue i s ts := snoc_kind_iff (hci s ts)
  refine {
    ctaBar := hX.ctaBar.snoc, cluster := hX.cluster.preserving le rfl,
    elect := ?_, vote := hvote, warpValue := hwv,
    warpBar := ?_, matrix := hmatrix, clc := ?_,
    tensor := ?_, store := ?_, atomic := hatomic, fenceSc := hfence,
    tmemPair := hX.tmemPair.mono le (fun _ => rfl) rfl,
    tmemPairResult := hres,
    tmemPairCompletion :=
      Tmem.Pair.completionClosed_of_growth le rfl rfl hX.tmemPair hX.tmemPairCompletion,
    tcCommit := ?_,
    mmaCompletion := TcMma.completionClosed_of_growth le rfl hX.tma.2.1 hX.mmaCompletion,
    tcRead := hread, reduce := hreduce }
  · have hiff {i : EvId} {pc mask inst leader : Nat} :
        (X.snoc g e r).Elect i pc mask inst leader ↔ X.Elect i pc mask inst leader :=
      ⟨fun h => snoc_get_not_kind h (by intro hk; exact hel _ _ _ hk), Execution.le_get le⟩
    simpa only [ElectOk, hiff] using hX.elect
  · have hiff {i : EvId} {mask inst : Nat} :
        (X.snoc g e r).WarpBar i mask inst ↔ X.WarpBar i mask inst :=
      snoc_kind_iff (hwb mask inst)
    simpa only [WarpBarOk, hiff] using hX.warpBar
  · obtain ⟨ha, hr, he, hi, hl⟩ := hX.clc
    refine ⟨ha, ?_, ?_, ?_, ?_⟩
    · intro rq a hh
      obtain ⟨i, s, ts, hh, his⟩ := hr rq a hh
      exact ⟨i, s, ts, hh, (hissue ..).mpr his⟩
    · intro i hh
      obtain ⟨s, ts, his⟩ := he i hh
      exact ⟨s, ts, (hissue ..).mpr his⟩
    · intro i s ts hh
      exact hi i s ts ((hissue ..).mp hh)
    · rintro ⟨i, s, ts, his⟩ h hh hn
      by_cases hg : h = g
      · subst hg
        rcases hne with hne | hl'
        · exact hl ⟨i, s, ts, (hissue ..).mp his⟩ h hh hne
        · exact hl' ⟨i, s, ts, (hissue ..).mp his⟩
      · apply hl ⟨i, s, ts, (hissue ..).mp his⟩ h hh
        simpa only [snoc_tr, ite_eq_right hg] using hn
  · intro i o ho
    obtain ⟨⟨addr, j, hj⟩, rest⟩ := hX.tensor i o ho
    exact ⟨⟨addr, j, Execution.le_get le hj⟩, rest⟩
  · intro i o ho
    obtain ⟨⟨addr, j, hj⟩, rest⟩ := hX.store i o ho
    exact ⟨⟨addr, j, Execution.le_get le hj⟩, rest⟩
  · intro i rank hr
    obtain ⟨⟨s, loc, hc, ht⟩, hd⟩ := hX.tcCommit i rank hr
    have hi : i.2 < (X.tr i.1).length := len_of_get hc.choose_spec
    refine ⟨⟨s, loc, ?_, ht⟩, ?_⟩
    · obtain ⟨q, hq⟩ := hc
      exact ⟨q, Execution.le_get le hq⟩
    · intro mma hm
      exact hd mma ((tracksMma_snoc_old hi).mp hm)

/-- Appending a quiet event that is no exit preserves all non-memory execution obligations, given
the obligations that the event itself may constrain (`snoc_quiet_of`). -/
theorem ExtensionObligations.snoc_quiet (hX : Consistent L K A mem0 X) (hp : e.kind.Quiet)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hx : e.kind ≠ .exit)
    (hres : Tmem.Pair.ResultOk L (X.snoc g e r))
    (hread : TcMma.ReadOk L A (X.snoc g e r))
    (hatomic : AtomicOk L (X.snoc g e r))
    (hfence : FenceScOk L (X.snoc g e r) (baseCausality L (X.snoc g e r)))
    (hmatrix : MatrixOk L A (X.snoc g e r)) (hreduce : TensorStore.ReduceOk A (X.snoc g e r)) :
    ExtensionObligations L A (X.snoc g e r) :=
  ExtensionObligations.snoc_quiet_of hX hp hne (snoc_voteOk hX.vote hp.laneValue hx)
    (snoc_warpValueOk hX.warpValue hp.laneValue hx) hres hread hatomic hfence hmatrix hreduce

/-- A plain event also adds no causality edge into existing events. When it is no atomic
read-modify-write, no matrix event, no linear copy and no exit, every obligation of the
extension follows from `X`. -/
theorem ExtensionObligations.snoc_plain (hX : Consistent L K A mem0 X) (hp : e.kind.Plain)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hx : e.kind ≠ .exit)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new) (hmat : isMatrix e = false)
    (hcp : ∀ s, e.kind ≠ .copy s) (hres : Tmem.Pair.ResultOk L (X.snoc g e r)) :
    ExtensionObligations L A (X.snoc g e r) := by
  have hsc := hp.not_fenceSc
  obtain ⟨-, hwb, -, hnb, -, -, -, -, -, hna, -⟩ := Kind.plain_cases hp
  have htc := (Kind.quiet_cases hp.quiet).2.2.2.2.2.2.2.2.1
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f) := fun hf =>
    baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf) hwb hnb hna hsc hf
  exact ExtensionObligations.snoc_quiet hX hp.quiet hne hx hres
    (readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo
      (by intro pc ta vals sh h; exact (htc _ (congrArg Event.kind h)).elim))
    (hX.atomic.snoc hX.store hX.tma.1 hrmw)
    (hX.fenceSc.snoc hsc fun _ _ hb h => (hbo hb).mp h)
    (hX.matrix.snoc hmat) (hX.reduce.snoc hcp)

/-- An exit appended to a thread that has not exited: every obligation of the extension follows
from `X`, the values of the lane collectives because every existing collective is complete
(`snoc_exit_voteOk`, `snoc_exit_warpValueOk`). -/
theorem ExtensionObligations.snoc_exit (hX : Consistent L K A mem0 X) (he : e.kind = .exit)
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) :
    ExtensionObligations L A (X.snoc g e r) := by
  have hp : e.kind.Plain := by rw [he]; trivial
  have hsc := hp.not_fenceSc
  obtain ⟨-, hwb, -, hnb, -, -, -, -, -, hna, -⟩ := Kind.plain_cases hp
  have htc := (Kind.quiet_cases hp.quiet).2.2.2.2.2.2.2.2.1
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f) := fun hf =>
    baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf) hwb hnb hna hsc hf
  exact ExtensionObligations.snoc_quiet_of hX hp.quiet hne (snoc_exit_voteOk hX he hgx)
    (snoc_exit_warpValueOk hX he hgx)
    (hX.tmemPairResult.snoc_not_wr (fun _ _ _ h => by rw [h] at he; cases he))
    (readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo
      (by intro pc ta vals sh h; exact (htc _ (congrArg Event.kind h)).elim))
    (hX.atomic.snoc hX.store hX.tma.1 (fun _ _ _ h => by rw [h] at he; cases he))
    (hX.fenceSc.snoc hsc fun _ _ hb h => (hbo hb).mp h)
    (hX.matrix.snoc (by obtain ⟨pc, k⟩ := e; simp only at he; subst he; rfl))
    (hX.reduce.snoc (fun _ h => by rw [h] at he; cases he))

/-- An appended object record changes no atomic operation, old-value source or moral strength. -/
theorem AtomicOk.appendObject {Z : Execution} {mb : Loc} {rec : Record Ref} (h : AtomicOk L Z) :
    AtomicOk L (Z.appendObject mb rec) := by
  refine ⟨fun p q l n k hp hq hne hs hk =>
    h.unique p q l n k hp hq hne ((rmwStrong_congr rfl rfl).mp hs) hk, fun p hc => h.acyclic p ?_⟩
  refine Relation.TransGen.mono (fun a b hab => ?_) _ _ hc
  obtain ⟨l, n, ha, hb, hs, rest⟩ := hab
  exact ⟨l, n, ha, hb, (rmwStrong_congr rfl rfl).mp hs, rest⟩

/-- Object records enter only the tensor-core read obligation and the Fence-SC order, through
the causality they add. -/
theorem ExtensionObligations.appendObject {Z : Execution} {mb : Loc} {rec : Record Ref}
    (h : ExtensionObligations L A Z) (hread : TcMma.ReadOk L A (Z.appendObject mb rec))
    (hfence : FenceScOk L (Z.appendObject mb rec) (baseCausality L (Z.appendObject mb rec))) :
    ExtensionObligations L A (Z.appendObject mb rec) := by
  obtain ⟨hcb, hcl, hel, hv, hwv, hwb, hmat, hclc, hten, hst, hat, -, htp, hres, hcomp, hcom,
    hmma, -, hred⟩ := h
  exact ⟨hcb, hcl, hel, hv, hwv, hwb, hmat, hclc, hten, hst, hat.appendObject, hfence, htp, hres,
    hcomp, hcom, TcMma.completionClosed_of_trace hmma rfl rfl, hread,
    hred.of_tensorStores rfl fun _ _ _ _ hY _ _ => ⟨hY, rfl⟩⟩

/-- A quiet event that also records an mbarrier object action. -/
theorem ExtensionObligations.snocObject_quiet {mb : Loc} {rec : Record Ref}
    (hX : Consistent L K A mem0 X) (hp : e.kind.Quiet)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hx : e.kind ≠ .exit)
    (hres : Tmem.Pair.ResultOk L (X.snoc g e r))
    (hread : TcMma.ReadOk L A (X.snoc g e r))
    (hatomic : AtomicOk L (X.snoc g e r))
    (hfence : FenceScOk L (X.snoc g e r) (baseCausality L (X.snoc g e r)))
    (hmatrix : MatrixOk L A (X.snoc g e r)) (hreduce : TensorStore.ReduceOk A (X.snoc g e r))
    (hread' : TcMma.ReadOk L A (X.snocObject g e r mb rec))
    (hfence' : FenceScOk L (X.snocObject g e r mb rec)
      (baseCausality L (X.snocObject g e r mb rec))) :
    ExtensionObligations L A (X.snocObject g e r mb rec) :=
  (ExtensionObligations.snoc_quiet hX hp hne hx hres hread hatomic hfence hmatrix
    hreduce).appendObject hread' hfence'

/-- A plain event that also records an mbarrier object action. -/
theorem ExtensionObligations.snocObject_plain {mb : Loc} {rec : Record Ref}
    (hX : Consistent L K A mem0 X) (hp : e.kind.Plain)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hx : e.kind ≠ .exit)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new) (hmat : isMatrix e = false)
    (hcp : ∀ s, e.kind ≠ .copy s)
    (hres : Tmem.Pair.ResultOk L (X.snoc g e r))
    (hread : TcMma.ReadOk L A (X.snocObject g e r mb rec))
    (hfence : FenceScOk L (X.snocObject g e r mb rec)
      (baseCausality L (X.snocObject g e r mb rec))) :
    ExtensionObligations L A (X.snocObject g e r mb rec) :=
  (ExtensionObligations.snoc_plain hX hp hne hx hrmw hmat hcp hres).appendObject hread hfence

end
end
end PTX

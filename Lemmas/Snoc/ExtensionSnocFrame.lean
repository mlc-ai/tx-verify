-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.ExtensionSnoc
public import Lemmas.Snoc.SnocObjectHistory

@[expose] public section

/-! Appending an arbitrary event preserves the execution-metadata obligations it does not touch.

`ExtensionObligations.snoc_frame` covers any event that is no warp barrier, election,
lane-value collective or exit: the barrier, completion and commit obligations follow from the
previous history. The obligations that an event may itself discharge or constrain (CLC,
paired-TMEM result, tensor-core reads, atomicity, Fence-SC and matrix instances) are premises,
with frame lemmas for events that do not touch them (`ClcOk.snoc`, `Consistent.tcRead_snoc`,
`Consistent.fenceSc_snoc`, `AtomicOk.snoc`, `MatrixOk.snoc`). -/

namespace PTX
open AsyncCopy MBarrier
noncomputable section

section
variable {L : Launch} {A : List Assumption} {K : Kernel} {mem0 : Mem0} {X : Execution}
  {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- A previous last event needs only the release that its own kind requires: a cluster
barrier must be recorded, while register requests and TMEM resource operations are excluded. -/
theorem LastReleased.of_get {q : Event} (hq : X.get (g, (X.tr g).length - 1) = some q)
    (hcl : ∀ pc op, q = ⟨pc, .cluster op⟩ → ClusterRecorded L X (g, (X.tr g).length - 1))
    (hsr : ∀ inc n inst, q.kind ≠ .setMaxReg inc n inst)
    (hres : ∀ grp dst act, q.kind ≠ .tc (.resource grp dst act)) : LastReleased L X g := by
  refine ⟨fun pc op h => hcl pc op ?_, fun pc inc n inst h => ?_, ?_⟩
  · rw [hq] at h; exact Option.some.inj h
  · rw [SetMaxNReg.Request, hq] at h
    exact (hsr inc n inst (congrArg Event.kind (Option.some.inj h))).elim
  · intro pc grp dst act h
    rw [hq] at h
    exact (hres grp dst act (congrArg Event.kind (Option.some.inj h))).elim

/-- An event that issues no CLC request preserves the CLC obligation, when its thread has started
or its cluster has been launched. -/
theorem ClcOk.snoc (h : ClcOk L X) (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hci : ∀ s ts, e.kind ≠ .clcIssue s ts) :
    ClcOk L (X.snoc g e r) := by
  have hissue (i : EvId) (s : Clc.Spec) (ts : List Nat) :
      (X.snoc g e r).ClcIssue i s ts ↔ X.ClcIssue i s ts := snoc_kind_iff (hci s ts)
  obtain ⟨ha, hr, he, hi, hl⟩ := h
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

/-- An event that adds no causality edge into existing events and loads no tensor-core words
preserves the tensor-core read obligation. -/
theorem Consistent.tcRead_snoc (hX : Consistent L K A mem0 X)
    (hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst) (hnb : ∀ id count mode,
        e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    (hld : ∀ pc ta vals sh, e ≠ ⟨pc, .tc (.ld ta vals sh)⟩) :
    TcMma.ReadOk L A (X.snoc g e r) :=
  readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1
    (baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf) hwb hnb hna hsc)
    (fun pc ta vals sh h => (hld pc ta vals sh h).elim)

/-- An event that adds no causality edge into existing events and is no `fence.sc` preserves the
Fence-SC obligation (MEM-FENCE-SC). -/
theorem Consistent.fenceSc_snoc (hX : Consistent L K A mem0 X)
    (hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst) (hnb : ∀ id count mode,
        e.kind ≠ .bar id count mode)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hsc : ∀ s, e.kind ≠ .fence .sc s) :
    FenceScOk L (X.snoc g e r) (baseCausality L (X.snoc g e r)) :=
  hX.fenceSc.snoc hsc fun _ _ hb h =>
    (baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf) hwb hnb hna hsc hb).mp h

/-- An event that is no tensor-core instruction and acts on no mbarrier keeps the
asynchronous effects valid. -/
theorem Consistent.tmaOk_snoc_unobserved (hX : Consistent L K A mem0 X)
    (hk : ∀ k, e.kind ≠ .tc k)
    (ha : ∀ l, objectAction (X.snoc g e r) X.async l (.thread (g, (X.tr g).length)) = none) :
    TmaOk (X.snoc g e r) :=
  ⟨snoc_copy_wellFormed hX.tma, tcEffectsOk_snoc hX.tma.2.1,
    snoc_objects_unchanged hX.effectValidity hk ha, snoc_arriveOk hX.tma.2.2.2⟩

/-- Appending an event that is no warp barrier, election, lane-value collective or exit preserves
all non-memory execution obligations, given the ones the event itself may discharge or constrain,
the reduction values among them (an appended linear copy may be a reduction). -/
theorem ExtensionObligations.snoc_frame_of (hX : Consistent L K A mem0 X)
    (hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst)
    (hel : ∀ mask inst leader, e.kind ≠ .elect mask inst leader)
    (hx : e.kind ≠ .exit) (hclc : ClcOk L (X.snoc g e r))
    (hres : Tmem.Pair.ResultOk L (X.snoc g e r))
    (hread : TcMma.ReadOk L A (X.snoc g e r)) (hatomic : AtomicOk L (X.snoc g e r))
    (hfence : FenceScOk L (X.snoc g e r) (baseCausality L (X.snoc g e r)))
    (hmatrix : MatrixOk L A (X.snoc g e r)) (hreduce : TensorStore.ReduceOk A (X.snoc g e r))
    (hlv : e.kind.laneValue = false := by rfl) :
    ExtensionObligations L A (X.snoc g e r) := by
  have le : X.le (X.snoc g e r) := le_snoc
  refine {
    ctaBar := hX.ctaBar.snoc, cluster := hX.cluster.preserving le rfl,
    elect := ?_, vote := snoc_voteOk hX.vote hlv hx,
    warpValue := snoc_warpValueOk hX.warpValue hlv hx,
    warpBar := ?_, matrix := hmatrix, clc := hclc,
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
      ⟨fun h => snoc_get_not_kind h (hel _ _ _), Execution.le_get le⟩
    simpa only [ElectOk, hiff] using hX.elect
  · have hiff {i : EvId} {mask inst : Nat} :
        (X.snoc g e r).WarpBar i mask inst ↔ X.WarpBar i mask inst :=
      snoc_kind_iff (hwb mask inst)
    simpa only [WarpBarOk, hiff] using hX.warpBar
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

/-- `snoc_frame_of` for an event that is no linear copy: the reduction values are those of `X`. -/
theorem ExtensionObligations.snoc_frame (hX : Consistent L K A mem0 X)
    (hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst)
    (hel : ∀ mask inst leader, e.kind ≠ .elect mask inst leader)
    (hx : e.kind ≠ .exit) (hclc : ClcOk L (X.snoc g e r))
    (hres : Tmem.Pair.ResultOk L (X.snoc g e r))
    (hread : TcMma.ReadOk L A (X.snoc g e r)) (hatomic : AtomicOk L (X.snoc g e r))
    (hfence : FenceScOk L (X.snoc g e r) (baseCausality L (X.snoc g e r)))
    (hmatrix : MatrixOk L A (X.snoc g e r)) (hcp : ∀ s, e.kind ≠ .copy s)
    (hlv : e.kind.laneValue = false := by rfl) :
    ExtensionObligations L A (X.snoc g e r) :=
  snoc_frame_of hX hwb hel hx hclc hres hread hatomic hfence hmatrix (hX.reduce.snoc hcp) hlv

end
end
end PTX

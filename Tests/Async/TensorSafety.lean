-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fin.VecNotation
public import Core.Async.Tensor.TensorSafety
public import Core.Assembly.Safety

namespace PTX.Tests.TensorSafety
noncomputable section

private def L : Launch := { grid := 2, block := 1, params := fun _ => none, clusterSize := 2 }
private def m : Loc := ⟨.shared, 0, 64⟩
private def spec : TensorCopy.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 0,
    128⟩, none⟩, m, true, .one⟩
private def X : Execution := {
  tr := fun g => if g = 0 then [⟨0, .mbInit m 1⟩, ⟨1, .tensorIssue 1024 spec⟩] else [],
  rf := fun _ _ => none }
private def allocated : Mem0 := fun _ => some none

private theorem issue : X.TensorIssue (0, 1) 1024 spec := ⟨1, rfl⟩
private theorem published : InitPublished L X (0, 0) (0, 1) m := by
  apply Or.inl
  apply Relation.TransGen.single
  exact Or.inl ⟨rfl, by decide, by decide⟩

-- The generic-proxy mbarrier operand needs publication, not an async proxy fence.
example : InitPublished L X (0, 0) (0, 1) m := published
example : ¬ ProxyBefore L X (0, 0) (0, 1) m := by
  rintro ⟨fence, sp, sc, hf, _⟩
  obtain ⟨g, i⟩ := fence
  simp [Execution.IsProxyFence, Execution.get, X] at hf
  split_ifs at hf <;> simp_all
  cases i with
  | zero => simp at hf
  | succ i => cases i <;> simp at hf

-- Reject a missing mbarrier allocation even before any copy effects are recorded: the mbarrier
-- of the load is an mbarrier operand (ERR-UNALLOCATED-ACCESS).
example : Unalloc (fun _ => none) X :=
  .inr ⟨(0, 1), m, m, Execution.UsesMbar.of_tensor issue, by simp [Acc.Covers, Loc.InRange],
    rfl⟩

-- Without the initialization, the load names an uninitialized mbarrier (ERR-MBAR-UNINITIALIZED).
private def uninit : Execution := {
  tr := fun g => if g = 0 then [⟨1, .tensorIssue 1024 spec⟩] else [],
  rf := fun _ _ => none }
example : MbarUninit L uninit := by
  refine ⟨(0, 0), m, Execution.UsesMbar.of_tensor (s := spec) (address := 1024) ⟨1, rfl⟩, ?_, ?_⟩
  · rintro count ⟨pc, h⟩
    simp [Execution.get, uninit] at h
  · rintro ⟨⟨g, j⟩, count, ⟨pc, h⟩, -⟩
    simp only [Execution.get, uninit] at h
    split_ifs at h <;> rcases j with _ | j <;> simp at h

private theorem issue_unique {i : EvId} {address : Nat} {s : TensorCopy.Spec}
    (h : X.TensorIssue i address s) : i = (0, 1) ∧ address = 1024 ∧ s = spec := by
  obtain ⟨g, j⟩ := i
  obtain ⟨pc, he⟩ := h
  change (if g = 0 then ([⟨0, .mbInit m 1⟩, ⟨1, .tensorIssue 1024 spec⟩] : List Event) else
    [])[j]? =
    some ⟨pc, .tensorIssue address s⟩ at he
  split_ifs at he with hg
  · subst g
    cases j with
    | zero => simp at he
    | succ j =>
      cases j with
      | zero => cases he; exact ⟨rfl, rfl, rfl⟩
      | succ j => simp at he
  · simp at he

-- Initialization followed by issue is accepted by these checks without a proxy fence.
-- No assertion about all other execution/safety obligations is made here.
example : ¬ TensorUnsafe X := by
  rintro ⟨i, o, slot, value, ho, _, _⟩
  cases ho
example : ¬ MbarUninit L X := by
  rintro ⟨⟨g, j⟩, m', hu, hni, hn⟩
  simp only [Execution.UsesMbar, Execution.Arrive, Execution.Copy, Execution.AsyncArrive,
    Execution.Commit, Execution.MbInval, Execution.TensorIssue, Execution.ClcIssue,
    Execution.MbInit, Execution.get, X] at hu hni
  split_ifs at hu hni with hg
  · subst hg
    rcases j with _ | _ | j
    · simp at hu hni
      exact hni hu
    · simp [spec] at hu
      subst hu
      exact hn ⟨(0, 0), 1, ⟨0, rfl⟩, published⟩
    · simp at hu
  · simp at hu

-- A remote notification target is a use of its CTA as soon as the instruction is issued.
private def remoteSpec : TensorCopy.Spec := { spec with mbar := ⟨.shared, 1, 64⟩, group := .two }
private def remote : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorIssue 1024 remoteSpec⟩] else [],
  rf := fun _ _ => none }
private theorem remoteUse : SharedUse L remote (.async (0, 0) (.notify .load)) 1 :=
  .inr (.inr (.inr (.inr ⟨(0, 0), .notify .load, rfl,
    .inr (.inr (.inr (.inr (.inr (.inl ⟨1024, remoteSpec, ⟨0, rfl⟩, rfl⟩))))),
    1024, remoteSpec, ⟨0, rfl⟩, rfl, rfl⟩)))
example : SharedUse L remote (.async (0, 0) (.notify .load)) 1 := remoteUse
-- No instruction of the target CTA precedes the issue, so its startup is unproven.
example (K : Kernel) (A : List Assumption) : SharedLifetimeUnsafe L K A remote := by
  refine ⟨_, 1, remoteUse, .inl ⟨by decide, ?_⟩⟩
  rintro ⟨⟨g, j⟩, ev, _, hc, hp, _⟩
  have hg : g = 1 := by simpa [L] using hc
  subst g
  simp [Execution.get, remote] at hp
example : ¬ remote.AsyncPresent (0, 0) (.notify .load) := by
  rintro ⟨o, ho, _⟩
  cases ho

-- The generic-proxy rule applies to a completion record too, including linear bulk.
example (Y : Execution) (init : EvId) (count : Nat)
    (r : MBarrier.Record AsyncCopy.Ref) (hi : Y.MbInit init m count)
    (hb : MBarrier.InitBefore (Y.objects m) (.thread init) r.id)
    (hp : InitPublished L Y init r.id.issuer m)
    (_noProxy : ¬ ProxyBefore L Y init r.id.issuer m) (hv : ∀ v, ¬ Y.MbInval v m) :
    ObjectPublished L Y m r :=
  Or.inr ⟨init, count, hi, hb, hp, fun v h => (hv v h).elim⟩

private def exited : Execution := { X with
  tr := fun g => if g = 0 then
    [⟨0, .mbInit m 1⟩, ⟨1, .tensorIssue 1024 spec⟩, ⟨2, .exit⟩] else [] }
private theorem owner_exited : CtaExited L exited 0 := by
  intro g _ hg
  have he : g = 0 := by simpa [L] using hg
  subst g
  exact ⟨2, rfl⟩

-- Local shared storage also cannot disappear with writes/notification pending: each is a use
-- of the issuer's own CTA, unsafe once that CTA exits before it is performed.
example (K : Kernel) (A : List Assumption) : SharedLifetimeUnsafe L K A exited := by
  refine ⟨.async (0, 1) (.write (.load 0 0 0)), 0,
    .inr (.inr (.inl ⟨(0, 1), 1024, spec, 0, 0, 0, rfl, ⟨1, rfl⟩, by decide, rfl⟩)),
    .inr ⟨owner_exited, ?_⟩⟩
  rintro ⟨⟨o, _, _, ho, _⟩, _⟩
  cases ho
example (K : Kernel) (A : List Assumption) : SharedLifetimeUnsafe L K A exited := by
  refine ⟨.async (0, 1) (.notify .load), 0,
    .inr (.inr (.inr (.inr ⟨(0, 1), .notify .load, rfl,
      .inr (.inr (.inr (.inr (.inr (.inl ⟨1024, spec, ⟨1, rfl⟩, rfl⟩))))),
      1024, spec, ⟨1, rfl⟩, rfl, rfl⟩))),
    .inr ⟨owner_exited, ?_⟩⟩
  rintro ⟨⟨o, ho, _⟩, _⟩
  cases ho

-- A typed fill without a scalar adapter is explicit unsupported content.
example (Y : Execution) (i : EvId) (o : TensorCopy.Observation)
    (slot : TensorTransfer.Slot o.spec.descriptor)
    (ho : Y.tensor i = some o) (hw : o.effects.write slot = some (.filled .oobNan .f16 0)) :
    TensorUnsafe Y :=
  ⟨i, o, slot, .filled .oobNan .f16 0, ho, hw, rfl⟩

end
end PTX.Tests.TensorSafety

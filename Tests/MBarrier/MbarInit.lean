-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

/-! Litmus tests for ERR-MBAR-UNINITIALIZED and the mbarrier storage clause of
ERR-UNALLOCATED-ACCESS (one CTA of one thread, and a cluster of two CTAs for cluster launch
control).

`arriveOnly`: a `cp.async.mbarrier.arrive` names an mbarrier that no instruction initializes. Its
issue is checked like every other mbarrier operand, and the execution is unsafe
(`arriveOnly_uninit`).

`initArrive`: the thread initializes the mbarrier and then issues the same instruction. The
initialization happens before the issue, and the initialization itself is not checked
(`initArrive_ok`).

`pollOnly`: a poll of an uninitialized mbarrier is unsafe (`pollOnly_uninit`).

Accepted cases: the mbarrier storage clause accepts `initArrive` when only the eight bytes of its
mbarrier are allocated (`initArrive_mbar_alloc`), and with every byte allocated neither mbarrier
clause of `Unsafe` rejects `initArrive` (`initArrive_mbar_ok`), while `arriveOnly` is `Unsafe`
through `MbarUninit` alone (`arriveOnly_alloc`, `arriveOnly_unsafe`).

`clcOnly`: a CLC request whose response mbarrier no instruction initializes is unsafe
(`clcOnly_uninit`), and with no shared memory allocated its response mbarrier lies in
unallocated memory (`clcOnly_unalloc`). -/

namespace PTX.Tests.MbarInit
open PTX

private def L : Launch := { grid := 1, block := 1, params := fun _ => none }
private def m : Loc := ⟨.shared, 0, 64⟩

private def arriveOnly : Execution :=
  { tr := fun g => if g = 0 then [⟨0, .asyncArrive m false⟩] else []
    rf := fun _ _ => none }

private def initArrive : Execution :=
  { tr := fun g => if g = 0 then [⟨0, .mbInit m 1⟩, ⟨1, .asyncArrive m false⟩] else []
    rf := fun _ _ => none }

private def pollOnly : Execution :=
  { tr := fun g => if g = 0 then [⟨0, .wait m 0 false true .cta⟩] else []
    rf := fun _ _ => none }

theorem arriveOnly_uninit : MbarUninit L arriveOnly := by
  refine ⟨(0, 0), m, .inr (.inr (.inl ⟨false, ⟨0, rfl⟩⟩)), ?_, ?_⟩
  · rintro count ⟨pc, h⟩
    simp [Execution.get, arriveOnly] at h
  · rintro ⟨⟨g, j⟩, count, ⟨pc, h⟩, -⟩
    simp only [Execution.get, arriveOnly] at h
    split_ifs at h <;> rcases j with _ | j <;> simp at h

theorem pollOnly_uninit : MbarUninit L pollOnly := by
  refine ⟨(0, 0), m, .inr (.inr (.inr (.inr (.inl ⟨0, 0, false, true, .cta, rfl⟩)))), ?_, ?_⟩
  · rintro count ⟨pc, h⟩
    simp [Execution.get, pollOnly] at h
  · rintro ⟨⟨g, j⟩, count, ⟨pc, h⟩, -⟩
    simp only [Execution.get, pollOnly] at h
    split_ifs at h <;> rcases j with _ | j <;> simp at h

private theorem published : InitPublished L initArrive (0, 0) (0, 1) m := by
  apply Or.inl
  apply Relation.TransGen.single
  exact Or.inl ⟨rfl, by decide, by decide⟩

theorem initArrive_ok : ¬ MbarUninit L initArrive := by
  rintro ⟨⟨g, j⟩, m', hu, hni, hn⟩
  simp only [Execution.UsesMbar, Execution.Arrive, Execution.Copy, Execution.AsyncArrive,
    Execution.Commit, Execution.MbInval, Execution.TensorIssue, Execution.ClcIssue,
    Execution.MbInit, Execution.get, initArrive] at hu hni
  split_ifs at hu hni with hg
  · subst hg
    rcases j with _ | _ | j
    · simp at hu hni
      exact hni hu
    · simp at hu
      subst hu
      exact hn ⟨(0, 0), 1, ⟨0, rfl⟩, published⟩
    · simp at hu
  · simp at hu

/-! ## Allocated and published mbarriers -/

/-- The launch memory in which exactly the eight bytes of `m` are allocated. -/
private def mbarOnly : Mem0 := fun l => if m.InRange 8 l then some none else none

/-- Every mbarrier `initArrive` names is `m`. -/
private theorem initArrive_uses {e : EvId} {m' : Loc} (h : initArrive.UsesMbar e m') : m' = m := by
  obtain ⟨g, j⟩ := e
  simp only [Execution.UsesMbar, Execution.Arrive, Execution.Copy, Execution.AsyncArrive,
    Execution.Commit, Execution.MbInval, Execution.TensorIssue, Execution.ClcIssue,
    Execution.MbInit, Execution.get, initArrive] at h
  split_ifs at h with hg
  · rcases j with _ | _ | j <;> simp at h <;> exact h.symm
  · simp at h

/-- The mbarrier storage clause of ERR-UNALLOCATED-ACCESS accepts `initArrive` when the eight
bytes of `m` are allocated, and no other byte is. -/
theorem initArrive_mbar_alloc :
    ¬ ∃ e m' l, initArrive.UsesMbar e m' ∧ Acc.Covers { loc := m', size := 8 } l ∧
      mbarOnly l = none := by
  rintro ⟨e, m', l, hu, hc, hn⟩
  rw [initArrive_uses hu] at hc
  have hc : m.InRange 8 l := hc
  simp [mbarOnly, hc] at hn

/-- With every byte allocated, `initArrive` and `arriveOnly` are not `Unalloc`. -/
theorem initArrive_alloc : ¬ Unalloc (fun _ => some none) initArrive := by
  simp [Unalloc]
theorem arriveOnly_alloc : ¬ Unalloc (fun _ => some none) arriveOnly := by
  simp [Unalloc]

/-- The two mbarrier clauses of `Unsafe` (ERR-UNSAFE) accept `initArrive`, whose mbarrier is
allocated and whose initialization is published to the arrival; with the same allocation,
`arriveOnly` is `Unsafe` through `MbarUninit` alone. -/
theorem initArrive_mbar_ok :
    ¬ Unalloc (fun _ => some none) initArrive ∧ ¬ MbarUninit L initArrive :=
  ⟨initArrive_alloc, initArrive_ok⟩
theorem arriveOnly_unsafe (K : Kernel) (A : List Assumption) :
    Unsafe L K A (fun _ => some none) arriveOnly := by
  unfold Unsafe
  iterate 27 right
  exact arriveOnly_uninit

/-! ## Cluster launch control -/

private def Lc : Launch :=
  { grid := 2, block := 1, params := fun _ => none, clusterSize := 2 }
private def clc : Clc.Spec := ⟨⟨.shared, 0, 0⟩, m, true⟩
private def clcOnly : Execution :=
  { tr := fun g => if g = 0 then [⟨0, .clcIssue clc [0, 1]⟩] else []
    rf := fun _ _ => none }

theorem clcOnly_uninit : MbarUninit Lc clcOnly := by
  refine ⟨(0, 0), { clc.mbar with cta := 1 },
    Execution.UsesMbar.of_clc (c := 1) ⟨0, rfl⟩ (by simp), ?_, ?_⟩
  · rintro count ⟨pc, h⟩
    simp [Execution.get, clcOnly] at h
  · rintro ⟨⟨g, j⟩, count, ⟨pc, h⟩, -⟩
    simp only [Execution.get, clcOnly] at h
    split_ifs at h <;> rcases j with _ | j <;> simp at h

theorem clcOnly_unalloc : Unalloc (fun _ => none) clcOnly :=
  .inr ⟨(0, 0), { clc.mbar with cta := 1 }, { clc.mbar with cta := 1 },
    Execution.UsesMbar.of_clc (c := 1) ⟨0, rfl⟩ (by simp),
    by simp [Acc.Covers, Loc.InRange], rfl⟩


end PTX.Tests.MbarInit

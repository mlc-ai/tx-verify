-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcDataAddress
public meta import Lean.Elab.Tactic.Omega
public import Core.Assembly.Execution
public import Mathlib.Tactic.Tauto
public import Core.Assembly.Correctness
public import Lemmas.Execution.NoTma

@[expose] public section

section
namespace PTX

/-- Lane field zero is supported by every warp position, for every shape whose half-split offset
is supported (EXT-TMEM-LANE-FIELD). -/
theorem tcDataAddressOk_of_row_zero {L : Launch} {g address : Nat} {s : TcShape}
    (hs : s.splitOk address = true) (h : address / 2^16 = 0) :
    tcDataAddressOk L g s address = true := by
  unfold tcDataAddressOk tmemLaneFieldOk
  rw [h, hs]
  cases s with
  | packed16 inner =>
    cases inner <;> simp_all [TcShape.singleAccess, TcShape.lanes, TcShape.splitOk]
  | _ => simp [TcShape.lanes]

/-- The warp's own first lane is supported, for every shape whose half-split offset is
supported. -/
theorem tcDataAddressOk_of_lane_base {L : Launch} {g address : Nat} {s : TcShape}
    (hs : s.splitOk address = true) (h : address / 2^16 = laneBase L g) :
    tcDataAddressOk L g s address = true := by
  unfold tcDataAddressOk tmemLaneFieldOk
  rw [h, hs]
  cases s with
  | packed16 inner =>
    cases inner <;> simp_all [TcShape.singleAccess, TcShape.lanes, TcShape.splitOk]
  | _ => simp [TcShape.lanes]

/-- For an access of at least one lane by a warp other than warp 0 of its warpgroup, the offset
and the absolute reading of the lane field exclude each other (THREAD-TC-DATA-ADDRESS). -/
theorem tmemLaneField_disjoint {L : Launch} {g field n : Nat} (hn : 0 < n)
    (hb : 32 ≤ laneBase L g) : ¬ (field + n ≤ 32 ∧ laneBase L g ≤ field) := by
  omega

end PTX
end

section
namespace PTX
noncomputable section

/-- A commit whose target mbarrier is never initialized leaves the mbarrier uninitialized
(ERR-MBAR-UNINITIALIZED; the commit-issue clause of `TcCommitUnsafe` no longer covers it). -/
theorem tcCommit_uninitialized_uninit {L : Launch} {X : Execution}
    {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some m)
    (hn : ∀ init count, ¬ X.MbInit init m count) : MbarUninit L X := by
  refine ⟨i, m, ?_, fun count => hn _ count, ?_⟩
  · exact .inr (.inr (.inr (.inl ⟨s, rank, hi, ht⟩)))
  · rintro ⟨j, count, hinit, -⟩
    exact hn j count hinit

/-- A commit's arrival at rank `rank` uses the target mbarrier's CTA, notified or not. -/
theorem tcCommit_use {L : Launch} {X : Execution} {i : EvId}
    {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some m) :
    SharedUse L X (.async i (.tcNotify rank)) m.cta :=
  .inr (.inr (.inr (.inr ⟨i, .tcNotify rank, rfl,
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (⟨s, rank, m, hi, ht, rfl⟩))))))),
    ⟨s, m, hi, ht, rfl⟩⟩)))

theorem tcCommit_pending_at_exit_unsafe {L : Launch} {K : Kernel} {A : List Assumption}
    {X : Execution}
    {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {m : Loc}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some m)
    (he : CtaExited L X m.cta) (hn : rank ∉ X.tcNotified i) :
    SharedLifetimeUnsafe L K A X :=
  ⟨_, _, tcCommit_use hi ht, .inr ⟨he, fun h => hn h.1⟩⟩

end
end PTX
end

section
namespace PTX

/-- A source without asynchronous instructions has no qualified tcgen05 operation. -/
theorem Op.tcGroup_eq_none_of_not_isTma {op : Op} (h : op.isTma = false) :
    op.tcGroup = none := by
  cases op <;> first | rfl | simp [Op.isTma, Op.isLocal] at h

/-- Reuse the checked absence of asynchronous instructions instead of recomputing
the tcgen05 group check over a long concrete source listing. -/
theorem Kernel.NoTma.tcGroupUniform {K : Kernel} (h : K.NoTma) :
    K.TcGroupUniform := by
  have hnone : ∀ ins ∈ K.code, ins.op.tcGroup = none := by
    intro ins hins
    have hi := List.all_eq_true.mp h ins hins
    apply Op.tcGroup_eq_none_of_not_isTma
    simpa using hi
  have h1 : (K.code.any fun ins => ins.op.tcGroup == some 1) = false := by
    apply List.any_eq_false.mpr
    intro ins hins
    simp [hnone ins hins]
  simp [Kernel.TcGroupUniform, Kernel.tcGroupUniform, h1]

/-- The executable check excludes any two differently qualified source instructions,
without reference to guards, traces, scheduling or reachability. -/
theorem Kernel.TcGroupUniform.no_mixed {K : Kernel} (h : K.TcGroupUniform)
    {a b : Instr} (ha : a ∈ K.code) (hb : b ∈ K.code)
    (hga : a.op.tcGroup = some 1) (hgb : b.op.tcGroup = some 2) : False := by
  have h1 : (K.code.any fun ins => ins.op.tcGroup == some 1) = true :=
    List.any_eq_true.mpr ⟨a, ha, by simp [hga]⟩
  have h2 : (K.code.any fun ins => ins.op.tcGroup == some 2) = true :=
    List.any_eq_true.mpr ⟨b, hb, by simp [hgb]⟩
  simp [Kernel.TcGroupUniform, Kernel.tcGroupUniform, h1, h2] at h

/-- A correct kernel cannot evade the static rule by avoiding a mixed instruction. -/
theorem Correct.tcGroupUniform {K : Kernel} {A : List Assumption} {L : Launch}
    {mem0 : Mem0} {post : FinalMem → Prop} (h : Correct K A L mem0 post) (hv : L.Valid K) :
    K.TcGroupUniform := (h.safe hv).1

end PTX
end

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Worker
public import Kernels.InklingRelDecode.Proof.Bound.Loader
public import Kernels.InklingRelDecode.Proof.Bound.Mma
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The rank of the worker thread's machine

A worker thread (`WComp.code`, warps 4 to 7) goes through its prologue to the dispatch loop's head
and then around the loop: `setmaxnreg.inc`, `barrier.sync 1`, the load of the role byte and the
role the byte names, which ends at the loop's head again. The rank of a state is its machine's
rank (`Bound/Worker.lean`, `Loader.lean`, `Mma.lean`) shifted above the loop's: a role's states
rank at least `4` (the loop's head is `3`), so a role's last event, which returns to the head,
lowers the rank by its count.

The one event at which the rank rises is the load of the role byte (`WComp.next` at
`Worker.Site.ldRole`, which starts one of the four roles): it may raise the rank by `budget`, the
largest rank of a role's first state. A run's counted events are then at most its initial rank
plus `budget` for each dispatch. The number of dispatches (the loads of the role byte) is not
bounded by the machine: it is the protocol layer's (`DispatchBound` in `Bound/Goal.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.WComp
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section
set_option maxRecDepth 100000

/-- The rank of a worker thread's state. -/
def rank : WComp.WSt → Nat
  | .worker w => Worker.rank w
  | .idle d => Worker.idleRank d.site + 4
  | .loader d _ => Loader.rank d + 4
  | .mma d _ => Mma.rank d + 4
  | .exit x => match x.site with
    | .bar => 1
    | .ret => 0

/-- The most the load of the role byte raises the rank: the rank of the first state of a role. -/
def budget : Nat := Loader.readTop + Mma.readTop + 16

/-- The raise at an event: the budget at the load of the role byte. -/
def extra (e : Event) : Nat := if e.pc = Worker.Site.ldRole.pc then budget else 0

/-- The first state's rank. -/
theorem rank_init (L : Launch) (g : Nat) (Q : Params) : rank (WComp.code L g Q).init = 7 := rfl

/-- **A role's first state is ranked within the budget.** -/
theorem roleStart_rank {L : Launch} {g : Nat} {P : Loader.Pro} {s : Worker.Site}
    {d' : WComp.WSt} (h : WComp.roleStart L g P s = some (some d')) : rank d' ≤ budget := by
  cases s <;> simp only [WComp.roleStart] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [rank, Loader.rank_start, Mma.rank_start, Worker.idleRank, Worker.Idle.D.start,
      Worker.rank, Worker.siteRank, budget] <;> omega

/-- **Every step of the worker thread's machine lowers the rank by its count**, except that the
load of the role byte may raise it by `budget`. -/
theorem rank_step {L : Launch} {g : Nat} {d d' : WComp.WSt} {e : Event}
    (hI : WComp.Inv L g d) (hpc : e.pc = WComp.pc d)
    (h : WComp.next L g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d + extra e := by
  have hc := counts_le e
  cases d with
  | worker w =>
    obtain ⟨s, P⟩ := w
    cases s
    case ldRole =>
      simp only [WComp.next, WComp.dispatch] at h
      have hx : extra e = budget := by
        simp only [extra, hpc, WComp.pc, ite_true]
      have hr : rank (WComp.WSt.worker ⟨.ldRole, P⟩) = 1 := rfl
      rw [hx, hr]
      split at h
      · rename_i d1 _
        have := roleStart_rank h
        omega
      · simp at h
      · simp at h
    all_goals
      simp only [WComp.next] at h
      obtain ⟨a, ha, rfl⟩ := map_inv h
      have := Worker.rank_step (by simp) ha
      simp only [rank]
      omega
  | idle d =>
    obtain ⟨s, P⟩ := d
    cases s
    case inc =>
      simp only [WComp.next, Option.some.injEq] at h
      subst h
      simp only [rank, Worker.rank, Worker.siteRank, Worker.idleRank]
      omega
    all_goals
      simp only [WComp.next] at h
      obtain ⟨a, ha, rfl⟩ := map_inv h
      have := Worker.idle_step ha
      simp only [rank, Worker.idleRank] at this ⊢
      omega
  | loader d P =>
    have hL := hI.1
    obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
    by_cases hs : s = .setMaxInc
    · subst hs
      simp only [WComp.next, Option.some.injEq] at h
      subst h
      simp only [rank, Loader.rank, Worker.rank, Worker.siteRank]
      omega
    · simp only [WComp.next] at h
      obtain ⟨a, ha, rfl⟩ := map_inv h
      have := Loader.rank_step hL hs ha
      simp only [rank] at this ⊢
      omega
  | mma d P =>
    have hM := hI.1
    obtain ⟨s, i, n, tm, pro⟩ := d
    by_cases hs : s = .setMaxRegInc
    · subst hs
      simp only [WComp.next, Option.some.injEq] at h
      subst h
      simp only [rank, Mma.rank, Worker.rank, Worker.siteRank]
      omega
    · simp only [WComp.next] at h
      obtain ⟨a, ha, rfl⟩ := map_inv h
      have := Mma.rank_step hM hs ha
      simp only [rank] at this ⊢
      omega
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s
    · simp only [WComp.next, Option.some.injEq] at h
      subst h
      simp only [rank]
      omega
    · simp [WComp.next] at h

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.WComp

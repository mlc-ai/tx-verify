-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Time
public import Kernels.InklingRelDecode.Proof.Mma.Commit
public import Kernels.InklingRelDecode.Proof.Mma.Ref
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow

inductive LoopIssue where | score | empty | done

def LoopIssue.commit : LoopIssue → CommitSite
  | .score => .qk | .empty => .empty | .done => .done

def LoopIssue.iter (op : LoopIssue) (r : Nat) := match op with
  | .score => r | .empty | .done => r+1

def LoopIssue.slot (op : LoopIssue) (r : Nat) :=
  slotTime (op.iter r)+op.commit.site.position

def LoopIssue.before (op : LoopIssue) (r : Nat) (d : D) :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => True
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc | .dispatch | .qkSkip | .pvSkip =>
    False
  | s => d.i<op.iter r ∨ (d.i=op.iter r ∧ s.position≤op.commit.site.position)

private theorem pos_le (s : Site) : s.position≤28 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)


theorem LoopIssue.cut {op : LoopIssue} {r d} (h : op.before r d) :
    time d≤op.slot r ∧ (time d=op.slot r → d.site=op.commit.site ∧ d.i=op.iter r) := by
  have unique (s : Site) : s.position=op.commit.site.position → s=op.commit.site := by
    cases op <;> cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  obtain ⟨s,i,v⟩ := d
  have ds := pos_le s
  have ts := pos_le op.commit.site
  rw [slot,slotTime,Lib.Slots.mma,Lib.Slots.frame,Lib.Slots.stride]
  cases s <;> simp only [before,time,slotTime,Lib.Slots.mma,Lib.Slots.frame,Lib.Slots.stride,
    Lib.Slots.enter,Lib.Slots.reuse] at h ⊢
  all_goals refine ⟨by omega,fun eq => ?_⟩
  all_goals first | omega | exact ⟨unique _ (by omega),by omega⟩

private theorem iter_before {op : LoopIssue} {r i v s} (earlier : i<op.iter r) (lim : r<low v) :
    op.before r (iterNext ⟨s,i,v⟩) := by
  by_cases eq : i=low v <;> by_cases test : i+1<low v <;> cases op <;>
    simp [iterNext,D.limit,eq,test,LoopIssue.before,LoopIssue.commit,CommitSite.site,
      LoopIssue.iter,Site.position] at earlier ⊢ <;> omega

private theorem after_before {op : LoopIssue} {r i v}
    (h : op.before r ⟨.qkCommit,i,v⟩) (lim : r<low v)
    (miss : .qkCommit=op.commit.site → i≠op.iter r) :
    op.before r (afterQk ⟨.qkCommit,i,v⟩) := by
  cases op <;> simp only [LoopIssue.before,LoopIssue.commit,CommitSite.site,LoopIssue.iter,
    Site.position,forall_const,reduceCtorEq,forall_false] at h miss
  all_goals unfold afterQk; split <;> dsimp only at *
  all_goals first
    | (apply iter_before (lim := lim); change _<_+1; omega)
    | (apply iter_before (lim := lim); change _<r; omega)
    | (simp only [LoopIssue.before,LoopIssue.commit,CommitSite.site,LoopIssue.iter,Site.position];
       omega)


theorem LoopIssue.before_next {L g d e dn r} {op : LoopIssue} (step : next L g d e=some (some dn))
    (h : op.before r d) (limit : d.site.hasCount → r<d.limit ∧ d.limit≤2147483646)
    (won : ∀ m inst ld, e.kind=.elect m inst ld → laneOf L g=ld)
    (recv : ∀ md a b c v ok, e.kind=.shfl md a b c v ok → low v=7)
    (miss : d.site=op.commit.site → d.i≠op.iter r) (inv : Inv d) :
    op.before r dn := by
  obtain ⟨s,i,v⟩ := d
  change s=op.commit.site → i≠op.iter r at miss
  cases s <;> try contradiction
  case setMaxReg => cases step; trivial
  case ldNum =>
    simp only [next] at step
    split at step <;> try contradiction
    rename_i bs _
    cases hv : (rebuild 3 bs).toOption <;> simp [hv] at step
    subst dn; trivial
  case bar0 =>
    obtain ⟨pos,cap⟩ := limit rfl
    cases step
    have n : ¬(low v=0 ∨ 2147483646<low v) := by change r<low v at pos; change low v≤_ at cap; omega
    change op.before r ⟨startSite (low v),i,v⟩
    simp only [startSite,n,ite_false]
    change i=0 at inv
    cases op <;> simp [before,iter,commit,CommitSite.site,Site.position,inv]; omega
  case qkCommit =>
    cases step
    exact after_before h (limit rfl).1 miss
  case pvCommit2 =>
    cases step
    apply iter_before (lim := (limit rfl).1)
    cases op <;> simp [before,iter,commit,CommitSite.site,Site.position] at h miss ⊢ <;> omega
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals try contradiction
  all_goals try (rename_i m inst ld kd other; exact False.elim (other (won _ _ _ kd)))
  all_goals try (rename_i _ _ _ _ v' _ kd other; exact False.elim (other (recv _ _ _ _ _ _ kd)))
  all_goals cases step
  all_goals try assumption
  all_goals try (rename_i p; fin_cases p)
  all_goals cases op <;> simp only [before,iter,commit,CommitSite.site,issueNext,
    Site.position,Fin.coe_ofNat_eq_mod,Nat.reduceMod,Nat.reduceAdd,
    Nat.reduceLT,↓reduceDIte] at h miss ⊢
  all_goals first | omega | (have ne := miss trivial; omega)

end PTX.Kernels.InklingRelDecode.Proof.Mma

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Ledger
public import Kernels.InklingRelDecode.Proof.Lib.CollectiveAt
public import Lemmas.Flow.PollRounds
public import Lemmas.Kernel.Progress.Warp
import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow

/-- Elections still owed for the current successful empty-ring poll. -/
def owed : Site → Nat
  | .readyBar | .arrive | .page false => 4
  | .page true => 2
  | .warpBar p | .elect p => 4-p.val
  | .copy p _ => 3-p.val
  | _ => 0

theorem finish_owed (d : D) (p : Fin 4) : owed (finishPair d p).site = 3-p.val := by
  fin_cases p <;> try rfl
  change owed (if _ then .endBar else .poll) = 0
  split <;> rfl

theorem canElect_off (s : Site) (h : ∀ p, s≠.elect p) : Lib.canElect s.pc=false := by
  cases s <;> first | decide +kernel | (rename_i p; exact (h p rfl).elim) |
    (rename_i p; revert p; decide +kernel) | (rename_i p b; revert p b; decide +kernel)

theorem owed_next {L g d dn ev} (src : Lib.CollectiveAt d.site.pc ev)
    (hn : next L g d ev=some (some dn)) :
    (isElectEv ev).toNat + owed dn.site = owed d.site + 4*(okPollAt 2374 ev).toNat := by
  obtain ⟨s,i,n,a,b⟩ := d
  have pc : ev.pc=s.pc := src.pc_eq
  by_cases poll : s=.poll
  · subst s
    have noVote := src.election (by decide +kernel : Lib.canElect 2374=false)
    obtain ⟨p,k⟩ := ev
    cases pc
    cases k with
    | wait l q ok ac sc => cases ok <;> cases hn <;> rfl
    | _ => cases hn
  have off : okPollAt 2374 ev=false := by
    have ne : s.pc≠2374 := by
      cases s <;> try contradiction
      all_goals first | decide | (rename_i j; fin_cases j <;> decide) |
        (rename_i j b; fin_cases j <;> cases b <;> decide)
    cases ev with
    | mk p k =>
      cases k <;> try rfl
      rename_i ok _ _
      cases ok <;> simp_all [okPollAt]
  rw [off]
  by_cases el : ∃ j, s=.elect j
  · obtain ⟨j,rfl⟩ := el
    obtain ⟨p,k⟩ := ev
    cases k with
    | elect mask inst l =>
      simp only [next] at hn
      split at hn <;> cases hn
      · change 1+(3-j.val)=4-j.val+0; omega
      · rw [finish_owed]; change 1+(3-j.val)=4-j.val+0; omega
    | _ => cases hn
  have vote := src.election (canElect_off s fun j eq => el ⟨j,eq⟩)
  rw [vote]
  simp only [Bool.toNat_false,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
  cases s with
  | poll => contradiction
  | elect j => exact (el ⟨j,rfl⟩).elim
  | first | second => obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn; rfl
  | page u => cases u <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn <;> rfl
  | copy j u => cases u <;> cases hn; · rfl
                exact finish_owed _ j
  | beginBar | readyBar => simp only [next] at hn; split at hn <;> cases hn <;> rfl
  | dispatch => cases hn
  | _ => cases hn; rfl

/-- The sites at a warp collective: the barriers and the elections. -/
def Site.coll : Site → Bool
  | .readyBar | .warpBar _ | .elect _ => true
  | _ => false

/-- Warp collectives still owed for the current successful empty-ring poll. -/
def remain : Site → Nat
  | .readyBar => 9
  | .elect p => 7 - 2 * p.val
  | s => 2 * owed s

theorem remain_next {L g d dn ev} (src : Lib.CollectiveAt d.site.pc ev)
    (hc : Sched.isWarpColl ev = d.site.coll) (hn : next L g d ev = some (some dn)) :
    (Sched.isWarpColl ev).toNat + remain dn.site =
      remain d.site + 9 * (okPollAt 2374 ev).toNat := by
  have o := owed_next src hn
  rw [hc]
  obtain ⟨s, i, n, a, b⟩ := d
  have quiet : (∀ p, s ≠ .elect p) → (isElectEv ev).toNat = 0 := fun h => by
    rw [src.election (canElect_off s h)]; rfl
  have fin (j : Fin 4) : remain (finishPair ⟨s, i, n, a, b⟩ j).site = 2 * (3 - j.val) := by
    fin_cases j <;> try rfl
    change remain (if _ then .endBar else .poll) = _
    split <;> rfl
  cases s with
  | poll =>
    obtain ⟨p, k⟩ := ev
    cases src.pc_eq
    cases k with
    | wait l q ok ac sc => cases ok <;> cases hn <;> rfl
    | _ => cases hn
  | elect j =>
    obtain ⟨p, k⟩ := ev
    cases k with
    | elect mask inst l =>
      simp only [next] at hn
      simp only [isElectEv, Bool.toNat_true] at o
      have := j.isLt
      split at hn <;> cases hn
      · simp only [Site.coll, remain, owed, Bool.toNat_true] at o ⊢
        omega
      · rw [fin, finish_owed] at *
        simp only [Site.coll, remain, owed, Bool.toNat_true] at o ⊢
        omega
    | _ => cases hn
  | dispatch => cases hn
  | first | second =>
    rw [quiet fun p h => by cases h] at o
    obtain ⟨_, _, _, _, _, rfl⟩ := read_next hn
    simp only [Site.coll, remain, owed, Bool.toNat_false] at o ⊢
    omega
  | page u =>
    rw [quiet fun p h => by cases h] at o
    cases u <;> obtain ⟨_, _, _, _, _, rfl⟩ := read_next hn <;>
      simp only [Site.coll, remain, owed, Bool.toNat_false] at o ⊢ <;> omega
  | beginBar | readyBar =>
    rw [quiet fun p h => by cases h] at o
    simp only [next] at hn
    split at hn <;> cases hn <;>
      simp only [Site.coll, remain, owed, Bool.toNat_true, Bool.toNat_false] at o ⊢ <;> omega
  | copy j u =>
    rw [quiet fun p h => by cases h] at o
    have := j.isLt
    cases u
    · cases hn
      simp only [Site.coll, remain, owed, Bool.toNat_false] at o ⊢
      omega
    · cases hn
      rw [fin, finish_owed] at *
      simp only [Site.coll, remain, owed, Bool.toNat_false] at o ⊢
      omega
  | warpBar j =>
    rw [quiet fun p h => by cases h] at o
    cases hn
    have := j.isLt
    simp only [Site.coll, remain, owed, Bool.toNat_true] at o ⊢
    omega
  | _ =>
    rw [quiet fun p h => by cases h] at o
    cases hn
    simp only [Site.coll, remain, owed, Bool.toNat_false] at o ⊢
    omega

end PTX.Kernels.InklingRelDecode.Proof.Loader

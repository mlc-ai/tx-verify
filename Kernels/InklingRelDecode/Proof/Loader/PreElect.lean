-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Time
public import Kernels.InklingRelDecode.Proof.Loader.ElectBalance
public import Kernels.InklingRelDecode.Proof.Loader.PollCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow

/-- Before any election an active Loader is no later than its first election.
A split with no recurrent block may already have finished at this point. -/
theorem pre_elect_time {lo hi : Nat} {d : D} (work : lo<hi) (limit : hi<2^31)
    (ref : Ref lo hi d) (bal : owed d.site=4*polls lo hi d) :
    time d ≤ Lib.Slots.frame lo + 5 ∧ d.site ≠ .inc := by
  obtain ⟨s,i,n,a,b⟩ := d
  have low (loop : s.inLoop) : lo ≤ (bits i).toNat := by
    obtain ⟨j,start,stop,word,_⟩ := ref_loop ref loop
    change i = Proof.b32 j at word
    rw [word]
    rwa [bits_b32 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  cases s
  case' page u => cases u
  case' warpBar p => fin_cases p
  case' elect p => fin_cases p
  case' copy p u => fin_cases p <;> cases u
  all_goals simp only [owed,polls] at bal
  all_goals try omega
  all_goals constructor
  all_goals try solve | intro h; cases h
  all_goals try solve | simp [time,Lib.Slots.frame,Lib.Slots.enter,Lib.Slots.reuse]; omega
  all_goals have le := low rfl
  all_goals have eq : (bits i).toNat=lo := by omega
  all_goals simp [time,slotTime,eq,Site.position]

private theorem pair_not_dispatch (d : D) (p : Fin 4) : (finishPair d p).site ≠ .dispatch := by
  fin_cases p <;> try solve | intro h; cases h
  change (if _ then Site.endBar else .poll) ≠ _
  split <;> exact nofun

theorem before_dispatch {L g d sn e} (step : next L g d e=some (some sn))
    (back : sn.site=.dispatch) : d.site=.inc := by
  obtain ⟨s,i,n,a,b⟩ := d
  cases s
  case inc => rfl
  case first | second => obtain ⟨_,_,_,_,_,rfl⟩ := read_next step; cases back
  case page u => cases u <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next step <;> cases back
  case copy p u =>
    cases u <;> cases step
    · cases back
    · exact (pair_not_dispatch _ p back).elim
  case elect p =>
    simp only [next] at step
    split at step <;> try contradiction
    split at step <;> cases step
    · cases back
    · exact (pair_not_dispatch _ p back).elim
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals cases back

end PTX.Kernels.InklingRelDecode.Proof.Loader

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.LoopRoute

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow

private theorem to_pre {e t d i v j} (hi : Inv e t d) (zero : i=0) (on : preEnabled e t) :
    Inv e t ⟨.pre j,i,v⟩ := by
  subst i
  exact ⟨hi.entry,hi.thread,Nat.zero_le _,fun _ => rfl,fun _ _ => ⟨rfl,on⟩,
    fun _ => nofun,nofun,fun _ _ _ h => (h j rfl).elim⟩

private theorem to_loop {e t d i v s} (hi : Inv e t d) (lt : i<e.limit)
    (normal : SiteBody s ∨ (∃ j, s=.nxt j ∧ nextEnabled e t i) ∨ (s=.arrive ∧ t%128=0)) :
    Inv e t ⟨s,i,v⟩ := by
  rcases normal with hs|⟨j,rfl,on⟩|⟨rfl,lead⟩
  · refine ⟨hi.entry,hi.thread,lt.le,?_,?_,?_,?_,fun _ _ _ _ => lt⟩
    · rintro (rfl|rfl) <;> cases hs
    · rintro _ rfl; cases hs
    · rintro _ rfl; cases hs
    · rintro rfl; cases hs
  · exact ⟨hi.entry,hi.thread,lt.le,(by rintro (h|h) <;> cases h),
      fun _ => nofun,fun _ _ => on,nofun,fun _ _ _ _ => lt⟩
  · exact ⟨hi.entry,hi.thread,lt.le,(by rintro (h|h) <;> cases h),
      fun _ => nofun,fun _ => nofun,fun _ => lead,fun _ _ _ _ => lt⟩

theorem inv_next {e L g d dn ev} (hi : Inv e (g%L.block) d)
    (move : next e L g d ev=some (some dn)) : Inv e (g%L.block) dn := by
  obtain ⟨s,i,v⟩ := d
  cases s
  case setMaxReg =>
    cases move
    exact ⟨hi.entry,hi.thread,hi.bound,fun _ => hi.init (.inl rfl),fun _ => nofun,
      fun _ => nofun,nofun,fun _ _ h _ => (h rfl).elim⟩
  case bar0 =>
    simp only [next] at move
    split at move <;> cases move
    · exact to_pre hi (hi.init (.inr rfl)) (by assumption)
    · exact loop_inv hi.entry hi.thread hi.bound
  case pre j =>
    simp only [next] at move
    split at move <;> cases move
    · exact to_pre hi (hi.pre _ rfl).1 (hi.pre _ rfl).2
    · exact loop_inv hi.entry hi.thread hi.bound
  case epilogue => cases move
  all_goals have lt := hi.loop nofun nofun nofun (fun _ => nofun)
  all_goals simp only [next] at move
  all_goals repeat' split at move
  all_goals cases move
  all_goals first | exact body_inv hi rfl rfl | exact to_loop hi lt (.inl rfl) |
    exact to_loop hi lt (.inr (.inl ⟨_,rfl,hi.nxt _ rfl⟩)) |
    exact to_loop hi lt (.inr (.inr ⟨rfl,by assumption⟩)) |
    exact loop_inv hi.entry hi.thread (Nat.succ_le_of_lt lt)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CompletedRound
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundBoundary

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

noncomputable section

/-- The statistics computed from the observed operands of a round are carried into v. -/
def RoundCarry (p : Params) (L : Launch) (X : Execution) (g u : Nat) (v : V) : Prop :=
  let rv := roundSnapshot p L X g u
  v.mf = finE (Data.maximum p L g rv.2 rv.1) ∧ v.mr = (Data.maximum p L g rv.2 rv.1).toReal ∧
    v.rs = Data.sumAfter p L g rv.2 rv.1

/-- The sequence of all completed rounds before a boundary with credit n. -/
structure RoundHistory (p : Params) (L : Launch) (X : Execution) (g : Nat) (t : Tile)
    (S : Nat → Nat → ℝ) (n : Nat) (v : V) : Prop where
  agree : ∀ u < n, RoundAgrees p L X g t S u
  carry : ∀ u, u+1 < n → RoundCarry p L X g u (roundSnapshot p L X g (u+1)).2
  last : ∀ u, n = u+1 → RoundCarry p L X g u v

theorem soft_row_history {p L m X g t S} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (reads : ScoreReads L X g S)
    (loads : ∀ {id a vs}, X.TLd id a vs .s32x32b → F32s vs)
    (ht : tileOf p L (g/L.block) = some t) (hv : t.Valid p (Prologue.warpIndex L g/4) (rowIx L g)) :
    ∀ n ≤ t.n, ∀ {i d}, i ≤ (X.tr g).length → softState p L X g i = some d →
      boundary d.site = true → Tm.sPolls L X g (Prologue.warpIndex L g/4) i = n →
      RoundHistory p L X g t S n d.v := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ _ _ _
    exact ⟨fun _ h => (Nat.not_lt_zero _ h).elim,fun _ h => (Nat.not_lt_zero _ h).elim,
      fun _ h => (Nat.zero_ne_add_one _ h).elim⟩
  | succ n ih =>
    intro bound i d hi state edge credit
    obtain ⟨j,hj,r,v,k,acc,closing,poll,stats⟩ :=
      soft_boundary_previous hp hX hw hi state edge credit
    obtain ⟨snap,verified⟩ := completed_round hp hX hf hw reads loads ht hv (by omega)
      (by omega) closing poll
    obtain ⟨j',_,e,⟨s,x,k',acc'⟩,out,he,st,site,hn,left,view,count⟩ :=
      soft_round_visit hp hX hw (.start r) (by omega) closing rfl
    change s = .ws r at site
    subst s
    have start := soft_start_poll hw he (softState_event hp hX he st) hn left
    have cr : Tm.sPolls L X g (Prologue.warpIndex L g/4) j' = n :=
      Nat.succ.inj (start.symm.trans (count.trans poll))
    have old := ih (by omega) (List.getElem?_eq_some_iff.mp he).1.le st rfl cr
    refine ⟨fun u hu => ?_,fun u hu => ?_,?_⟩
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hu) with rfl | lt
      · exact verified
      · exact old.agree u lt
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hu) with eq | lt
      · rw [eq,snap]
        have prev := old.last u eq.symm
        have mf := congrArg V.mf view
        have mr := congrArg V.mr view
        have rs := congrArg V.rs view
        exact ⟨mf.symm.trans prev.1,mr.symm.trans prev.2.1,rs.symm.trans prev.2.2⟩
      · exact old.carry u lt
    · intro u eq
      obtain rfl := Nat.succ.inj eq
      simpa only [RoundCarry,snap] using stats

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values

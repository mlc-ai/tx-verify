-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundOrdinal
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

/-- A later round's factor field is read at its own shared store, with exactly the operands
of the round's closing poll. -/
theorem soft_round_factor {p L m X g i r v k acc u} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hw : Prologue.warpIndex L g < 8)
    (hs : softState p L X g i = some ⟨.pwend r,v,k,acc⟩) (hi : i ≤ (X.tr g).length)
    (credit : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1) (later : r ≠ .first) :
    (softRow p L X g).f u = Data.factor p v r := by
  obtain ⟨b,rfl⟩ : ∃ b : Bool, r = (if b then .plain else .bias) := by
    cases r
    · exact (later rfl).elim
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  obtain ⟨j,_,e,⟨s,x,k',acc'⟩,out,get,st,site,hn,_,same,cr⟩ :=
    soft_round_visit hp hX hw (.factor b) hi hs rfl
  change s = .stat b at site
  subst s
  change x = v at same
  subst x
  obtain ⟨c,rb,rp,ns,nv,ref,_,poll,sst⟩ := soft_round_counts hp hX hw get st
  have ord := factor_ordinal ref (pl := b) rfl
  have ev := softState_event hp hX get st
  have count := (soft_credit_step hw get ev (by change (0 : Nat) ≠ 80; decide)).symm.trans
    (cr.trans credit)
  change c (.acquire 80) = c .sst + 2 at ord
  have diff : u-1 = c .sst := by omega
  have nu : u ≠ 0 := by omega
  have isWrite : Softmax.cls L g .sst e = true := by
    rcases ev.1 with ⟨a,bs,kind⟩ | ⟨f,h⟩
    · simp only [Softmax.cls,kind]
    · exact (ev.2 f h).elim
  have idx := nthEv_eq get isWrite
  rw [sst] at idx
  simp only [softRow,nu,ite_false,wordState,diff,idx,st]
  cases b <;> rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Values

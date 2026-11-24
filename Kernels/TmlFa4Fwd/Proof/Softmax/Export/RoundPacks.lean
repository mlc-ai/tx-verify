-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundVisit
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Identify the four pack states directly from a closing round. Their entire operand state
is the closing poll's state. -/
theorem soft_round_pack (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g < 8) {i r v k acc u}
    (hs : softState p L X g i = some ⟨.pwend r,v,k,acc⟩) (hi : i ≤ (X.tr g).length)
    (credit : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1) (q : Fin 4) :
    ∃ j e k' acc', X.get (g,j) = some e ∧ softState p L X g j = some ⟨.pst r q,v,k',acc'⟩ ∧
      Tm.sPolls L X g (Prologue.warpIndex L g/4) j = u+1 ∧
      packState p L X g u q.val = some ⟨.pst r q,v,k',acc'⟩ := by
  obtain ⟨j,_,e,⟨s,x,k',acc'⟩,out,get,st,site,hn,left,same,poll⟩ :=
    soft_round_visit hp hX hw (.pack r q) hi hs rfl
  change s = .pst r q at site
  subst s
  change x = v at same
  subst x
  have ev := softState_event hp hX get st
  have cr := (soft_credit_step hw get ev (by change (0 : Nat) ≠ 80; decide)).symm.trans
    (poll.trans credit)
  obtain ⟨-, -, -, notWait, -⟩ := (succ_cases hn).resolve_left (fun stay => left stay.1)
  obtain ⟨pc,kd⟩ := e
  have store : Tm.isTcSt ⟨pc,kd⟩ = true := by
    have shape := ev.1
    change (if (Site.pst r q).delayed && k'.val == 0 then _ else _) at shape
    split at shape
    · rename_i h
      simp only [Bool.and_eq_true,beq_iff_eq] at h
      exact (notWait h.1 (Fin.ext h.2)).elim
    · rcases shape with ⟨a,vs,sh,rfl⟩ | ⟨f,h⟩
      · rfl
      · exact (ev.2 f h).elim
  refine ⟨j,⟨pc,kd⟩,k',acc',get,st,cr,?_⟩
  have num : Tm.stN X g j = 4*u+q.val := by
    unfold softState at st
    split at st
    · rename_i d n hd
      cases Option.some.inj st
      have ctrl := control_of_data hp hd
      obtain ⟨⟨c,⟨⟨rb,rp,ref⟩⟩,link⟩,_⟩ :=
        ((SmWarp.good hp hX hw (Frame.lt_of_get hX get) rfl j).2 _ ctrl).2 (ub_zero hX get ctrl)
      have num := ((site_counts ref).2 r q rfl).2
      change c .tcst+4 = 4*c (.acquire 80)+q.val at num
      rw [link .tcst rfl,link (.acquire 80) rfl] at num
      obtain ⟨poll,_,stores⟩ := tm_counts hw ctrl
      rw [poll] at cr
      rw [stores]
      omega
    · cases st
  rw [packState,← num]
  rwa [show nthEv X Tm.isTcSt g (Tm.stN X g j) = j from nthEv_eq get store]

end PTX.Kernels.TmlFa4Fwd.Proof.Values

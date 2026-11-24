-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundCredit
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem bias_stay {p L g z c v k acc e d'} (dst : d'.site = Site.bld z c)
    (h : succ p L g ⟨.bld z c,v,k,acc⟩ e = some (some d')) :
    k.val < 3 ∧ d'.k.val = k.val + 1 ∧ d'.v = v := by
  simp only [succ] at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · cases h
    exact ⟨by assumption,by change ((k+1 : Fin 4) : Nat) = _; omega,rfl⟩
  · cases h
    change (if c.val = 15 then Site.fence z else .bld z (c+1)) = .bld z c at dst
    split at dst
    · cases dst
    · have eq := (Site.bld.inj dst).2; omega

theorem bias_leaves_at_three {p L g z c v k acc e d'}
    (h : succ p L g ⟨.bld z c,v,k,acc⟩ e = some (some d')) (dst : d'.site ≠ .bld z c) :
    k.val = 3 := by
  by_contra hne
  have hlt : k.val < 3 := by have := k.isLt; omega
  simp only [succ,hlt,ite_true] at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> cases h
  exact dst rfl

/-- The substep index is exactly the number of earlier, consecutive reads of the same vector.
All these events occur at the vector load's own PC. -/
theorem soft_bias_history (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {z c} : ∀ {i v k acc e}, X.get (g,i) = some e →
    softState p L X g i = some ⟨.bld z c,v,k,acc⟩ →
    ∃ j, i = j+k.val ∧ softState p L X g j = some ⟨.bld z c,v,0,[]⟩ ∧
      ∀ x ≤ k.val, ∃ a bs, X.get (g,j+x) = some ⟨(Site.bld z c).pc,.rd a bs⟩ := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro v k acc e he hs
    have now : ∃ a bs, X.get (g,i) = some ⟨(Site.bld z c).pc,.rd a bs⟩ := by
      have ev := softState_event hp hX he hs
      unfold softState at hs
      split at hs
      · rename_i d n hd
        cases Option.some.inj hs
        have pc := Frame.event_pc (fun _ hg => threadD_sound hp hg) hX he hd
        change e.pc = (Site.bld z c).pc at pc
        rcases ev.1 with ⟨a,bs,hk⟩ | ⟨f,hk⟩
        · obtain ⟨pp,kd⟩ := e
          change pp = _ at pc
          change kd = _ at hk
          subst pp; subst kd
          exact ⟨_,_,he⟩
        · exact (ev.2 f hk).elim
      · cases hs
    by_cases hk : k = 0
    · subst k
      have ha : acc = [] := by
        unfold softState at hs
        split at hs
        · rename_i d n hd
          cases Option.some.inj hs
          rcases (SmWarp.data_event hp hX (SmWarp.storeSafe hp g) he hd).2 with ⟨_,ha,_⟩ | ha
          · exact ha
          · exact List.length_eq_zero_iff.mp ha.1
        · cases hs
      subst acc
      refine ⟨i,rfl,hs,fun x hx => ?_⟩
      obtain rfl : x = 0 := by omega
      exact now
    · obtain ⟨j,ev,prev,eq,get,old,hn⟩ := softState_pred hp
        (List.getElem?_eq_some_iff.mp he).1.le hs (by intro h; cases h)
      have site : prev.site = .bld z c := by
        rcases succ_cases hn with ⟨same,_⟩ | move
        · exact same.symm
        · exact (hk move.2.1).elim
      obtain ⟨s,v',k',acc'⟩ := prev
      change s = .bld z c at site
      subst s
      obtain ⟨_,ks,vs⟩ := bias_stay (by rfl) hn
      change k.val = k'.val + 1 at ks
      change v = v' at vs
      subst v'
      obtain ⟨base,pos,start,reads⟩ := ih j (by omega) get old
      refine ⟨base,by omega,start,fun x hx => ?_⟩
      by_cases h : x ≤ k'.val
      · exact reads _ h
      · simpa only [show base+x = i by omega] using now

end PTX.Kernels.TmlFa4Fwd.Proof.Values

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatVals
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatRead
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
import Kernels.TmlFa4Fwd.Proof.Common.DataTrace
import Kernels.TmlFa4Fwd.Proof.Softmax.Data.MaxSum
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundStep
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatSite
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat}

/-- The running sum at a data state with a minus-infinite maximum is zero. -/
theorem softState_sum_of_masked (hp : Pre p L m) {d : D} (hi : i ≤ (X.tr g).length)
    (hs : softState p L X g i = some d) : d.v.mf = false → d.v.rs = 0 := by
  unfold softState at hs
  split at hs
  · rename_i d' n hd
    cases hs
    refine role_induct (r := .softmax) (Q := fun _ (v : D) => v.v.mf = false → v.v.rs = 0)
      (fun _ _ => rfl) (fun {i d d' n e} _ _ h hn => ?_) hi hd
    change (SmWarp.codeT p L g).next d e = _ at hn
    rw [SmWarp.next_eq (SmWarp.numSteps hp)] at hn
    rcases Data.succ_stats hn with ⟨hf,_,hs⟩ | ⟨r,_,hf,_,hs⟩
    · rw [hf,hs]; exact h
    · intro hm
      rw [hf,finE,decide_eq_false_iff_not,not_not] at hm
      exact hs.trans (Data.sumAfter_of_bot hp g _ _ hm)
  · cases hs

/-- The two final statistics words see identical running statistics. -/
theorem soft_final_pair (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    {a bs} (he : X.get (g,i) = some ⟨(Site.fin 0).pc,.wr a bs⟩)
    (hl : LoadsBefore L X (g,i)) (hl' : LoadsBefore L X (g,i+1)) (hi : i+1 < (X.tr g).length) :
    ∃ (v : V), ∃ k acc, softState p L X g i = some ⟨.fin 0,v,k,acc⟩ ∧
      (softRow p L X g).rs = v.rs ∧ softMaxFinite p L X g = v.mf ∧
      (softRow p L X g).rm = (if v.mf then v.mr else 0) := by
  obtain ⟨⟨s,v,k,acc⟩,n,c,rb,rp,hs,pcEq,hQ,hF,w,_⟩ := stat_state hp hX hf hw hb he hl
  have es : s = .fin 0 := stat_site_of_pc (by simp) pcEq
  subst s
  obtain ⟨ec,hpos⟩ := final_ordinal hQ hF (j := 0) rfl
  change c .sst = softRounds p L g - 1 + 0 at ec
  rw [Nat.add_zero] at ec
  rw [ec] at w
  have state : softState p L X g i = some ⟨.fin 0,v,k,acc⟩ := by simp only [softState,hs]
  have next := softState_step hp he state (d' := D.mk' (.fin 1) v) rfl
  generalize eq : (X.tr g)[i+1] = e
  obtain ⟨pc,kd⟩ := e
  have get : X.get (g,i+1) = some ⟨pc,kd⟩ := (List.getElem?_eq_getElem hi).trans (congrArg some eq)
  have ev : EvS p L g (D.mk' (.fin 1) v) ⟨pc,kd⟩ := by
    unfold softState at next
    split at next
    · rename_i d count h
      cases Option.some.inj next
      exact (SmWarp.data_event hp hX (SmWarp.storeSafe hp g) get h).1
    · cases next
  rcases ev.1 with ⟨ad,bytes,rfl⟩ | ⟨f,h⟩
  · obtain ⟨d',n',c',rb',rp',hs',_,hq',hf',w',_⟩ := stat_state hp hX hf hw hb get hl'
    have e' : d' = D.mk' (.fin 1) v := Option.some.inj (by simpa only [softState,hs'] using next)
    subst d'
    obtain ⟨ec',_⟩ := final_ordinal hq' hf' (j := 1) rfl
    change c' .sst = softRounds p L g - 1 + 1 at ec'
    rw [show c' .sst = softRounds p L g by omega] at w'
    exact ⟨v,k,acc,state,by simp only [softRow,w,Option.map_some,Option.getD_some],
      by simp only [softMaxFinite,w',Option.map_some,Option.getD_some],
      by simp only [softRow,w',Option.map_some,Option.getD_some]⟩
  · exact (ev.2 f h).elim

/-- When the sum of a completed tile is positive, its final maximum has a finite payload. -/
theorem soft_finite_of_final_sum (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    {a bs pc N} (he : X.get (g,i) = some ⟨pc,.wr a bs⟩) (hloc : a.loc = statLoc L g 0)
    (hN : SoftRounds p L g N) (ho : barOrd X g i (Prologue.warpIndex L g + 3) = N)
    (hl : LoadsBefore L X (g,i)) (hl' : LoadsBefore L X (g,i+1)) (hi : i+1 < (X.tr g).length)
    (hpos : 0 < (softRow p L X g).rs) : softMaxFinite p L X g = true := by
  obtain ⟨s,rfl,word,⟨pl,rfl,_,hlt⟩ | ⟨j,rfl,_⟩⟩ := soft_stat_site hp hX hf hw he
  · have := hlt N hN; omega
  · have hj : j = 0 := by
      have eq := word.2.symm.trans hloc
      fin_cases j
      · rfl
      · simp [statLoc,statIx] at eq
    subst j
    obtain ⟨v,k,acc,hs,rs,flag,_⟩ := soft_final_pair hp hX hf hw hb he hl hl' hi
    rw [flag]
    cases hm : v.mf
    · have hz := softState_sum_of_masked hp (by omega) hs hm
      rw [rs,hz] at hpos
      exact (lt_irrefl _ hpos).elim
    · rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Values

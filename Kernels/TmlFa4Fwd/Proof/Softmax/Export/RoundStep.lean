-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Readback
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataFiring

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat} {e : Event}

/-- Read back a single traced transition of the data role, including the last recorded event. -/
theorem softState_step (hp : Pre p L m) (he : X.get (g,i) = some e)
    {d d' : D} (hs : softState p L X g i = some d) (hn : succ p L g d e = some (some d')) :
    softState p L X g (i+1) = some d' := by
  unfold softState at hs ⊢
  split at hs
  · rename_i a n hc
    obtain rfl := Option.some.inj hs
    rw [Frame.stateAt_succ (show (X.tr g)[i]? = some e from he), hc]
    have h : (SmWarp.codeT p L g).next a e = some (some d') := by
      rw [SmWarp.next_eq (SmWarp.numSteps hp)]
      exact hn
    have step : (threadD p L g).next (.inr ⟨.softmax,a⟩,n) e =
        some (some (.inr ⟨.softmax,d'⟩, Code.bump (Proof.cls L g) n e)) := by
      change (((SmWarp.codeT p L g).next a e).map _).map _ = _
      rw [h]
      rfl
    change (match (threadD p L g).next (.inr ⟨.softmax,a⟩,n) e with
      | some (some (.inr ⟨.softmax,v⟩,_)) => some v | _ => none) = _
    rw [step]
  · cases hs

/-- On the actual poll that closes a round, the next state records the online maximum
and the previous sum times the factor plus the sum of this round's probabilities. -/
theorem soft_round_step (hp : Pre p L m) (he : X.get (g,i) = some e) {r : Rd} {v k acc l par ac sc}
    (hs : softState p L X g i = some ⟨.pwend r,v,k,acc⟩)
    (hk : e.kind = .wait l par true ac sc) :
    ∃ d, softState p L X g (i+1) = some d ∧
      d.v.mf = finE (Data.maximum p L g v r) ∧ d.v.mr = (Data.maximum p L g v r).toReal ∧
      d.v.rs = (if r = .first then 0 else v.rs * Data.factor p v r) +
        ∑ col ∈ Finset.range 128, Data.scale p (Data.maximum p L g v r) *
          Data.weight p (Data.adjusted p (v.score col) (Data.loadedBias p L g v r col)) := by
  let d : D := ⟨.pwend r,v,k,acc⟩
  have hn : succ p L g d e = some (some (afterRound p L g d r)) := by simp only [d,succ,hk,ite_true]
  obtain ⟨h1,h2,h3⟩ := Data.afterRound_stats p L g d r
  refine ⟨_,softState_step hp he hs hn,h1,h2,h3.trans ?_⟩
  change Data.sumAfter p L g v r = _
  simp only [← Data.loaded_score, ← Data.probability_eq]
  cases r
  · simpa only [ite_true,zero_add,Data.P,Data.sumAfter] using Data.first_sum hp g v
  · simpa only [reduceCtorEq, ite_false, Data.rowSumT_eq, Data.P, Data.sumAfter] using
      Data.bias_sum hp g v
  · simpa only [reduceCtorEq, ite_false, Data.rowSumT_eq, Data.P, Data.sumAfter] using
      Data.plain_sum hp g v

end PTX.Kernels.TmlFa4Fwd.Proof.Values

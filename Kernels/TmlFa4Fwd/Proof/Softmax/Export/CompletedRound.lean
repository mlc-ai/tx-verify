-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundPacks
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StoredScores
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StoredBias
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundFactor
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundOrdinal
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.PlainCredit
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.PlainBias

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

noncomputable section

/-- Read the kind and all arithmetic operands of a round at its first P store. -/
def roundSnapshot (p : Params) (L : Launch) (X : Execution) (g u : Nat) : Rd × V :=
  match packState p L X g u 0 with
  | some ⟨.pst r _,v,_,_⟩ => (r,v)
  | _ => (.first,{})

/-- The trace fields and tile weights agree with one arithmetic round. -/
structure RoundAgrees (p : Params) (L : Launch) (X : Execution) (g : Nat) (t : Tile)
    (S : Nat → Nat → ℝ) (u : Nat) : Prop where
  first : u = 0 ↔ (roundSnapshot p L X g u).1 = .first
  weight : ∀ col < 128, let rv := roundSnapshot p L X g u
    Data.weight p (Data.score p L g rv.2 rv.1 col) =
      weightOf p t (t.rowOf (Prologue.warpIndex L g/4) (rowIx L g)) S u col
  pack : ∀ col < 128, let rv := roundSnapshot p L X g u
    (softRow p L X g).P u col = Data.P p L g rv.2 rv.1 col
  scale : let rv := roundSnapshot p L X g u
    (softRow p L X g).c u = Data.scale p (Data.maximum p L g rv.2 rv.1)
  factor : let rv := roundSnapshot p L X g u
    (softRow p L X g).f u = Data.factor p rv.2 rv.1

theorem completed_round {p L m X g t S u i r v k acc} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (reads : ScoreReads L X g S)
    (loads : ∀ {id a vs}, X.TLd id a vs .s32x32b → F32s vs)
    (ht : tileOf p L (g/L.block) = some t) (hv : t.Valid p (Prologue.warpIndex L g/4) (rowIx L g))
    (hu : u<t.n) (hi : i ≤ (X.tr g).length)
    (hs : softState p L X g i = some ⟨.pwend r,v,k,acc⟩)
    (credit : Tm.sPolls L X g (Prologue.warpIndex L g/4) i = u+1) :
    roundSnapshot p L X g u = (r,v) ∧ RoundAgrees p L X g t S u := by
  obtain ⟨j,e,k',acc',he,st,cr,pack⟩ := soft_round_pack hp hX hw hs hi credit 0
  change packState p L X g u 0 = some ⟨.pst r 0,v,k',acc'⟩ at pack
  have snap : roundSnapshot p L X g u = (r,v) := by simp only [roundSnapshot,pack]
  have first := first_at_pack hp hX hw he st cr
  refine ⟨snap,?_,?_,?_,?_,?_⟩
  · simpa only [snap] using first
  · intro c hc
    simp only [snap]
    have score := soft_stored_scores hp hX hw reads st (List.getElem?_eq_some_iff.mp he).1.le cr
      (⟨c,hc⟩ : Fin 128)
    apply Data.tile_weight _ _ _ _ _ _ _ _ _ _ _ score
    cases r with
    | first =>
      exact soft_stored_bias hp hX hf hw loads ht hv (z := false) st he cr
        (iff_of_true (first.mpr rfl) rfl) hu ⟨c,hc⟩
    | bias =>
      exact soft_stored_bias hp hX hf hw loads ht hv (z := true) st he cr
        (iff_of_false (fun h => Rd.noConfusion (first.mp h)) Bool.noConfusion) hu ⟨c,hc⟩
    | plain =>
      obtain ⟨B,rounds,lt⟩ := soft_plain_credit hp hX hw he st cr
      obtain ⟨key,zero⟩ := soft_plain_bias hp (Frame.lt_of_get hX he) hw rounds ht hv lt hu hc
      simp only [Data.loadedBias,key,zero,ite_true]
  · intro c hc
    let q : Fin 4 := ⟨c/32,by omega⟩
    obtain ⟨_,_,_,_,_,_,_,pack⟩ := soft_round_pack hp hX hw hs hi credit q
    simp only [snap,softRow,show c/32 = q.val from rfl,pack]
  · simp only [snap,softRow,pack]
  · simp only [snap]
    by_cases h : r = .first
    · obtain rfl := first.mpr h
      subst r
      rfl
    · exact soft_round_factor hp hX hw hs hi credit h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values

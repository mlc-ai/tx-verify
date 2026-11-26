-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TracedFold
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatRead
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.FinalPair
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatSite

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Numeric.OnlineFold
open PTX.Flow Softmax

/-- At the final shared sum write the running fold has covered the tile's blocks. -/
theorem soft_fold_at_sum {p L m X g i t S a bs pc} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (hb : SmWarp.BiasReadHandoff p L X)
    (reads : ScoreReads L X g S) (loads : ∀ {id a vs}, X.TLd id a vs .s32x32b → F32s vs)
    (ht : tileOf p L (g/L.block) = some t) (hv : t.Valid p (Prologue.warpIndex L g/4) (rowIx L g))
    (he : X.get (g,i) = some ⟨pc,.wr a bs⟩) (hloc : a.loc = statLoc L g 0)
    (hN : SoftRounds p L g t.n) (ord : barOrd X g i (Prologue.warpIndex L g + 3) = t.n)
    (hi : i+1 < (X.tr g).length) :
    Fold t.n (weightOf p t (t.rowOf (Prologue.warpIndex L g/4) (rowIx L g)) S)
      (softRow p L X g).P (softRow p L X g).c (softRow p L X g).f (softRow p L X g).rs ∧
      (softRow p L X g).c (t.n-1) =
        (2:ℝ) ^ (-(abiFloat p.scaleLog2Bits * (softRow p L X g).rm)) := by
  obtain ⟨s,rfl,word,⟨pl,rfl,_,hlt⟩ | ⟨j,rfl,_⟩⟩ := soft_stat_site hp hX hf hw he
  · have := hlt t.n hN; omega
  · have hj : j = 0 := by
      have eq := word.2.symm.trans hloc
      fin_cases j
      · rfl
      · simp [statLoc,statIx] at eq
    subst j
    have before (i : Nat) : LoadsBefore L X (g,i) := fun _ _ _ ld _ _ => loads ld
    obtain ⟨v,k,acc,state,rs,_,rm⟩ := soft_final_pair hp hX hf hw hb he (before _) (before _) hi
    have credit := (soft_final_credit hp hX hw he state).trans (softRounds_eq hN)
    exact traced_fold hp (tileOk hp ht).2.blocks
      (soft_row_history hp hX hf hw reads loads ht hv t.n le_rfl (by omega) state rfl credit) rs rm

end PTX.Kernels.TmlFa4Fwd.Proof.Values

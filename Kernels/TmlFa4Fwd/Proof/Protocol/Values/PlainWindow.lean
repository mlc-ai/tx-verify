-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.BiasGap
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageBar
import Kernels.TmlFa4Fwd.Proof.Loader.Export.BiasLag

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow.Arith32 Loader

/-- Beyond its biased rounds a stage is at least ten blocks left of its right edge. -/
theorem plain_window {p L g m B u} (hp : Pre p L m) (hg : g<L.threads)
    (hw : Prologue.warpIndex L g<8) (tile : StageRounds p L g B) (later : B<u) :
    ∃ b < p.batch, tilePrefix p b*p.heads ≤ g/L.block ∧ g/L.block < tilePrefix p (b+1)*p.heads ∧
      let t := (Epilogue.assignedCoordinates p b (g/L.block)).1
      let n := tileBlocks p b t
      u<n → 10+(if Prologue.warpIndex L g/4=0 ∧ stageZeroBlocks p b t<n then 1 else 0) ≤ u := by
  obtain ⟨R,bal,picked,rfl⟩ := tile
  obtain ⟨b,num⟩ := tile_num hp hg picked
  refine ⟨b,num.batch,num.lo,num.hi,?_⟩
  intro t n hu
  have ht : n<2^31 := by dsimp [n,tileBlocks]; have := (hp.lengths b num.batch).2.2; omega
  have cap := biasPick_rounds (p := p) (L := L) (g := g) (y := g) rfl R bal
  have stage : Softmax.stg L g = decide (4≤Prologue.warpIndex L g) := by
    have test : ∀ w<8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4≤w) := by decide
    exact test _ hw
  have val : sv (W n) = n := sv_W ht
  have prev := sv_addi_neg1 (W n) (by omega)
  simp only [biasPick,biasOf,r28Ref,r29Ref,num.r28,(bias_gap hp num).2,stage,w0,wRn] at cap
  change 1+(if sv (W n)<2 then 0 else (min (max (sv (addi (W n) (-1))) 0) 9).toNat)+
    (if decide (4≤Prologue.warpIndex L g)=false ∧ 10<sv (W n) ∧
      sv (if stageZeroBlocks p b t<n then i32 (-1) else i32 0)<0 then 1 else 0) = _ at cap
  rw [prev,val] at cap
  by_cases gap : stageZeroBlocks p b t<n
  · simp only [gap,ite_true,show sv (i32 (-1))<0 from by decide,and_true,
      decide_eq_false_iff_not] at cap ⊢
    split_ifs at cap ⊢ <;> omega
  · simp only [gap,ite_false,show ¬sv (i32 0)<0 from by decide,and_false,add_zero] at cap ⊢
    split at cap <;> omega

end PTX.Kernels.TmlFa4Fwd.Proof

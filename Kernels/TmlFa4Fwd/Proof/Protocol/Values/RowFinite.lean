-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.CompleteRounds
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.FinalPair
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.SoftStores
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatReadsAll

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Numeric.OnlineFold
open PTX PTX.Proof PTX.Flow TcMma Tm

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {t : Tile}

/-- A valid row has positive mass for any assignment of real-valued scores. Its last
block contains key zero. -/
theorem tile_fold_sum_pos (hp : Pre p L m) {c st ρ : Nat} (ht : tileOf p L c = some t)
    (hv : t.Valid p st ρ) (S : Nat → Nat → ℝ) (D : RowData)
    (fold : Fold t.n (weightOf p t (t.rowOf st ρ) S) D.P D.c D.f D.rs) : 0 < D.rs := by
  obtain ⟨_,ok⟩ := tileOk hp ht
  have hn := ok.blocks
  have nonneg (u k : Nat) : 0 ≤ weightOf p t (t.rowOf st ρ) S u k := by
    unfold weightOf
    split
    · exact (Real.rpow_pos_of_pos (by norm_num) _).le
    · exact le_rfl
  rw [fold.sum]
  apply mul_pos (fold.pos _ (by omega))
  apply Finset.sum_pos' (fun u _ => Finset.sum_nonneg fun k _ => nonneg u k)
  refine ⟨t.n-1,Finset.mem_range.mpr (by omega),?_⟩
  apply Finset.sum_pos' (fun k _ => nonneg _ k)
  refine ⟨0,Finset.mem_range.mpr (by decide),?_⟩
  have key : t.key (t.n-1) 0 < p.keyCount t.batch (t.rowOf st ρ) := by
    have := (hp.lengths t.batch ok.batch).2.1
    unfold Tile.Valid at hv
    simp only [Tile.key,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Params.keyCount]
    omega
  simp only [weightOf,key,ite_true]
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- Finiteness follows from the softmax link alone on a complete execution. -/
theorem rowFinite_of_softLink (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hC : Complete L X) (link : SoftLink p L X (tileOf p L) (softRow p L X)) :
    RowFinite p L X := by
  intro g t hg hw ht hv
  have before (e : EvId) : LoadsBefore L X e :=
    fun _ _ _ he _ _ => loads_f32 hp hX hf (softFacts hp hX hf) he
  have inputs := inputsUnwritten hp (Top.noInputWrite hp hX hf)
  have bytes : OperandBytes (tileInputs p L X) L X := operandBytes hp hX hf inputs
  let S u k := dot (tileInputs p L X (g/L.block)) (Prologue.warpIndex L g/4) u (rowIx L g) k
  have fold := (link g hg hw S (by
    intro i a j u vs he hj hu
    have hl : (tcDataCell32 L g a j).lane = rowIx L g := by
      simp only [tcDataCell32,laneBase,laneOf,rowIx,hp.block]
      omega
    simpa only [hl,S] using score_load hp hX hf bytes hw he hj hu)).2 t ht hv
  have pos := tile_fold_sum_pos hp ht hv S _ fold.1
  obtain ⟨hN,i,pc,he,ord⟩ := complete_soft_arrival hp hX hf hC hg hw ht
  have hn := (tileOk hp ht).2.blocks
  obtain ⟨j,hj,_,_,_,write,_,loc,same⟩ := soft_stat_sum hp hX hf hw he
    (show 1 ≤ barOrd X g i _ by omega)
  have len := (List.getElem?_eq_some_iff.mp (show (X.tr g)[i]? = _ from he)).1
  exact soft_finite_of_final_sum hp hX hf hw
    (biasReadHandoff hp hX hf inputs (biasWrites hp hX hf)) write loc hN (same.trans ord)
    (before _) (before _) (by omega) pos

end PTX.Kernels.TmlFa4Fwd.Proof.Values

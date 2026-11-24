-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LinksAll
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.RowFinite
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.SoftWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatReadsAll
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.FinalFold
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Every complete softmax lane stores its tile's running weights, scales and final statistics. -/
theorem softLink (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hC : Complete L X) : SoftLink p L X (tileOf p L) (softRow p L X) := by
  intro g hg hw S reads
  refine ⟨soft_pStored hp hX hf hw S reads,fun t ht hv => ?_⟩
  obtain ⟨hN,i,pc,he,ord⟩ := complete_soft_arrival hp hX hf hC hg hw ht
  have hn := (tileOk hp ht).2.blocks
  obtain ⟨j,hj,_,_,_,write,_,loc,same⟩ := soft_stat_sum hp hX hf hw he
    (show 1 ≤ barOrd X g i _ by omega)
  have len := (List.getElem?_eq_some_iff.mp (show (X.tr g)[i]? = _ from he)).1
  exact soft_fold_at_sum hp hX hf hw
    (biasReadHandoff hp hX hf
      (inputsUnwritten hp (Top.noInputWrite hp hX hf)) (biasWrites hp hX hf))
    reads (fun ld => loads_f32 hp hX hf (softFacts hp hX hf) ld)
    ht hv write loc hN (same.trans ord) (by omega)

/-- The final row-maximum word of every valid softmax row is finite. -/
theorem rowFinite (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hC : Complete L X) : RowFinite p L X :=
  rowFinite_of_softLink hp hX hf hC (softLink hp hX hf hC)

end PTX.Kernels.TmlFa4Fwd.Proof.Values

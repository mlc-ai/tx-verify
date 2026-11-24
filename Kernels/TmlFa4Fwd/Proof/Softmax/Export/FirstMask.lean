-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MaskWords
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
import Kernels.TmlFa4Fwd.Proof.Softmax.Data.MaskCount
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Common.Frame

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

/-- At a first-round P store, the instruction mask keeps exactly the tile's attended
keys. In particular the entire first block can be masked in stage zero. -/
theorem soft_first_mask {p L m X g i e} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hw : Prologue.warpIndex L g<8)
    (he : X.get (g,i) = some e) {q v k acc}
    (hs : softState p L X g i = some ⟨.pst .first q,v,k,acc⟩)
    {t : Tile} (tile : tileOf p L (g/L.block) = some t)
    (valid : t.Valid p (Prologue.warpIndex L g/4) (rowIx L g)) (c : Fin 4) (j : Fin 32) :
    Data.diagonal (mcnt p L g v) c.val j.val =
      decide (t.key 0 (32*c.val+j.val) < p.keyCount t.batch
        (t.rowOf (Prologue.warpIndex L g/4) (rowIx L g))) := by
  let d : D := ⟨.pst .first q,v,k,acc⟩
  have hg := Frame.lt_of_get hX he
  unfold softState at hs
  split at hs
  · rename_i d' n hd
    obtain rfl := Option.some.inj hs
    have hc := control_of_data hp hd
    have fit := (((SmWarp.good hp hX hw hg rfl i).2 _ hc).2 (ub_zero hX he hc)).2
    obtain ⟨b,hb,lo,hi,h0,h1,hu,hr⟩ := mask_words hp hg fit (by rfl) (by rfl)
    have eq := tileOf_eq (p := p) (L := L) (tileOf_some tile).1 (show Work p _ b from ⟨hb,lo,hi⟩)
    obtain rfl := Option.some.inj (tile.symm.trans eq)
    have out := Data.mask_key (v := v) hp hw hb h0 h1 hu hr valid c j
    simpa only [workTile,Tile.key,Tile.rowOf,rowIx,Loader.tileBlocks,Nat.sub_zero,
      Nat.add_assoc,Nat.reduceAdd,Prologue.warpIndex]
      using out
  · cases hs

end PTX.Kernels.TmlFa4Fwd.Proof.Values

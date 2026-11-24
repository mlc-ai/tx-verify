-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasColumn
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasTile
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Full

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow

/-- Each observed bias byte used after the first-round mask encodes the tile's bias.
Later rounds encode the masked value for every key, including unattended ones. -/
theorem soft_bias_match {p L m X g i a bs tl} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g<8) (b : Bool) (c : Fin 16)
    (he : X.get (g,i) = some ⟨(Softmax.Site.bld b c).pc,.rd a bs⟩) (z : Fin 4)
    (tile : tileOf p L (g/L.block) = some tl)
    (valid : tl.Valid p (Prologue.warpIndex L g/4) (rowIx L g)) :
    let u := barOrd X g i (stageId (Prologue.warpIndex L g/4))
    let key := tl.key u (8*c.val+2*(a.loc.addr/4%4)+z.val/2)
    let row := tl.rowOf (Prologue.warpIndex L g/4) (rowIx L g)
    u<tl.n → (key<p.keyCount tl.batch row ∨ u≠0) →
      bs[z.val]? = some (some ((biasValue (if key<p.keyCount tl.batch row then
        some (biasAt p tl.batch tl.head row key) else none)).byteAt (z.val%2))) := by
  obtain ⟨tl',st,q,j,org,k,al,pc,tile',hst,hq,hoff,issue,count,bytes⟩ :=
    soft_bias_tile_byte hp hX hf hw b c he z
  obtain rfl := Option.some.inj (tile'.symm.trans tile)
  rw [← hst] at valid ⊢
  intro u key row hu used
  obtain ⟨cta,warp⟩ := tmaLane_in (L := L) (X := X) hp g
  have objEq : bF L g st = obj L (tmaLane L X g) (320+8*st.val) := by simp only [bF,obj,cta]
  rw [objEq,← cta] at issue
  rw [objEq] at count
  obtain ⟨_,_,_,_,_,_,_,won⟩ := ld_tma_copy hp hX hf (.inl warp) (b_tmaOff st) issue rfl
  obtain ⟨batch,hb,lo,hi,col⟩ := ld_bias_group_column hp hX hf warp
    (fun _ _ _ _ _ get => tmaLane_won hX won get) issue hoff count
  rw [cta] at lo hi col
  obtain rfl := Option.some.inj (tile'.symm.trans (tileOf_eq (tileOf_some tile').1 ⟨hb,lo,hi⟩))
  let x := 8*(c.val%8)+2*(a.loc.addr/4%4)+z.val/2
  have idx : 64*q.val+x = 8*c.val+2*(a.loc.addr/4%4)+z.val/2 := by dsimp [x]; omega
  have hx : x<64 := by dsimp [x]; have := z.isLt; omega
  obtain ⟨lt,eq⟩ := bias_column_key (st := st) (q := q) hp hb hu hx
    (Nat.mod_lt _ (by decide : 0<128)) valid
  rw [Nat.add_assoc _ (64*q.val) x,idx] at eq
  let coord : Fin 3 → Int := ![org 0+(x : Int),((p.qOffset batch+row : Nat) : Int),
    ((workTile p (g/L.block) batch).head : Int)]
  have ec : coord 0 = p.biasColumn batch row key := by
    change org 0+(x : Int) = _
    rw [col]
    exact eq used
  have cut : p.biasColumn batch row key < 1280 := by
    rw [← ec]
    change org 0+(x : Int)<1280
    rw [col]
    exact lt
  have input := tile_bias_input hp hb (tileOk hp tile').2.head valid coord ec
    (by dsimp [coord]) rfl (Or.inr cut)
  change bs[z.val]? = some (some ((biasValue (inputVal p true coord)).byteAt (z.val%2))) at bytes
  rw [input] at bytes
  exact bytes

end PTX.Kernels.TmlFa4Fwd.Proof.Values

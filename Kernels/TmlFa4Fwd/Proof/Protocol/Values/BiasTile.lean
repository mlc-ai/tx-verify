-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasRead
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasElement
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.BiasOrigin
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Full

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow

/-- A bias byte at its tile row and head, with its signed source column recovered
from the observed copy and the element of the vector read. -/
theorem soft_bias_tile_byte {p L m X g i a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (b : Bool) (c : Fin 16)
    (he : X.get (g,i) = some ⟨(Softmax.Site.bld b c).pc,.rd a bs⟩) (t : Fin 4) :
    ∃ (tl : Tile) (st q : Fin 2) (j : Fin 14) (org : Fin 3 → Int) (k al pc : Nat),
      tileOf p L (g/L.block) = some tl ∧
      st.val = Prologue.warpIndex L g / 4 ∧ Fin.val (n := 2) q = c.val/8 ∧
      (Loader.inputSite j).sharedOffset = 166912+32768*st.val+16384*q.val ∧
      X.get (tmaLane L X g,k) =
        some ⟨pc,.tensorIssue al (inputSpec p L (g/L.block) j org (bF L g st))⟩ ∧
      ((X.tr (tmaLane L X g)).take k).countP (issuesTo (bF L g st)) =
        2 * barOrd X g i (stageId st.val)+q.val ∧
      let col := org 0 + ((8*(c.val%8)+2*(a.loc.addr/4%4)+t.val/2 : Nat) : Int)
      let row := tl.rowOf st.val (rowIx L g)
      bs[t.val]? = some (some ((biasValue (inputVal p true
        ![col,(p.qOffset tl.batch+row : Nat),tl.head])).byteAt (t.val%2))) := by
  obtain ⟨st,q,sub,j,org,hst,hq,subEq,_,hoff,⟨k,al,pc,issue,count⟩,hval⟩ :=
    soft_bias_source hp hX hf hw b c he t
  obtain ⟨cta,warp⟩ := tmaLane_in (L := L) (X := X) hp g
  have issue' := issue
  rw [← cta] at issue'
  obtain ⟨req,hreq,lo,hi,hr,hh⟩ := ld_bias_row_head hp hX hf (.inl warp) issue' hoff
  rw [cta] at lo hi hr hh
  let tl := workTile p (g/L.block) req
  have hg := Frame.lt_of_get hX he
  have grid : g/L.block < L.grid := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  refine ⟨tl,st,q,j,org,k,al,pc,tileOf_eq grid ⟨hreq,lo,hi⟩,hst,hq,hoff,issue,count,?_⟩
  have coord : boxCoord org (8*(c.val%8)+2*(a.loc.addr/4%4)+t.val/2) (g%L.block%128) =
      ![org 0+((8*(c.val%8)+2*(a.loc.addr/4%4)+t.val/2 : Nat) : Int),
        ((p.qOffset tl.batch+tl.rowOf st.val (rowIx L g) : Nat) : Int), (tl.head : Int)] := by
    funext z
    fin_cases z
    · rfl
    · change org 1 + ((g%L.block%128 : Nat) : Int) =
        ((p.qOffset tl.batch+tl.rowOf st.val (rowIx L g) : Nat) : Int)
      simp only [hr,tl,workTile,Tile.rowOf,rowIx,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      omega
    · exact hh
  simpa only [subEq,coord] using hval

end PTX.Kernels.TmlFa4Fwd.Proof.Values

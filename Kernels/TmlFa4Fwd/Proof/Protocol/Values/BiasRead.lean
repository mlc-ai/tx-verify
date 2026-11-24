-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasWindow
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Lemmas.Order.ReadLast

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow PTX.Proof

/-- A bias byte’s source coordinates and the ordinal of its copy. -/
theorem soft_bias_source {p L m X g i a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (b : Bool) (c : Fin 16)
    (he : X.get (g,i) = some ⟨(Softmax.Site.bld b c).pc,.rd a bs⟩) (t : Fin 4) :
    ∃ (st q : Fin 2) (k : Fin 4) (j : Fin 14) (org : Fin 3 → Int),
      st.val = Prologue.warpIndex L g / 4 ∧ q.val = c.val/8 ∧ k.val = a.loc.addr/4%4 ∧
      (Loader.inputSite j).bias = true ∧
      (Loader.inputSite j).sharedOffset = 166912 + 32768*st.val + 16384*q.val ∧
      (∃ k al pc, X.get (tmaLane L X g,k) =
        some ⟨pc,.tensorIssue al (inputSpec p L (g/L.block) j org (bF L g st))⟩ ∧
        ((X.tr (tmaLane L X g)).take k).countP (issuesTo (bF L g st)) =
          2 * barOrd X g i (stageId st.val) + q.val) ∧
      bs[t.val]? = some (some ((biasValue (inputVal p true
        (boxCoord org (8*(c.val%8)+2*k.val+t.val/2) (g%L.block%128)))).byteAt (t.val%2))) := by
  obtain ⟨poll,sz,sp,cta,_,q,row⟩ := soft_bias_read_at hp hX hf hw b c he
  let st : Fin 2 := ⟨Prologue.warpIndex L g / 4, by omega⟩
  have hh : SoftIn L g st.val g := ⟨Frame.lt_of_get hX he,rfl,hw,rfl⟩
  have objEq : sobj L g 320 = bF L g st := by
    rw [sobj]
    simp only [bF, st]
    congr 1
    omega
  rw [objEq] at poll
  have hBase := hp.shared.1
  have hr := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
  have hqBound := q.isLt
  have ht := t.isLt
  obtain ⟨j,org,hb,hoff,⟨k,al,pc,_,hg,rfl,cnt⟩,x,y,z,v,dst,dat,hwrite,hcov,hbyte,ord,last⟩ :=
    bias_byte hp hX hf (inputsUnwritten hp (Top.noInputWrite hp hX hf)) (biasWrites hp hX hf)
      (q := q) hh poll he (l := a.loc.at t.val) sp cta
      ⟨rfl,rfl,by simp [Loc.at],by simp only [Loc.at]; omega⟩
      (by simp only [Loc.at,st]; omega) (by simp only [Loc.at,st]; omega)
  obtain ⟨sub,subEq,hr',hwrd⟩ := soft_bias_window hp hX hf hw b c he
  have hq : q.val=c.val/8 := by omega
  refine ⟨st,q,sub,j,org,rfl,hq,subEq,hb,hoff,⟨k,al,pc,hg,cnt⟩,?_⟩
  have read : X.MemReads (.thread (g,i)) a bs := .inl ⟨_,he⟩
  have datEq := (read_byte_of_last_write hX read (show t.val < a.size by omega)
    hwrite hcov ord last).trans (congrArg some hbyte)
  let B := L.sharedBase+166912+32768*(Prologue.warpIndex L g/4)+16384*(c.val/8)
  have base : L.sharedBase+(Loader.inputSite j).sharedOffset = B := by
    rw [hoff,hq]
    dsimp [B,st]
    omega
  simp only [Loc.at,base] at datEq
  have off := hwrd t
  change TensorSwizzle.offset .b128 B (a.loc.addr+t.val-B) = _ at off
  rw [off] at datEq
  have rem := TensorSwizzle.offset_byte .b128 B (a.loc.addr+t.val-B)
  rw [off] at rem
  have hs := sub.isLt
  have col : (128*(g%L.block%128)+16*(c.val%8)+4*sub.val+t.val)%128/2 =
      8*(c.val%8)+2*sub.val+t.val/2 := by omega
  have erow : (128*(g%L.block%128)+16*(c.val%8)+4*sub.val+t.val)/128 = g%L.block%128 := by omega
  have parity : (a.loc.addr+t.val-B)%2=t.val%2 := by omega
  simpa only [col,erow,parity] using datEq

end PTX.Kernels.TmlFa4Fwd.Proof.Values

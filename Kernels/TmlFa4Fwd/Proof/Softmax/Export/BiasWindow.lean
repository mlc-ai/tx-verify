-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasReadAt
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.BiasOffset
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Lib.LoadAt
import Kernels.TmlFa4Fwd.Proof.Lib.LineWord
import Lemmas.Kernel.FrameU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow PTX.Proof Softmax

/-- The exact box, row and logical word of a bias read, before applying its TMA origin. -/
theorem soft_bias_window_state {p L m X g i a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (b : Bool) (c : Fin 16)
    (he : X.get (g,i) = some ⟨(Site.bld b c).pc,.rd a bs⟩) :
    let B := L.sharedBase+166912+32768*(Prologue.warpIndex L g/4)+16384*(c.val/8)
    ∃ (k : Fin 4) (v : Control.V) (acc : List Value) (n : Cls → Nat),
      Frame.stateAt (thread p L) X g i =
      some (some (SmWarp.sinj p L g ⟨.bld b c,v,k,acc⟩ n)) ∧ k.val = a.loc.addr/4%4 ∧
      a.loc.addr / 128 = B/128+(g%L.block%128) ∧
      ∀ t : Fin 4, TensorSwizzle.offset .b128 B (a.loc.addr+t.val-B) =
        128*(g%L.block%128)+16*(c.val%8)+4*k.val+t.val := by
  obtain ⟨v,k,acc,n,hs⟩ := bias_state_at hp hX hf hw b c he
  obtain ⟨ts,ins,o,hat,_,hc,hfi⟩ :=
    Frame.fired_siteU (fun _ hg => thread_sound hp hg) hX he hs (by intro _ h; cases h)
  obtain ⟨ins',ds,hcode,_,tmpl⟩ := bld_tmpl b c
  change kernel.code[(Site.bld b c).pc]? = some ins at hc
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have reg := bld_reg b c k v.scheduler acc hat
  change Fires _ (eventTmpl Assumptions.all L g ts ins.op) _ _ at hfi
  rw [tmpl] at hfi
  obtain ⟨hl,_⟩ := loadTmpl_rd (effAddr_shared32 reg) hfi rfl
  let A := (truncBits 32 (truncBits 32 (bldX L g c)+BitVec.ofInt 64 (bldOff c))).toNat
  have addr : a.loc.addr=A+4*k.val := by rw [hl]; exact congrArg (fun j => A+4*j) hat.2.1
  have val := Data.bias_address hp hw c
  have bound := Arith32.col_xor_lt (c.val%8) (by omega) (g%L.block%128%8) (by omega)
  have align := hp.shared.1
  have hk := k.isLt
  dsimp only
  refine ⟨k,v,acc,n,hs,?_,?_,?_⟩
  · dsimp only [A] at addr
    rw [addr,val]
    omega
  · change a.loc.addr/128 =
        (L.sharedBase+166912+32768*(g%L.block/32/4)+16384*(c.val/8))/128 + g%L.block%128
    dsimp only [A] at addr
    rw [addr,val]
    omega
  · intro t
    have ht := t.isLt
    have hoff := Data.bias_offset hp hw c ⟨4*k.val+t.val,by omega⟩
    rw [addr]
    simpa only [A,Prologue.warpIndex,Nat.add_assoc] using hoff

theorem soft_bias_window {p L m X g i a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g < 8) (b : Bool) (c : Fin 16)
    (he : X.get (g,i) = some ⟨(Site.bld b c).pc,.rd a bs⟩) :
    let B := L.sharedBase+166912+32768*(Prologue.warpIndex L g/4)+16384*(c.val/8)
    ∃ k : Fin 4, k.val = a.loc.addr/4%4 ∧ a.loc.addr / 128 = B/128+(g%L.block%128) ∧
      ∀ t : Fin 4, TensorSwizzle.offset .b128 B (a.loc.addr+t.val-B) =
        128*(g%L.block%128)+16*(c.val%8)+4*k.val+t.val := by
  obtain ⟨k,_,_,_,_,idx,row,bytes⟩ := soft_bias_window_state hp hX hf hw b c he
  exact ⟨k,idx,row,bytes⟩

end PTX.Kernels.TmlFa4Fwd.Proof

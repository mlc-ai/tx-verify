-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasMatch
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasDecoded
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow

private theorem bias_byte_inj {x y : Option ℝ}
    (h : (biasValue x).byteAt 0 = (biasValue y).byteAt 0) : x=y := by
  cases x <;> cases y <;> cases h <;> rfl

/-- The decoded real half used in a round equals the specification bias, with the
first-round mask applied. A masked key is represented by none. -/
theorem soft_bias_operand {p L m X g i a bs tl} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g<8) (b : Bool) (c : Fin 16)
    (he : X.get (g,i) = some ⟨(Softmax.Site.bld b c).pc,.rd a bs⟩)
    (tile : tileOf p L (g/L.block) = some tl)
    (valid : tl.Valid p (Prologue.warpIndex L g/4) (rowIx L g))
    (hprev : ∀ j < i, ∀ ad xs sh, X.TLd (g,j) ad xs sh → F32s xs) :
    let u := barOrd X g i (stageId (Prologue.warpIndex L g/4))
    let row := tl.rowOf (Prologue.warpIndex L g/4) (rowIx L g)
    u<tl.n → ∃ w, rebuild 3 bs = .ok w ∧ Softmax.biasOk w=true ∧ ∀ z : Fin 2,
      let key := tl.key u (8*c.val+2*(a.loc.addr/4%4)+z.val)
      let v := if z=0 then (maskedPair .bf16 w).1 else (maskedPair .bf16 w).2
      (if u=0 ∧ p.keyCount tl.batch row ≤ key then none else v) =
        if key<p.keyCount tl.batch row then some (biasAt p tl.batch tl.head row key) else none := by
  intro u row hu
  obtain ⟨w,lo,hi,read,accept,parts,bytes⟩ := soft_bias_decoded hp hX hf
    (biasReadHandoff hp hX hf
      (inputsUnwritten hp (Top.noInputWrite hp hX hf)) (biasWrites hp hX hf))
    hw b c he hprev
  refine ⟨w,read,accept,?_⟩
  intro z key v
  by_cases skip : u=0 ∧ p.keyCount tl.batch row ≤ key
  · simp only [skip.1,skip.2,true_and,ite_true,Nat.not_lt.mpr skip.2,ite_false]
  rw [ite_eq_right skip]
  have used : key < p.keyCount tl.batch row ∨ u≠0 := by omega
  let t : Fin 4 := ⟨2*z.val,by have := z.isLt; omega⟩
  have eq := soft_bias_match hp hX hf hw b c he t tile valid hu
    (by simpa only [t,Nat.mul_div_cancel_left _ (by decide : 0<2)] using used)
  rw [bytes] at eq
  apply bias_byte_inj
  fin_cases z <;> simpa [v,t,parts,SmWarp.biasPairBytes,key] using eq

end PTX.Kernels.TmlFa4Fwd.Proof.Values

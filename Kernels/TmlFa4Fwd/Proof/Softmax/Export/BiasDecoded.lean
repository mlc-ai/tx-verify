-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasReadAt
public import Kernels.TmlFa4Fwd.Proof.SmWarp.PrefixReads
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.BiasSrc
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataFiring
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow Softmax

/-- Decode both real operands, including the all-mask bit-pattern. -/
theorem rebuild_bias_halves (lo hi : Option ℝ) :
    ∃ w, rebuild 3 (SmWarp.biasPairBytes lo hi) = .ok w ∧ maskedPair .bf16 w = (lo,hi) := by
  refine ⟨(match lo,hi with
    | none,none => Value.bits 32 0xFF80FF80
    | _,_ => .pair (biasValue lo) (biasValue hi)),?_,?_⟩
  · cases lo <;> cases hi <;>
      simp [SmWarp.biasPairBytes,biasValue,rebuild,rebuild.halves,Value.bytes,Value.byteAt,
        Value.toBytes,FloatFmt.bytes,List.range_succ,intByte,rebuildBits,littleEndianBits,
        byteBits,Value.bitPattern,bind,Option.bind,Except.bind,pure,Except.pure]
  · cases lo <;> cases hi <;> rfl

/-- The word decoded by a live softmax load, with the four bytes it came from. -/
theorem soft_bias_decoded {p L m X g i a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hB : SmWarp.BiasReadHandoff p L X) (hw : Prologue.warpIndex L g<8)
    (b : Bool) (c : Fin 16) (he : X.get (g,i) = some ⟨(Site.bld b c).pc,.rd a bs⟩)
    (hprev : ∀ j < i, ∀ ad xs sh, X.TLd (g,j) ad xs sh → Values.F32s xs) :
    ∃ w lo hi, rebuild 3 bs = .ok w ∧ biasOk w=true ∧ maskedPair .bf16 w = (lo,hi) ∧
      bs = SmWarp.biasPairBytes lo hi := by
  obtain ⟨_,_,_,_,hc⟩ := bias_state_at hp hX hf hw b c he
  obtain ⟨d,nxt,eq⟩ := SmWarp.lift_state hp hc (SmWarp.alive_of_prefix_reads hp hX hw hB he hprev)
  have ctl := control_of_data hp nxt
  obtain ⟨⟨n,ref,_⟩,_⟩ := ((SmWarp.good hp hX hw (Frame.lt_of_get hX he) rfl i).2 _ ctl).2
    (ub_zero hX he ctl)
  obtain ⟨lo,hi,src⟩ := hB _ _ _ _ _ _ _ _ _ _ he nxt (SmWarp.data_ref ref)
    (congrArg Control.D.site eq) rfl
  have size := (soft_bias_read_at hp hX hf hw b c he).2.1
  have bytes := SmWarp.read_biasPairBytes hX (.inl ⟨_,he⟩) size src
  obtain ⟨w,read,parts⟩ := rebuild_bias_halves lo hi
  obtain ⟨w',read',accept⟩ := SmWarp.rebuild_biasPairBytes lo hi
  cases read.symm.trans read'
  exact ⟨w,lo,hi,bytes ▸ read,accept,parts,bytes⟩

end PTX.Kernels.TmlFa4Fwd.Proof

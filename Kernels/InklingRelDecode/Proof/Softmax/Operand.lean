-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
public import Lemmas.Kernel.Frame
import Lemmas.Kernel.FrameU
import Kernels.InklingRelDecode.Proof.Common.FollowControl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control

/-- The operand of a butterfly shuffle is the tracked value of its source register. -/
theorem operand {Q L m X g k ev mode a b c recv ok w ent d cnt dst src pc bv}
    {n : Int}
    (hX : Consistent L kernel Assumptions.all m X) (hp : Pre Q L m) (get : X.get (g,k)=some ev)
    (kind : ev.kind=.shfl mode a b c recv ok) (hpc : d.site.pc=pc)
    (hs : Frame.stateAt (thread Q L) X g k=some (some (softState w ent d cnt)))
    (code : kernel.code[pc]?=some ⟨none,.warp ⟨.shfl .bfly,some (.int .b 32),[some dst],
      [.reg src,.imm n,.imm 31],some (.imm (-1))⟩⟩)
    (one : ∀ t : TState, ∃ m, readBits L g t 32 (.imm n)=.ok m ∧ m.toNat=bv) :
    (src ∈ ctlLive pc → a=valueOf ent L g d src) ∧ mode=.bfly ∧ b=bv ∧ c=31 := by
  subst hpc
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs
    (fun _ h => by rw [kind] at h; cases h)
  change kernel.code[d.site.pc]?=some ins at hc
  change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) _ o at fire
  obtain rfl := Option.some.inj (hc.symm.trans code)
  obtain ⟨_,_,_,_,regs⟩ := ht
  obtain ⟨m,one,tn⟩ := one t
  obtain ⟨same,mode,bval,cval⟩ := Lib.shfl_operand (n := n) one tn fire kind
  refine ⟨fun live => ?_,mode,bval,cval⟩
  have reg := holds_mem regs (mem_factsFrom live)
  change t.regs src=some (valueOf ent L g d src) at reg
  exact Option.some.inj (same.symm.trans reg)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

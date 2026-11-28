-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
public import Kernels.InklingRelDecode.Proof.Common.ValueThread
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Step
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEntry
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Proof.Softmax.Export.Value
import Kernels.InklingRelDecode.Proof.Softmax.Operand
import Kernels.InklingRelDecode.Proof.Softmax.LateStep
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Kernel.FrameU

/-! # The state of a lane at its shuffle of pc 1838

The word a lane sends at pc 1838 is register 1520 of its value state at the site of the shuffle,
which is the first window's result on the registers of the state. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The word a lane sends at pc 1838** is the first window's result on its value state's
registers; the state is a softmax state at the site of the shuffle. -/
public theorem sent_state {m : Mem0} {X : Execution} {k : Nat} {mode : ShflMode} {b c : Nat}
    {recv : Value} {ok : Bool} {sent : Value} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩) :
    ∃ (w : Value) (ent : Control.Entry) (d : Control.D) (y : Data.D) (n : Cls → Nat),
      Frame.stateAt (thread Q L) X g k = some (some (softState w ent d n)) ∧
      Control.Inv ent (g % L.block) d ∧
      Frame.stateAt (threadD Q L) X g k = some (some (softDState w ent y n)) ∧
      y.c = d ∧ y.c.site = .shfl5 ∧ sent = vFin (w1V ent L g y) 1520 := by
  have clean : ∀ f, (Event.mk 1838 (.shfl mode sent b c recv ok)).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, -, -, -, hsc, -, hinv, atpc, -⟩ := softmax_event_entry hp hX hf get clean
    (by show 574 < 1838; omega) (by show 1838 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have site : y.c.site = .shfl5 := by
    have h7 : y.c.site.pc = 1838 := by
      have := atpc
      rw [← hy] at this
      exact this.symm
    revert h7
    cases y.c.site <;> repeat' first | decide +kernel | (rename_i i; revert i)
  refine ⟨w, ent, d, y, n, hsc, hinv, hs, hy, site, ?_⟩
  obtain ⟨t, ins, o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t at ht
  obtain ⟨-, -, -, -, regs⟩ := ht
  change kernel.code[y.c.site.pc]? = some ins at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t ins.op) _ o at fire
  have h7 : y.c.site.pc = 1838 := by rw [site]; rfl
  rw [h7] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_5)
  obtain ⟨same, -, -, -⟩ := Lib.shfl_operand (n := 16) (m := (16 : Nat)) (bv := 16) rfl rfl fire rfl
  have reg : t.regs 1520 = some (vFin (w1V ent L g y) 1520) := by
    obtain ⟨-, -, -, hW⟩ := atS_holds regs
    refine holds_mem hW ?_
    simp [w1F, site, factsFrom, kXin]
  exact Option.some.inj (same.symm.trans reg)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

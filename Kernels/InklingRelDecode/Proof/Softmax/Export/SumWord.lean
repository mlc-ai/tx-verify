-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ni
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Proof.Softmax.Export.Value
import Kernels.InklingRelDecode.Proof.Softmax.Operand
import Kernels.InklingRelDecode.Flow.Code.Part035

/-! # The word a lane sends at pc 2234 is a number

The row sum (register 1529) is one of the registers the exponent window leaves; it is a number when
the window's inputs are typed (`exp_typed`, `xV_expIn`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem site_2234 (s : Site) (h : s.pc = 2234) : s = .shfl6 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The shuffle at pc 2234 is the `bfly` by 16 and its word is a number**, when the score loads
return numbers and the shuffles of pc 1838 send and bring numbers or `-inf`. -/
public theorem sent_sum {m : Mem0} {X : Execution} {k : Nat} {mode : ShflMode} {b c : Nat}
    {recv : Value} {ok : Bool} {sent : Value} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (get : X.get (g, k) = some ⟨2234, .shfl mode sent b c recv ok⟩) :
    mode = .bfly ∧ b = 16 ∧ c = 31 ∧ SK.fl.Has sent := by
  have clean : ∀ f, (Event.mk 2234 (.shfl mode sent b c recv ok)).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean (by show 574 < 2234; omega)
    (by show 2234 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  have lane : g % L.block < 128 := data_warp hp hX len hsc
  obtain ⟨typ, ni⟩ := soft_ni hp hX hf hS (h5 lane) k len _ hs nub w ent y n rfl
  have site : y.c.site = .shfl6 := site_2234 _ (by
    have := atpc
    rw [← hy] at this
    exact this.symm)
  obtain ⟨t, ins, o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t at ht
  obtain ⟨-, -, -, -, regs⟩ := ht
  change kernel.code[y.c.site.pc]? = some ins at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t ins.op) _ o at fire
  have h7 : y.c.site.pc = 2234 := by rw [site]; rfl
  rw [h7] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_6)
  obtain ⟨same, hm, hb, hc⟩ :=
    Lib.shfl_operand (n := 16) (m := (16 : Nat)) (bv := 16) rfl rfl fire rfl
  have hE : ExpIn (xV ent L g y) := xV_expIn hp typ (by simp [m0, site]; exact ni.m) ni.mx
  have hF := atS_xF regs
  rw [xF_round (by rw [site]; rfl) hE] at hF
  have k1 : 1529 ∈ xKeys := by decide +kernel
  have hreg := holds_mem hF (mem_factsFrom (val := xE ent L g y) k1)
  refine ⟨hm, hb, hc, ?_⟩
  rw [Option.some.inj (same.symm.trans hreg)]
  have := exp_typed hE (show 1529 ∈ runE2.outs by decide +kernel)
  simp only [ExpTy] at this
  exact this

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

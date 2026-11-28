-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.WordsEv
public import Kernels.InklingRelDecode.Proof.Softmax.Export.Butterfly
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds
import Kernels.InklingRelDecode.Proof.Softmax.Soft.MxInv
import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.EntGlue
import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaExact
import Kernels.InklingRelDecode.Proof.Softmax.ShuffleCount
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEntry
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Softmax.Data.Update
import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
import Kernels.InklingRelDecode.Proof.Softmax.Data.Site
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Kernel.FrameU

/-! # The first stage of the minimum butterfly sends the rescale factor

The word the shuffle of pc 2242 sends is the rescale factor of its round (register 507): it reads
as the fold's factor `stepAlpha` of the round `R` the shuffle's poll count names, and the lane has
made `1 + preload + shflBase R + 3` shuffles before it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem site_2242 (s : Site) (h : s.pc = 2242) : s = .shfl7 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The first stage sends the fold's factor.** -/
public theorem stage0_ev {m : Mem0} {X : Execution} {j : Nat} {a r : Value} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X) (lane : g % L.block < 128)
    (st : Stage X 0 g j a r) :
    ∃ R, pollRound 1257 ((X.tr g).take j) = R + 1 ∧
      ((X.tr g).take j).countP Execution.isShfl =
        1 + Iface.preloadCount Q L (g / L.block) + Lib.shflBase R + 3 ∧
      (Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block)) →
        Lib.Rd a ((Lib.SoftRow.stepAlpha (Q.scale * log2eF32) (Lib.laneBlk Q L g R)
          (Lib.laneSt Q L g R) : ℝ) : EReal)) := by
  obtain ⟨ok, get⟩ := st
  have get' : X.get (g, j) = some ⟨2242, .shfl .bfly a 8 31 r ok⟩ := get
  have clean : ∀ f, (Event.mk 2242 (.shfl .bfly a 8 31 r ok)).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, t, ins, u, hsc, -, inv, atpc, hc, fire⟩ := softmax_event_entry hp hX hf
    get' clean (by show 574 < 2242; omega) (by show 2242 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have hg := Frame.lt_of_get hX get'
  have len := (List.getElem?_eq_some_iff.mp get').1.le
  have nub := Frame.noUbBefore_of_get hX get'
  have site : y.c.site = .shfl7 := by
    refine site_2242 _ ?_
    have := atpc
    rw [← hy] at this
    exact this.symm
  obtain ⟨E, -, -, -⟩ := ent_glue hp hX hg len hsc
  obtain ⟨led, -, -, -⟩ := soft_win hp hX (hB g) j len _ hs nub w ent y n rfl inv.entry E
  have led' : pollRound 1257 ((X.tr g).take j) = y.c.i + 1 := by
    simpa only [Led, site, Site.afterS, Bool.toNat_true] using led
  have ord := shfl_ordinal hp hX len hsc nub
  have shf : n Cls.shfl = ((X.tr g).take j).countP Execution.isShfl := fcount hsc _
  have inr : shflInRound d.site d.i = 3 := by rw [← hy, site]; rfl
  simp only [shflCount, inr] at ord
  have hc7 : y.c.i = d.i := by rw [← hy]
  refine ⟨y.c.i, led', by rw [← shf, ord, ← hc7]; omega, fun hv => ?_⟩
  have M := soft_mex hp hX (words_ev hp hX hf hB hS lane hv) j len _ hs nub w ent y n rfl inv.entry
  obtain ⟨t', ins', o, ht, -, hc', fire'⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX
    get' hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t' at ht
  have ht := atS_code ht
  change kernel.code[y.c.site.pc]? = some ins' at hc'
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t' ins'.op) _ o at fire'
  have h7 : y.c.site.pc = 2242 := by rw [site]; rfl
  rw [h7] at hc' fire'
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_2242)
  obtain ⟨same, -, -, -⟩ := Lib.shfl_operand (n := 8) (m := (8 : Nat)) (bv := 8) rfl rfl fire' rfl
  have round : inRound y.c.site = true := by rw [site]; rfl
  have reg : t'.regs 507 = some (alphaWord (scaleW L) y.v.m y.v.mx) := by
    refine holds_mem (atD_dF ht) ?_
    exact round_sub round y.v _ (by simp [alphaFacts, alphaWord])
  have eq : a = alphaWord (scaleW L) y.v.m y.v.mx := Option.some.inj (same.symm.trans reg)
  have hpos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  have a0 : updS y.c.site = false := by rw [site]; rfl
  have a1 : afterW y.c.site = true := by rw [site]; rfl
  have jm0 := M.m
  simp only [a0, Bool.toNat_false, Nat.add_zero] at jm0
  obtain ⟨-, -, hal⟩ := alpha_exact (scaleW_ev hp) hpos jm0 (M.mx a1)
  rw [eq]
  exact hal

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

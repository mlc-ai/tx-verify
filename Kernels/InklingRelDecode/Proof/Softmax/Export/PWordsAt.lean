-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ni
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
import Kernels.InklingRelDecode.Proof.Softmax.Data.PkTyped
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal6
import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaExact
import Kernels.InklingRelDecode.Proof.Softmax.Data.ShiftExact
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Lemmas.Flow.TcStValsAny

/-! # The words of the probability store are pairs of `bf16` numbers

At the store of pc 1009 the thread's value state holds the exponent window's facts, whose pack
words are the 32 registers the store reads (`tm_typed`): typed when the window's inputs are, which
the value state's typing gives (`soft_ni`, `xV_expIn`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem site_1009 (s : Site) (h : s.pc = 1009) : s = .tmemSt := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem tm_reg : ∀ p < 32, 1677 + p ∈ kTm := by decide +kernel

/-- **Every word of the probability store is a pair of `bf16` numbers**, when the score loads
return numbers and the shuffles of pc 1838 send and bring numbers or `-inf`. -/
public theorem pword_event {m : Mem0} {X : Execution} {k a : Nat} {vals : List Value}
    {sh : TcShape} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (get : X.get (g, k) = some ⟨1009, .tc (.st a vals sh)⟩) :
    ∀ v ∈ vals, ∃ x y : ℝ, v = .pair (.float .bf16 x) (.float .bf16 y) := by
  have clean : ∀ f, (Event.mk 1009 (.tc (.st a vals sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hsc, atpc⟩ := at_site hp hX get clean (by show 574 < 1009; omega)
    (by show 1009 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  have lane : g % L.block < 128 := data_warp hp hX (List.getElem?_eq_some_iff.mp get).1.le hsc
  obtain ⟨typ, ni⟩ := soft_ni hp hX hf hS (h5 lane) k len _ hs nub w ent y n rfl
  have site : y.c.site = .tmemSt := by
    refine site_1009 _ ?_
    have := atpc
    rw [← hy] at this
    exact this.symm
  obtain ⟨t, ins, o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t at ht
  obtain ⟨-, -, -, -, regs⟩ := ht
  change kernel.code[y.c.site.pc]? = some ins at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t ins.op) _ o at fire
  have h7 : y.c.site.pc = 1009 := by rw [site]; rfl
  rw [h7] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_0)
  have hm0 : m0 y = y.v.mp := by simp [m0, site]
  have hE : ExpIn (xV ent L g y) := xV_expIn hp typ (by rw [hm0]; exact ni.mp) ni.mx
  have hF := atS_xF regs
  rw [xF_tmemSt site hE] at hF
  obtain ⟨hl0, hvals⟩ := fires_tcSt_valsAny (sh := .s16x32bx2 32) (fun s h => nomatch h) fire rfl
  have hl : vals.length = 32 := hl0
  intro v hv
  obtain ⟨p, hpv, rfl⟩ := List.getElem_of_mem hv
  have hp32 : p < 32 := by
    have := hpv
    rw [hl] at this
    simpa using this
  have hk := tm_reg p hp32
  have hreg := holds_mem hF (mem_factsFrom (val := vP2 (vP1 (xE ent L g y))) hk)
  have hv' := hvals p hpv (1677 + p) (by interval_cases p <;> rfl)
  rw [hreg] at hv'
  rw [← Option.some.inj hv']
  exact tm_typed hE _ hk

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

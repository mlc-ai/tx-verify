-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.WordsEv
public import Kernels.InklingRelDecode.Proof.Lib.LaneFold
import Kernels.InklingRelDecode.Proof.Softmax.Soft.PwEx
import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.EntGlue
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEntry
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Rows
import Lemmas.Flow.TcStValsAny
import Lemmas.Kernel.FrameU

/-! # The words of the probability store of a valid row are the exact probabilities

Word `p` of the store of pc 1009 is the pair of the probabilities of columns `2 p` and `2 p + 1`
of the lane's half of the round's block (`Lib.lanePw`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem site_1009 (s : Site) (h : s.pc = 1009) : s = .tmemSt := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The probability store writes the exact probabilities.** -/
public theorem pword_ev {m : Mem0} {X : Execution} {k a : Nat} {vals : List Value}
    {sh : TcShape} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X)
    (lane : g % L.block < 128) (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block)))
    (get : X.get (g, k) = some ⟨1009, .tc (.st a vals sh)⟩) :
    vals.length = 32 ∧ pollRound 1257 ((X.tr g).take k) - 1 <
      Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x) ∧
    ∀ p < 32, vals[p]? = some (.pair
      (.float .bf16 (Lib.lanePw Q L g (pollRound 1257 ((X.tr g).take k) - 1) (2 * p)))
      (.float .bf16 (Lib.lanePw Q L g (pollRound 1257 ((X.tr g).take k) - 1) (2 * p + 1)))) := by
  have clean : ∀ f, (Event.mk 1009 (.tc (.st a vals sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, t, ins, u, hsc, -, inv, atpc, -, -⟩ := softmax_event_entry hp hX hf get
    clean (by show 574 < 1009; omega) (by show 1009 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have hg := Frame.lt_of_get hX get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  obtain ⟨E, hP, lim, hq⟩ := ent_glue hp hX hg len hsc
  obtain ⟨hx, hy', hz⟩ := Lib.coordinate_bounds hp hg
  have vr := valid_row hq (hp.qLenLe _ hz) hv
  have site : y.c.site = .tmemSt := by
    refine site_1009 _ ?_
    have := atpc
    rw [← hy] at this
    exact this.symm
  obtain ⟨led, inv', cur, sc⟩ := soft_win hp hX (hB g) k len _ hs nub w ent y n rfl inv.entry E
  have M := soft_mex hp hX (words_ev hp hX hf hB hS lane hv) k len _ hs nub w ent y n rfl inv.entry
  obtain ⟨k', a', sh', hk', hg', hpr⟩ := sc.ev (by rw [site]; rfl)
  have hs64 : ∀ j < 64, y.v.s[j]? = some (.float .f32 (Lib.laneScore Q L g y.c.i j)) := by
    intro j hj
    have := hS g k' a' y.v.s sh' hg' hv j hj
    rwa [hpr, Nat.add_sub_cancel] at this
  have hc64 := (cur vr).cur (by rw [site]; rfl)
  have hlt : y.c.i < ent.limit := inv'.loop (by rw [site]; decide) (by rw [site]; decide)
    (by rw [site]; decide) (fun j => by rw [site]; nofun)
  rw [lim] at hlt
  have hn := Lib.blk_lt hp.splitsPos hlt
  have hn' : Q.splits * y.c.i + (L.ctaidOf (g / L.block)).get .x <
      Q.blocks ((L.ctaidOf (g / L.block)).get .z) := by
    have := Nat.mul_comm Q.splits y.c.i
    omega
  have rd : pollRound 1257 ((X.tr g).take k) - 1 = y.c.i := by
    have := led
    simp only [Led, site, Site.afterS, Bool.toNat_true] at this
    omega
  obtain ⟨hE, hw⟩ := pw_words hp site E hP inv'.thread hn' (hp.seqRange _ hz) hs64 hc64 M
  obtain ⟨t', ins', o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t' at ht
  obtain ⟨-, -, -, -, regs⟩ := ht
  change kernel.code[y.c.site.pc]? = some ins' at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t' ins'.op) _ o at fire
  have h7 : y.c.site.pc = 1009 := by rw [site]; rfl
  rw [h7] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_0)
  have hF := atS_xF regs
  rw [xF_tmemSt site hE] at hF
  obtain ⟨hl0, hvals⟩ := fires_tcSt_valsAny (sh := .s16x32bx2 32) (fun s h => nomatch h) fire rfl
  refine ⟨hl0, by rw [rd]; exact hlt, fun p hp32 => ?_⟩
  have hk : 1677 + p ∈ kTm := (by decide +kernel : ∀ p < 32, 1677 + p ∈ kTm) p hp32
  have hreg := holds_mem hF (mem_factsFrom (val := vP2 (vP1 (xE ent L g y))) hk)
  have hv' := hvals p (by rw [hl0]; exact hp32) (1677 + p) (by interval_cases p <;> rfl)
  rw [hreg, hw p hp32] at hv'
  rw [rd, List.getElem?_eq_getElem (by rw [hl0]; exact hp32)]
  exact hv'.symm

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

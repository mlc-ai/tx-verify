-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.WordsEv
public import Kernels.InklingRelDecode.Proof.Lib.LaneFold
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleOrder
import Kernels.InklingRelDecode.Proof.Softmax.Soft.OvAt
import Kernels.InklingRelDecode.Proof.Softmax.Soft.RescaleState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.MxInv
import Kernels.InklingRelDecode.Proof.Softmax.Soft.WinState
import Kernels.InklingRelDecode.Proof.Softmax.Soft.EntGlue
import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaExact
import Kernels.InklingRelDecode.Proof.Softmax.Data.LExact
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEntry
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Lemmas.Kernel.FrameU

/-! # The rescale store of a valid row writes its factor times the loaded words

The words of the store of pc 2328 are the rescale factor of the round (`stepAlpha` of the fold's
state and block) times the words of the accumulator load of the round. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem site_2328 (s : Site) (h : s.pc = 2328) : s = .stO := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The rescale store writes the fold's factor times the words of the load.** -/
public theorem rescale_ev {m : Mem0} {X : Execution} {k a : Nat} {vals : List Value}
    {sh : TcShape} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X)
    (lane : g % L.block < 128) (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block)))
    (hov : ∀ j a' ov sh', X.get (g, j) = some ⟨2260, .tc (.ld a' ov sh')⟩ →
      ∀ x ∈ ov, ∃ r : ℝ, x = .float .f32 r)
    (get : X.get (g, k) = some ⟨2328, .tc (.st a vals sh)⟩) {kl a' ov sh'}
    (hl : X.get (g, kl) = some ⟨2260, .tc (.ld a' ov sh')⟩)
    (hr : pollRound 1257 ((X.tr g).take kl) = pollRound 1257 ((X.tr g).take k)) {jj : Nat}
    (hj : jj < vals.length) :
    ∃ x : ℝ, ov[jj]? = some (.float .f32 x) ∧ vals[jj]? = some (.float .f32
      (Lib.SoftRow.stepAlpha (Q.scale * log2eF32)
        (Lib.laneBlk Q L g (pollRound 1257 ((X.tr g).take k) - 1))
        (Lib.laneSt Q L g (pollRound 1257 ((X.tr g).take k) - 1)) * x)) := by
  have clean : ∀ f, (Event.mk 2328 (.tc (.st a vals sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, t, ins, u, hsc, -, inv, atpc, -, -⟩ := softmax_event_entry hp hX hf get
    clean (by show 574 < 2328; omega) (by show 2328 < 2331; omega)
  obtain ⟨s, hs, hse⟩ := value_state hsc
  obtain ⟨y, hy, rfl⟩ := softD_shape hse
  have hg := Frame.lt_of_get hX get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  have site : y.c.site = .stO := by
    refine site_2328 _ ?_
    have := atpc
    rw [← hy] at this
    exact this.symm
  obtain ⟨E, -, -, -⟩ := ent_glue hp hX hg len hsc
  obtain ⟨led, -, -, -⟩ := soft_win hp hX (hB g) k len _ hs nub w ent y n rfl inv.entry E
  have M := soft_mex hp hX (words_ev hp hX hf hB hS lane hv) k len _ hs nub w ent y n rfl inv.entry
  have O := soft_ov hp hX k len _ hs nub w ent y n rfl inv.entry
  obtain ⟨k', a2, sh2, hk', hg2, hpr⟩ := O.ev (by rw [site]; rfl)
  have led' : pollRound 1257 ((X.tr g).take k) = y.c.i + 1 := by
    have := led
    simpa only [Led, site, Site.afterS, Bool.toNat_true] using this
  have hpr' : pollRound 1257 ((X.tr g).take k') = y.c.i + 1 := hpr
  have kk : kl = k' := by
    have h1 : pollRound 1257 ((X.tr g).take k') = pollRound 1257 ((X.tr g).take kl) := by
      omega
    rcases lt_trichotomy kl k' with h | h | h
    · have := ld_rounds hp hX hg2 kl h _ hl
      try dsimp only at this
      omega
    · exact h
    · have := ld_rounds hp hX hl k' h _ hg2
      omega
  subst kk
  have hev := Option.some.inj (hl.symm.trans hg2)
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hev
  obtain ⟨-, -, hovy, -⟩ := hev
  subst hovy
  obtain ⟨t', ins', o, ht, -, hc, fire⟩ := Frame.fired_siteU (fun g h => threadD_sound hp h) hX get
    hs (fun f h => by cases h)
  change (Data.codeS ent L g).AtD y t' at ht
  change kernel.code[y.c.site.pc]? = some ins' at hc
  change Fires y.c.site.pc (eventTmpl Assumptions.all L g t' ins'.op) _ o at fire
  obtain ⟨hl64, hwords⟩ := rs_site_words ht hc fire site
  have hlen := O.len (by rw [site]; rfl)
  have jlt : jj < 64 := by omega
  have jm : jj < y.v.ov.length := by omega
  obtain ⟨r, hr'⟩ := hov kl a' y.v.ov sh' hl _ (List.getElem_mem jm)
  have e1 : y.v.ov.getD jj (b32 0) = .float .f32 r := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem jm]
    exact hr'
  have hpos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  have a0 : updS y.c.site = false := by rw [site]; rfl
  have a1 : afterW y.c.site = true := by rw [site]; rfl
  have jm0 := M.m
  simp only [a0, Bool.toNat_false, Nat.add_zero] at jm0
  obtain ⟨-, -, hal⟩ := alpha_exact (scaleW_ev hp) hpos jm0 (M.mx a1)
  refine ⟨r, by rw [List.getElem?_eq_getElem jm, hr'], ?_⟩
  rw [hwords jj jlt, e1]
  have hrd : Rd (alphaWord (scaleW L) y.v.m y.v.mx) _ := hal
  rw [mulE_reads hrd (readEReal_float r) (mulEReal_coe _ r), erealValue_coe]
  simp only [okVal, led', Nat.add_sub_cancel]
  rfl

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

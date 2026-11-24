-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftF16
public import Kernels.FlashAttn4Fwd.Proof.Interface.TcMmaThread

@[expose] public section

/-! # The softmax probability stores write packed half-precision pairs

A `tcgen05.st` stores its source registers' values (`fires_tcSt_vals`), and at a store site every
source register holds a packed pair of half-precision values (`Softmax.pst_pairs_*`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The source registers of every store site hold packed half-precision pairs, when the scale
word reads as a number and the reference and the words are single-precision payloads. -/
theorem pst_pairs {g : Nat} {d : Softmax.D} {t : TState} {ta : Nat} {ss : List Opnd} {lp : Bool}
    {c : Fin 4} (hsc : Softmax.ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : Softmax.WordsF32 d.w) (hs : d.site = .pst lp c) (h : Holds t.regs (Softmax.facts L g d))
    (hc : kernel.code[(Softmax.Site.pst lp c).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r x y, ss[p]? = some (.reg r) ∧
      t.regs r = some (.pair (.float .f16 x) (.float .f16 y)) := by
  cases lp <;> rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
  · exact Softmax.pst_pairs_0 hsc hm hwf hs h hc
  · exact Softmax.pst_pairs_1 hsc hm hwf hs h hc
  · exact Softmax.pst_pairs_2 hsc hm hwf hs h hc
  · exact Softmax.pst_pairs_3 hsc hm hwf hs h hc
  · exact Softmax.pst_pairs_4 hsc hm hwf hs h hc
  · exact Softmax.pst_pairs_5 hsc hm hwf hs h hc
  · exact Softmax.pst_pairs_6 hsc hm hwf hs h hc
  · exact Softmax.pst_pairs_7 hsc hm hwf hs h hc

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **Every load of a softmax thread before event `i` returned 32 single-precision numbers**, when
each returned single-precision floats. -/
theorem soft_loadsF32_of {h i : Nat} (hw : warpOf L h < 8)
    (hld : ∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (h, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    Softmax.LoadsF32 ((X.tr h).take i) := by
  intro x hx pc a vals hxe
  subst hxe
  obtain ⟨j, hj, hget⟩ := get_of_mem_take hx
  exact ⟨(soft_tld hpre hX ht hw hget).choose_spec.choose_spec.choose_spec.2.2.2.2.2,
    hld j hj pc a vals hget⟩

/-- **At a softmax store site, after single-precision loads, the reference and the words are
single-precision payloads.** -/
theorem pst_f32 {h i : Nat} {d : Softmax.D} {lp : Bool} {c : Fin 4} (hw : warpOf L h < 8)
    (hc : Softmax.Counts L h d ((X.tr h).take i)) (hs : d.site = .pst lp c)
    (hld : ∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (h, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    (∃ x, d.m = .float .f32 x) ∧ Softmax.WordsF32 d.w := by
  have hF := soft_loadsF32_of hpre hX ht hw hld
  obtain ⟨hH, hR⟩ := hc.refs hF (Softmax.scale_ok hpre)
  refine ⟨?_, Softmax.words_f32 hc.words hF (by simp [Softmax.chunks, hs])⟩
  cases lp
  · exact ⟨_, hH (by rw [hs]; rfl)⟩
  · exact ⟨_, (hR (.inl (by rw [hs]; rfl))).1⟩

/-- **`TcMmaThreadFacts.soft_f16`**: a softmax store writes packed pairs of half-precision
values, once the thread's earlier loads returned single-precision floats. -/
theorem TcMmaThreadFacts_soft_f16 {h i a : Nat} {vals : List Value} (_hh : h < L.threads)
    (hw : warpOf L h < 8) (he : X.TSt (h, i) a vals .s32x32b)
    (hld : ∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (h, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    ∀ v ∈ vals, ∃ x y : ℝ, v = .pair (.float .f16 x) (.float .f16 y) := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨-, -, -, -, -, -, -, -, hl⟩ := soft_tst hpre hX ht hw he
  obtain ⟨d, t, ins, o, -, hc, -, hat, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  intro v hv
  obtain ⟨p, hp, hvp⟩ := List.getElem_of_mem hv
  cases hsd : d.site with
  | pst lp c =>
    obtain ⟨⟨xm, hm⟩, hwf⟩ := pst_f32 hpre hX ht hw hc hsd hld
    obtain ⟨ta, ss, hcd, -⟩ := pst_len lp c
    rw [hsd] at hcode hf
    obtain rfl := Option.some.inj (hcode.symm.trans hcd)
    obtain ⟨r, x, y, hs, hr⟩ :=
      pst_pairs (Softmax.scale_ok hpre) hm hwf hsd hat.2.2.2.2 hcd p (by omega)
    have := fires_tcSt_vals (fun _ h => by cases h) hf rfl hs hr
    rw [List.getElem?_eq_getElem hp, hvp] at this
    exact ⟨x, y, Option.some.inj this⟩
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof

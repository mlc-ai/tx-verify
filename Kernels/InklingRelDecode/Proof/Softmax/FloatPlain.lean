-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.FloatRules
public import Kernels.InklingRelDecode.Proof.Lib.FloatPlain3
public import Lemmas.Flow.SegQF
public import Kernels.InklingRelDecode.Gen.TypedSoftmax
import Lemmas.Flow.SegQFCtl
import Kernels.InklingRelDecode.Gen.TypedLateLane00
import Kernels.InklingRelDecode.Gen.TypedLateLane01
import Kernels.InklingRelDecode.Gen.TypedLateLane02
import Kernels.InklingRelDecode.Gen.TypedLateLane03
import Kernels.InklingRelDecode.Gen.TypedLateLane04
import Kernels.InklingRelDecode.Gen.TypedLateLane05
import Kernels.InklingRelDecode.Gen.TypedLateLane06
import Kernels.InklingRelDecode.Gen.TypedLateLane07
import Lemmas.Flow.F32DatTag

@[expose] public section

/-! # What the typed float windows of the Softmax warp need of the assumptions

`FloatPlain Assumptions.all L g a b` (`Lemmas/Flow/TypedAllF.lean`) for a stretch inside the
Softmax pcs 1299 to 1837, which holds none of the software `exp2` sites (pcs 1913 and above) and
none of the single-instruction readings (pcs 600, 807, 2562). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.Lib

variable {L : Launch} {g : Nat} {t : TState}

private theorem emu_free {pc : Nat} (ha : 1299 ≤ pc) (hb : pc < 1838) :
    Assumptions.emuSites.contains pc = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, he⟩ := h
  omega

private theorem form_none {op : Op} (h : PlainOp op) :
    FloatForm.ofOp op = none ∧ ApproxForm.ofOp op = none := by
  rcases h with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩
  · simp [FloatForm.ofOp, ApproxForm.ofOp]
  · simp [FloatForm.ofOp, ApproxForm.ofOp]
  · simp [FloatForm.ofOp, ApproxForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, hd]

private theorem plain_none (ha : 1299 ≤ t.pc) (hb : t.pc < 1838) {op : Op} (h : PlainOp op) :
    ∀ x ∈ Assumptions.all, x.localRule L g t op = none := by
  obtain ⟨hf, hap⟩ := form_none h
  intro x hx
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | hx
  · exact idealReal_localRule_none fun f hf' => by simp [hf] at hf'
  · exact approxExact_localRule_none fun f hf' => by simp [hap] at hf'
  by_cases hc : ∃ c, op = .cvt c
  · obtain ⟨c, rfl⟩ := hc
    obtain ⟨c', k, w, h', hd⟩ := h.resolve_left (by simp) |>.resolve_left (by simp)
    obtain rfl : c = c' := by simpa using h'
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
        Assumptions.negExact, Assumptions.bf16Exact, hd]
  · exact other_rules_none (by omega) (by omega) (by omega) (fun c hc' => hc ⟨c, hc'⟩) x
      (by simp only [Assumptions.all, List.drop_succ_cons, List.drop_zero, List.mem_cons,
        List.not_mem_nil, or_false]; exact hx)

private theorem decline_fma2 (h : Assumptions.emuSites.contains t.pc = false)
    (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600) (h3 : t.pc ≠ 807) :
    DeclineAt Assumptions.all .fmaRnF32x2 L g t := by
  intro op hf hn
  rw [(segFree h).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ Assumptions.all.drop 2
  · refine other_rules_none h1 h2 h3 (fun c hc => ?_) a hd
    subst hc
    simp only [FloatForm.ofOp] at hf
    split_ifs at hf <;> simp at hf
  · simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
      List.drop_succ_cons, List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs
      · exact hn
      · rfl
    · exact approxExact_localRule_none fun f' h' => by
        rw [approxForm_none_of_float hf] at h'; cases h'
    · exact absurd ha' hd

/-- The first assumption that takes `cvt.f32.bf16` is the exact reading of `bf16Exact`. -/
private theorem widen_find {d r : Nat} :
    Assumptions.all.findSome? (fun a => a.localRule L g t (.cvt (widenBfC d (.reg r)))) =
      execWidenBf t d (.reg r) := by
  have hb : Assumptions.bf16Exact.localRule L g t (.cvt (widenBfC d (.reg r))) =
      execWidenBf t d (.reg r) := by
    simp [Assumptions.bf16Exact, widenBfC, CvtInstr.plain, execWidenBf]
  have h1 : Assumptions.idealArith.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.idealArith, Assumption.idealReal, FloatForm.ofOp, widenBfC,
      CvtInstr.widenF16?, CvtInstr.packF16?]
  have h2 : Assumptions.approx.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.approx, Assumption.approxExact, ApproxForm.ofOp]
  have h4 : Assumptions.lg2Exact.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.lg2Exact]
  have h5 : Assumptions.divFullExact.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.divFullExact]
  have h6 : Assumptions.negExact.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.negExact]
  have h3 : (Assumptions.swExp2 kernel).localRule L g t (.cvt (widenBfC d (.reg r))) = none := rfl
  simp only [Assumptions.all, List.findSome?_cons, h1, h2, h3, h4, h5, h6, hb]
  cases execWidenBf t d (.reg r) <;> rfl

/-- **The Softmax warp's pcs 1299 to 1837 are plain for the typed float family.** -/
theorem floatPlain {a b : Nat} (ha : 1299 ≤ a) (hb : b ≤ 1838) :
    FloatPlain Assumptions.all L g a b where
  shape t h1 h2 op hop x hx := plain_none (by omega) (by omega) hop x hx
  segs pc h1 h2 := segFree (emu_free (by omega) (by omega))
  ideal t h1 h2 :=
    have he := emu_free (pc := t.pc) (by omega) (by omega)
    ⟨⟨ideal_at (by simp) he, decline_at (by simp) he (by omega) (by omega) (by omega)⟩,
      ⟨idealAt_head (by decide) (segFree he).tail,
        decline_fma2 he (by omega) (by omega) (by omega)⟩⟩
  widen t h1 h2 d r :=
    have he := emu_free (pc := t.pc) (by omega) (by omega)
    have hw := widen_find (L := L) (g := g) (t := t) (d := d) (r := r)
    ⟨fun e h => by
      rw [(segFree he).exec rfl, execLocalRule, hw, h],
     fun h => by
      rw [(segFree he).exec rfl, execLocalRule, hw, h]⟩
  bra t x target uni hx := by
    simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact idealReal_localRule_none fun f hf => by simp [FloatForm.ofOp] at hf
    · exact approxExact_localRule_none fun f hf => by simp [ApproxForm.ofOp] at hf
    all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
      Assumptions.negExact]

/-- **The pilot**: the Softmax warp's window from `tmemWait_1` to `shfl_5` (pcs 1299 to 1838, 539
instructions, both branches falling through) is a strict segment under the generated tags. -/
theorem softmax_window {F G : List (Nat × Value)} (hW : ∀ p ∈ G, p.1 ∉ Gen.Typed.sm1_wr)
    (hG : ∀ p ∈ G, p ∈ F)
    (hB1 : ∀ u, At u 1302 G → QTF Gen.Typed.sm1_qt u → u.regs 96 = some (.pred false))
    (hB2 : ∀ u, At u 1466 G → QTF Gen.Typed.sm1_qt u → u.regs 97 = some (.pred false)) :
    SegQ kernel Assumptions.all L g (QTF Gen.Typed.sm1_qt) 1299 F 1838 G :=
  Gen.Typed.sm1 (floatPlain (by omega) le_rfl) hW hG hB1 hB2

end PTX.Kernels.InklingRelDecode.Proof.Softmax

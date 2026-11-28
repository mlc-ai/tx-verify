-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Base
public import Kernels.InklingRelDecode.Proof.Softmax.LateDiv
public import Lemmas.Flow.SegQFH
import Lemmas.Flow.Recip
import Kernels.InklingRelDecode.Proof.Lib.RoundWords
import Lemmas.Flow.TypedDeclI
import Kernels.InklingRelDecode.Flow.Code.Part009

@[expose] public section

/-! # The pieces of the setup between the generated windows: the division at pc 600

The window before pc 600 leaves the divisor and the dividend as words of four bytes only, so the
division is a piece of its own: the dividend is the constant `1.0` (register 804, an exact fact of
the span) and the divisor the scale register (525, a launch constant). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- **The division at pc 600 is a strict segment**: `1.0 / scale` is a datum of four bytes. -/
theorem seg_div {R : TState → Prop} {y : ℝ} (hy : valFloat .f32 (scaleVal L) = .ok y)
    (h0 : y ≠ 0) {F G : List (Nat × Value)} (h4 : (804, b32 1065353216) ∈ F)
    (h5 : (525, scaleVal L) ∈ F) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ 805) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g R) 600 F 601 G := by
  refine SegQ.local1 Flow.code_600 rfl hG fun t ht hq => ?_
  obtain ⟨hpc, -, -, -, hR⟩ := ht
  have e4 : t.regs 804 = some (b32 1065353216) := holds_mem hR h4
  have e5 : t.regs 525 = some (scaleVal L) := holds_mem hR h5
  obtain ⟨v, hex, hdv⟩ := Softmax.divFull_step (L := L) (g := g) hpc (OpndIs.reg e4)
    (OpndIs.reg e5) (valFloat_one) hy h0
  obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := 805) (tg := .dat32) ⟨v, rfl, hdv⟩
  refine ⟨_, hex, by simp [PTX.next, setReg, hpc], rfl, rfl, rfl,
    fun p hp => by simp [setReg, PTX.next, hd p hp], fun hu => ⟨?_, ?_⟩⟩
  · exact QTF.after1 (outs := [(805, .dat32)]) hq.1 hpc
      (by simp [PTX.next, setReg, hpc]) hw1 hw2 (by decide +kernel)
  · exact fun w hw => hq.2 w (.head hu hw)

/-- **The launch of dependent grids at pc 2561** changes nothing, and neither do the tags. -/
theorem seg_launch {R : TState → Prop} {F G : List (Nat × Value)} (hG : ∀ p ∈ G, p ∈ F) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g R) 2561 F 2562 G := by
  refine SegQ.local1 Flow.code_2561 rfl hG fun t ht hq => ?_
  have hn : execLocalA Assumptions.all L g t (.misc (.gridDep false)) = .ok (PTX.next t) := by
    have hseg : SegFreePc Assumptions.all t.pc :=
      Kernels.InklingRelDecode.Proof.segFree (by rw [ht.1]; decide +kernel)
    rw [hseg.exec rfl, execLocalRule_of_none]
    · rfl
    · intro a ha
      have hx2 : a = Assumptions.all[0] ∨ a = Assumptions.all[1] ∨ a ∈ Assumptions.all.drop 2 := by
        simpa [Assumptions.all] using ha
      rcases hx2 with rfl | rfl | hd
      · exact idealReal_localRule_none fun f hf => by simp [FloatForm.ofOp] at hf
      · exact approxExact_localRule_none fun f hf => by simp [ApproxForm.ofOp] at hf
      · exact Lib.other_rules_none (op := .misc (.gridDep false)) (by rw [ht.1]; decide)
          (by rw [ht.1]; decide)
          (by rw [ht.1]; decide) (fun c hc => nomatch hc) a hd
  refine ⟨_, hn, by simp [PTX.next, ht.1], rfl, rfl, rfl, fun _ _ => rfl, fun hu => ⟨?_, ?_⟩⟩
  · exact QTF.after1 (outs := []) hq.1 ht.1 (by simp [PTX.next, ht.1]) (fun _ _ => rfl)
      (fun _ h => nomatch h) (by decide +kernel)
  · exact fun w hw => hq.2 w (.head hu hw)

/-- **The single pieces under the lane's fact**: the pieces of `single_step` where the fact is the
lane's `LateR'`. -/
theorem single_late {pc : Nat} (hk : lateOk pc = true) :
    SingleStep kernel Assumptions.all L g (LateR' L g) pc :=
  fun op nd hc hn t hpc hT hR => single_step hk op nd hc hn t hpc hT hR.1

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict

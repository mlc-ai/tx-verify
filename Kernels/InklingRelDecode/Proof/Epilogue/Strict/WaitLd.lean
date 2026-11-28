-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Wait
import Kernels.InklingRelDecode.Flow.Code.Part041
import Lemmas.Flow.Async
import Kernels.InklingRelDecode.Gen.TypedLateLane06

@[expose] public section

/-! # The strict step of the wait for the accumulator load (pc 2608)

The windows of the scaled row (2609 to 2673), the last product, and the row store gate. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt PTX.Kernels.InklingRelDecode.Gen.TypedLate06

set_option maxRecDepth 100000

variable {e : Entry} {L : Launch} {g : Nat} {v : Value} {R : TState → Prop} {Wf : Event → Prop}
local notation "F" => facts e L g v
local notation "Lane" => (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t)

/-- The side conditions of a window from the facts of `a` to those of `b`. -/
theorem fw {a b : Nat} {wr : List Nat} (hw : ∀ r ∈ ctlLive b, r ∉ wr)
    (hs : ∀ r ∈ ctlLive b, r ∈ ctlLive a) :
    (∀ p ∈ F b, p.1 ∉ wr) ∧ ∀ p ∈ F b, p ∈ F a := by
  refine ⟨fun p hp => ?_, fun p hp => fsub (v := v) hs p hp⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  exact hw r hr

theorem singles_of {l : List Nat} (h : ∀ pc ∈ l, 2642 ≤ pc ∧ pc ≤ 2673) :
    ∀ pc ∈ l, epiS pc = true := fun pc hp => by
  have := h pc hp
  simp only [epiS, Bool.and_eq_true, decide_eq_true_eq]
  exact this

/-- **The windows of the scaled row**, from the wait to the last product. -/
theorem scaled_row (hS : ∀ pc, epiS pc = true → SingleStep kernel Assumptions.all L g R pc) :
    SegQ kernel Assumptions.all L g Lane 2609 (F 2608) 2673 (F 2673) := by
  obtain ⟨w1, g1⟩ := fw (v := v) (e := e) (L := L) (g := g) (a := 2608) (b := 2649)
    (wr := l06_2609_wr) (by decide +kernel) (by decide +kernel)
  obtain ⟨w2, g2⟩ := fw (v := v) (e := e) (L := L) (g := g) (a := 2649) (b := 2657)
    (wr := l06_2649_wr) (by decide +kernel) (by decide +kernel)
  obtain ⟨w3, g3⟩ := fw (v := v) (e := e) (L := L) (g := g) (a := 2657) (b := 2665)
    (wr := l06_2657_wr) (by decide +kernel) (by decide +kernel)
  obtain ⟨w4, g4⟩ := fw (v := v) (e := e) (L := L) (g := g) (a := 2665) (b := 2673)
    (wr := l06_2665_wr) (by decide +kernel) (by decide +kernel)
  have s1 : SegQ kernel Assumptions.all L g Lane 2609 (F 2608) 2649 (F 2649) :=
    lw_l06_2609 (R := R) (fp3_epi (by decide +kernel)) w1 g1
      (fun pc hp => hS pc (singles_of (by decide) pc hp)) (fun _ h => nomatch h)
  have s2 : SegQ kernel Assumptions.all L g Lane 2649 (F 2649) 2657 (F 2657) :=
    lw_l06_2649 (R := R) (fp3_epi (by decide +kernel)) w2 g2
      (fun pc hp => hS pc (singles_of (by decide) pc hp)) (fun _ h => nomatch h)
  have s3 : SegQ kernel Assumptions.all L g Lane 2657 (F 2657) 2665 (F 2665) :=
    lw_l06_2657 (R := R) (fp3_epi (by decide +kernel)) w3 g3
      (fun pc hp => hS pc (singles_of (by decide) pc hp)) (fun _ h => nomatch h)
  have s4 : SegQ kernel Assumptions.all L g Lane 2665 (F 2665) 2673 (F 2673) :=
    lw_l06_2665 (R := R) (fp3_epi (by decide +kernel)) w4 g4
      (fun pc hp => hS pc (singles_of (by decide) pc hp)) (fun _ h => nomatch h)
  exact s1.comp (s2.comp (s3.comp s4))

/-- The last product of the row. -/
theorem last_mul (hS : ∀ pc, epiS pc = true → SingleStep kernel Assumptions.all L g R pc) :
    SegQ kernel Assumptions.all L g Lane 2673 (F 2673) 2674 (F 2674) :=
  segQ_single (qt := lateQt) (R := R) (d := 2479) Flow.code_2673 (by decide +kernel)
    (hS 2673 (by decide)) (fun p hp => fsub (v := v) (by decide +kernel) p hp) (fun p hp h => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      exact (by decide +kernel : ∀ r ∈ ctlLive 2674, r ≠ 2479) r hr h)

/-- **The strict step of the wait for the accumulator load**. -/
theorem sstep_waitLd (hS : ∀ pc, epiS pc = true → SingleStep kernel Assumptions.all L g R pc)
    (ev : Event) : (code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) Wf
      ⟨.waitLd, v⟩ ev :=
  adv_gen (s' := firstStore e.valid (lead (g % L.block))) (p := 2608) rfl Flow.code_2608
    (fires_async_next trivial) (fun _ => rfl) (fun _ => first_inv ..)
    (by decide +kernel) ((scaled_row hS).comp ((last_mul hS).comp store_gate_seg)) ev

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict

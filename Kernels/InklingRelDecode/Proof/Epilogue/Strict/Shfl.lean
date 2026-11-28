-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Gate
public import Kernels.InklingRelDecode.Proof.Lib.LaneStrict
public import Lemmas.Flow.StepsQFO
import Kernels.InklingRelDecode.Flow.Code.Part040

@[expose] public section

/-! # The strict step of the lane shuffle (pc 2603) and the span to the load (2604 to 2607)

The received word is a 32-bit word `b32 x` (the well-formedness of the event); the base word of the
entry is `b32 0` (`Iface.BaseRead`), so the three words of the span are computed. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Control
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

/-- The entry with the base word of the prologue. -/
abbrev eb (e : Entry) : Entry := {e with base := b32 0}

variable {e : Entry} {L : Launch} {g x : Nat}
local notation "F" => facts (eb e) L g (b32 x)

theorem c_shl : Value.bits 32
    (if (truncBits 32 (BitVec.ofInt 64 21)).toNat ≥ 32 then 0
    else truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) <<<
      (truncBits 32 (BitVec.ofInt 64 21)).toNat)) = valueOf (eb e) L g (b32 x) 1829 := by
  have h21 : (truncBits 32 (BitVec.ofInt 64 21)).toNat = 21 := by decide
  rw [h21]
  simp only [valueOf, scalarValue]
  simp
  exact Lib.shift_lane_word (b32 x)

theorem c_mask : Value.bits 32
    (truncBits 32 (BitVec.ofNat 64 ((Lib.word (b32 x)).toNat * 2 ^ 21 % 2 ^ 32)) &&&
      truncBits 32 (BitVec.ofInt 64 6291456)) = valueOf (eb e) L g (b32 x) 1830 := by
  rw [Lib.mask_bits]
  simp [valueOf]

theorem c_sum : Value.bits 32
    (truncBits 32 (truncBits 32 (BitVec.ofNat 64 ((Lib.word (b32 x)).toNat % 4 * 2 ^ 21)) +
      truncBits 32 (BitVec.ofNat 64 (((Lib.word (b32 0)).toNat + 256) % 2 ^ 32)))) =
    valueOf (eb e) L g (b32 x) 1827 := by
  rw [Lib.sum_bits]
  have h1 : Lib.addBase (b32 0) 256 = b32 256 := by simpa using Lib.addBase_bits 0 256
  simp only [valueOf, scalarValue]
  simp only [eb, h1]
  rw [ite_true]
  have h2 : ∀ d, Lib.addBase (b32 256) d = b32 ((256 + d) % 2 ^ 32) := fun d => by
    simpa using Lib.addBase_bits 256 d
  have h0 : (Lib.word (b32 0)).toNat = 0 := by decide
  rw [h2, h0]
  congr 1
  omega

theorem shfl_head : Seg kernel Assumptions.all L g 2 2604 (F 2604) 2606 (F 2606) := by
  have a : Seg kernel Assumptions.all L g 1 2604 (F 2604) 2605 (F 2605) := by
    intro t ht; seg_fp ht using exact c_shl
  have b : Seg kernel Assumptions.all L g 1 2605 (F 2605) 2606 (F 2606) := by
    intro t ht; seg_fp ht using exact c_mask
  exact a.comp b

theorem shfl_last : Seg kernel Assumptions.all L g 1 2606 (F 2606) 2607 (F 2607) := by
  intro t ht; seg_fp ht using exact c_sum

theorem shfl_ok : epiOk 2604 2606 = true ∧
    checkF absF5 lateQt 2604 2606 [] [] ((kernel.code.drop 2604).take (2606 - 2604)) = true := by
  decide +kernel

theorem shfl_last_ok : epiOk 2606 2607 = true ∧
    frameB ((kernel.code.drop 2606).take 1) ((lateQt 2607).map Prod.fst) = true ∧
    tagsInF (lateQt 2607) (lateQt 2606) = true := by
  decide +kernel

/-- **The span from the shuffle to the load**: the three words of the lane field. -/
theorem shfl_span : SegQ kernel Assumptions.all L g (QTF lateQt) 2604 (F 2604) 2607 (F 2607) :=
  (segQF_of_seg_typed lateQt (Ft := []) (n := 2) shfl_head rfl (by decide)
    (by have := kernel_code_length; omega) (absF5_sound (fp3_epi shfl_ok.1))
    (factTags_of_B (by rfl)) shfl_ok.2).comp
  (SegQF.of_seg_frame Lib.rulesFrame shfl_last rfl (by have := kernel_code_length; omega)
    (by decide) (fp3_epi (L := L) (g := g) shfl_last_ok.1).plain.plain.segs shfl_last_ok.2.1
    shfl_last_ok.2.2)

variable {v : Value} {R : TState → Prop} {Wf : Event → Prop}

theorem word_other (w : Value) {r : Nat} (hr : r ∈ ctlLive 2603) :
    valueOf e L g w r = valueOf e L g v r := by
  have ks : ∀ x ∈ ctlLive 2603, x ≠ 1827 ∧ x ≠ 1828 ∧ x ≠ 1829 ∧ x ≠ 1830 := by decide +kernel
  obtain ⟨a, b, c, d⟩ := ks r hr
  simp only [valueOf, a, b, c, d, ↓reduceIte]

/-- The span after the shuffle, from the facts of the shuffle site and the received word. -/
theorem shfl_from (hb : e.base = b32 0) : SegQ kernel Assumptions.all L g
    (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t) 2604
    ((1828, b32 x) :: facts e L g v 2603) 2607 (facts e L g (b32 x) 2607) := by
  have he : eb e = e := by
    show ({e with base := b32 0} : Entry) = e
    rw [← hb]
  have span := shfl_span (e := e) (L := L) (g := g) (x := x)
  rw [he] at span
  refine SegQ.laneConv R ?_ (fun _ h => h) span
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  have cov : ∀ r ∈ ctlLive 2604, r = 1828 ∨ r ∈ ctlLive 2603 := by decide +kernel
  rcases cov r hr with rfl | hm
  · exact List.mem_cons_self ..
  · refine List.mem_cons_of_mem _ ?_
    rw [word_other (v := v) (b32 x) hm]
    exact mem_factsFrom hm

/-- **The strict step of the lane shuffle**: the received word is a 32-bit word. -/
theorem sstep_shfl (hb : e.base = b32 0)
    (hW : ∀ ev, Wf ev → ev.pc = 2603 → ∀ m av bv cv recv ok,
      ev.kind = .shfl m av bv cv recv ok → ∃ x, recv = b32 x) (ev : Event) :
    (code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g R) Wf ⟨.shfl, v⟩ ev := by
  refine Code.shflOneFP (C := code e L g) (d := ⟨.shfl, v⟩) (f := fun w => ⟨.load, w⟩)
    (Pv := fun w => ∃ x, w = b32 x) (tr := .old (.bits 32)) Flow.code_2603 ?_ hW ?_ ?_ rfl rfl
    (by change afterF lateQt 2603 _ = true; decide +kernel) ?_ ev
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact (by decide +kernel : ∀ r ∈ ctlLive 2603, r ≠ 1828) r hr
  · rintro w ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · intro m av bv cv recv ok _
    rfl
  · rintro w ⟨x, rfl⟩
    exact ⟨rfl, rfl, trivial, shfl_from hb⟩

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict

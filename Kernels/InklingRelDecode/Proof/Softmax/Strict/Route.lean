-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Loop
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Pieces
public import Lemmas.Flow.SegQFBraS
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Vals
import Kernels.InklingRelDecode.Gen.TypedLateLane06
import Kernels.InklingRelDecode.Gen.TypedLate06
import Kernels.InklingRelDecode.Flow.Code
@[expose] public section
/-! # The loop's route: from the test at pc 1050 to the site of the next state -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The facts of a table are not about a register that neither the data nor the table names. -/
theorem rf_ne {D : List (Nat × Value)} {K : List Nat} {V : Nat → Value} {x : Nat}
    (hD : ∀ p ∈ D, p.1 ≠ x) (hK : ∀ r ∈ K, r ≠ x) : ∀ p ∈ D ++ factsFrom K V, p.1 ≠ x := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hD p h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact hK r hr

/-- The test of pc 2560: the number of blocks as a signed word is below one. -/
theorem cmp_blocks (n : Nat) (hn : n < 2 ^ 32) :
    compare Cmp.lt IType.s 32 (truncBits 32 (BitVec.ofNat 64 n))
      (truncBits 32 (BitVec.ofInt 64 1)) = decide (n = 0 ∨ 2 ^ 31 ≤ n) := by
  have h1 : BitVec.ofInt 64 1 = BitVec.ofNat 64 1 := rfl
  rw [h1]
  simp only [compare, Lib.toSigned32_ofNat, Nat.reduceMod, Nat.reducePow,
    Nat.reduceLT, ↓reduceIte, Nat.cast_one, decide_eq_decide]
  split_ifs <;> omega

theorem val_173 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 173 = .pred (decide (e.blocks = 0 ∨ 2 ^ 31 ≤ e.blocks)) := by
  simp [Control.valueOf, Control.scalarValue]

theorem val_1760 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 1760 = b32 0 := by
  simp [Control.valueOf, Control.scalarValue]

/-- The facts of the data at the loop's head, with the table of `pc` at the counters `j`. -/
noncomputable abbrev RF (e : Control.Entry) (L : Launch) (g : Nat) (m : Value) (j : Nat)
    (v : Control.Carry) (pc : Nat) : List (Nat × Value) :=
  [(498, Data.scaleW L), (1914, m)] ++ factsFrom (Control.ctlLive pc)
    (Control.valueOf e L g ⟨.arrive, j, v⟩)

/-- The test of pc 1050 holds: the branch goes to the epilogue's start. -/
theorem route_branch {j : Nat} {v : Control.Carry} (m : Value) (hz : j = e.limit) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1050
      (RF e L g m j v 1050) 2560 (RF e L g m j v 1050) := by
  have h91 : (91, Value.pred true) ∈ factsFrom (Control.ctlLive 1050)
      (Control.valueOf e L g ⟨.arrive, j, v⟩) := by
    have : Control.valueOf e L g ⟨.arrive, j, v⟩ 91 = .pred true := by
      simp [Control.valueOf, Control.scalarValue, hz]
    exact this ▸ mem_factsFrom (by decide +kernel)
  exact SegQ.tauAll _ (SegQF.braPS (qt := lateQt) true Flow.code_1050
    (fun _ hR => holds_mem hR (List.mem_append_right _ h91)) (fun t _ ha => Lib.bra_rule t _ ha)
    (segFree (by decide)) (by decide +kernel))

/-- **The epilogue's start**: the span from the branch's target to the first poll. -/
theorem route_epi {j : Nat} {v : Control.Carry} (m : Value)
    (hb : e.blocks < 2 ^ 32) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2560
      (RF e L g m j v 2560) 2565 (RF e L g m j v 2565) := by
  refine SegQ.cut (m := 2561) ?_ ?_
  · refine SegQ.tauAll _ ?_
    simp only [RF, List.cons_append, List.nil_append]
    late_ctl 2560, 2561 using
      rw [val_173]; exact congrArg Value.pred (cmp_blocks _ hb)
  refine SegQ.cut (m := 2562) ?_ ?_
  · exact seg_launch (sub_facts (fun _ h => h) (by decide +kernel))
  refine SegQ.cut (m := 2563) ?_ ?_
  · exact segQ_single (d := 1759) Flow.code_2562 (by decide +kernel)
      (single_late (by decide +kernel)) (sub_facts (fun _ h => h) (by decide +kernel))
      (rf_ne (by simp) (by decide +kernel))
  · refine SegQ.tauAll _ ?_
    simp only [List.cons_append, List.nil_append]
    late_ctl 2563, 2565 using (rw [val_1760]; decide)
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Span
public import Lemmas.Flow.StepsQFO
import Kernels.InklingRelDecode.Proof.Lib.LaneField
import Kernels.InklingRelDecode.Gen.StepSoftmax15
import Kernels.InklingRelDecode.Flow.Code.Part019

@[expose] public section

/-! # The strict step of the warp broadcast before the score load (pc 1261)

The received word is a 32-bit word `b32 x` (`LWf.idx`), and the base word of the entry is `b32 0`
(`Iface.BaseRead`), so that the span to the load of the scores (1262 to 1265) is computed. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption Arith32
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem lane_506 (x : Nat) :
    truncBits 32 (if 32 ≤ (truncBits 32 21#64).toNat then 0#64
      else truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) <<< (truncBits 32 21#64).toNat)) &&&
      truncBits 32 6291456#64 =
    BitVec.ofNat 64 ((truncBits 32 (BitVec.ofNat 64 x)).toNat % 4 * 2097152) := by
  have h21 : (truncBits 32 21#64).toNat = 21 := by decide
  rw [h21]
  simp only [Nat.reduceLeDiff, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  have hm := Lib.and_lane x
  have hb : (x * 2097152 % 4294967296 &&& 6291456) ≤ 6291456 := Nat.and_le_right
  have hi : (6291456#64).toNat = 6291456 := by decide
  simp only [truncBits, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, hi]
  norm_num only [Nat.reducePow, Nat.reduceMod] at *
  have e1 : x % 18446744073709551616 % 4294967296 % 18446744073709551616 * 2097152 %
      18446744073709551616 % 4294967296 % 18446744073709551616 % 4294967296 %
      18446744073709551616 = x * 2097152 % 4294967296 := by omega
  rw [e1]
  have e3 : x % 18446744073709551616 % 4294967296 % 18446744073709551616 % 4 * 2097152 %
      18446744073709551616 = x % 4 * 2097152 := by omega
  rw [e3, ← hm]
  have : (x * 2097152 % 4294967296 &&& 6291456) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt this]

theorem add_1676 (Z A B : Nat) (hZ : Z = 0) (hB : B < 2 ^ 23) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 ((Z + A) % 4294967296)) +
      truncBits 32 (BitVec.ofNat 64 B)) =
    BitVec.ofNat 64 (((truncBits 32 (BitVec.ofNat 64 ((Z + A) % 4294967296))).toNat + B) %
      4294967296) := by
  subst hZ
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_add]
  omega

theorem val_506 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 506 = b32 ((Lib.word d.held.base).toNat % 4 * 2 ^ 21) := by
  simp [Control.valueOf]

theorem val_1676 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 1676 = Control.basePlus (Control.basePlus e.base (d.i % 2 * 128))
      ((Lib.word d.held.base).toNat % 4 * 2 ^ 21) := by
  simp [Control.valueOf]

/-- The closing tactic of the pointer arithmetic over the base word `b32 0`. -/
macro "late_ptr" : tactic => `(tactic| first
  | (rw [val_506]; simp [Lib.word, b32, Value.regBits]; exact lane_506 _)
  | (rw [val_1676]
     simp [Control.basePlus, Control.u32, Lib.word, b32, Value.regBits]
     apply add_1676 _ _ _ (by decide) (by omega)))

variable {L : Launch} {g : Nat}

/-- The facts of the span from the broadcast to the score load. -/
noncomputable abbrev bcF (L : Launch) (g : Nat) (e0 : Control.Entry) (w : Data.Vals)
    (x i : Nat) (v : Control.Carry) (pc : Nat) :
    List (Nat × Value) :=
  (498, Data.scaleW L) :: (1914, w.m) :: factsFrom (Control.ctlLive pc)
    (Control.valueOf {e0 with base := b32 0} L g ⟨.ldS, i, {v with base := b32 x}⟩)

theorem span_bcast_a (e0 : Control.Entry) (w : Data.Vals) (x i : Nat) (v : Control.Carry) :
    SegQ kernel Assumptions.all L g (QTF lateQt) 1262 (bcF L g e0 w x i v 1262) 1264
      (bcF L g e0 w x i v 1264) := by
  late_ctl 1262, 1265 using late_ptr

theorem span_bcast_b (e0 : Control.Entry) (w : Data.Vals) (x i : Nat) (v : Control.Carry) :
    SegQ kernel Assumptions.all L g (QTF lateQt) 1264 (bcF L g e0 w x i v 1264) 1265
      (bcF L g e0 w x i v 1265) := by
  late_ctl 1262, 1265 using late_ptr

/-- The span from the broadcast to the score load. -/
theorem span_bcast (e0 : Control.Entry) (w : Data.Vals) (x i : Nat) (v : Control.Carry) :
    SegQ kernel Assumptions.all L g (QTF lateQt) 1262 (bcF L g e0 w x i v 1262) 1265
      (bcF L g e0 w x i v 1265) :=
  (span_bcast_a e0 w x i v).comp (span_bcast_b e0 w x i v)

variable {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- The shuffle only changes the table words that depend on the received base. -/
theorem other_base (e : Control.Entry) (x : Value) {r : Nat} (hr : r ∈ Control.ctlLive 1262)
    (h : r ≠ 944) :
    Control.valueOf e L g ⟨.ldS, i, {v with base := x}⟩ r =
      Control.valueOf e L g ⟨.shfl4, i, v⟩ r := by
  have free : ∀ r ∈ Control.ctlLive 1262, r = 944 ∨ r ∉ [506, 944, 945, 1542, 1543, 1544, 1611,
      1676] := by decide +kernel
  have off := (free r hr).resolve_left h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at off
  obtain ⟨h1, h2, h3, h6, h7, h8, h4, h5⟩ := off
  simp only [Control.valueOf, h1, h2, h3, h6, h7, h8, h4, h5, ↓reduceIte]

/-- The warp broadcast before the score load (the entry's base word is `b32 0`). -/
theorem sstep_shfl4 (e0 : Control.Entry) (ev : Event) :
    (Data.code {e0 with base := b32 0} L g).StepForQP (QTF lateQt)
      (TauAll kernel Assumptions.all L g (LateR' L g)) LWf ⟨⟨.shfl4, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => Code.shflOneFP
    (C := Data.code {e0 with base := b32 0} L g)
    (d := ⟨⟨.shfl4, i, v⟩, w⟩) (f := fun r => ⟨⟨.ldS, i, {v with base := r}⟩, w⟩)
    (Pv := fun r => ∃ x, r = b32 x) (tr := .old (.bits 32)) Flow.code_1261 ?_ ?_
    (fun r ⟨x, hx⟩ => ⟨BitVec.ofNat 64 x, congrArg some hx⟩) (fun _ _ _ _ _ _ _ => rfl) rfl rfl
    (by change afterF lateQt 1261 _ = true; decide +kernel) ?_ ev
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact (by decide +kernel : ∀ r ∈ Control.ctlLive 1261, r ≠ 944) r hr
    · simp only [Data.dF, Data.dFS, Data.inRound] at h
      simp at h
      rcases h with rfl | rfl <;> simp
  · exact fun e he hpc m av bv cv recv ok hk => he.idx (Or.inl hpc) m av bv cv recv ok hk
  · rintro recv ⟨x, rfl⟩
    refine ⟨rfl, rfl, Control.body_inv hinv rfl rfl, ?_⟩
    have e1 : (Data.code {e0 with base := b32 0} L g).pc ⟨⟨.shfl4, i, v⟩, w⟩ = 1261 := by
      change Site.pc .shfl4 = 1261; decide +kernel
    have e2 : (Data.code {e0 with base := b32 0} L g).pc
        ⟨⟨.ldS, i, {v with base := b32 x}⟩, w⟩ = 1265 := by
      change Site.pc .ldS = 1265; decide +kernel
    rw [e1, e2]
    refine SegQ.laneConv _ (a := 1262) (b := 1265)
      (F' := (498, Data.scaleW L) :: (1914, w.m) :: factsFrom (Control.ctlLive 1262)
        (Control.valueOf {e0 with base := b32 0} L g ⟨.ldS, i, {v with base := b32 x}⟩))
      (G' := (498, Data.scaleW L) :: (1914, w.m) :: factsFrom (Control.ctlLive 1265)
        (Control.valueOf {e0 with base := b32 0} L g ⟨.ldS, i, {v with base := b32 x}⟩)) ?_ ?_ ?_
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact List.mem_cons_of_mem _ (List.mem_append_right _
          (by simp [Data.dF, Data.dFS, Data.inRound]))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _
          (by simp [Data.dF, Data.dFS, Data.inRound]))
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        by_cases h : r = 944
        · subst h
          exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
          rw [other_base _ _ hr h]
          exact mem_factsFrom (by
            have key : ∀ r ∈ Control.ctlLive 1262, r = 944 ∨ r ∈ Control.ctlLive 1261 := by
              decide +kernel
            exact (key r hr).resolve_left h)
    · intro p hp
      obtain h | h := List.mem_append.mp (ctl_out (w := w) (i := i) (v := {v with base := b32 x})
        .ldS (by decide +kernel : Site.pc .ldS = 1265) p hp)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      · simp [Data.dF, Data.dFS, Data.inRound] at h
        rcases h with rfl | rfl <;> simp
    · exact span_bcast e0 w x i v

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict

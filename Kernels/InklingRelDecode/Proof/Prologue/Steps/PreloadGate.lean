-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Divide
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyRoute
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockPointer
import Kernels.InklingRelDecode.Gen.StepPrologue
import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
import Lemmas.Flow.SegPieces
import Lemmas.Flow.IssueNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
local notation "F" => facts Q L g w d

theorem seg_gate_numerator : Seg kernel Assumptions.all L g 1 181 (F 180) 182 (F 182) := by
  intro t ht
  seg_fp ht using rfl

private theorem quotient {m} (hp : Pre Q L m) :
    SegU kernel Assumptions.all L g 182 (F 182) 183 (F 183) := by
  apply div_span (valueOf Q L g w d) Flow.code_182 (by decide)
    (by decide +kernel) (by decide +kernel) rfl rfl _ _
  · dsimp only [iters]
    rw [Nat.mod_eq_of_lt (show Q.splits < 2^32 by have := hp.splitsRange; omega)]
    rfl
  · intro r hr
    have keys : (ctlLive 183).all (fun r => decide (r=679 ∨ r ∈ ctlLive 182)) := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp keys r hr)

theorem seg_gate_clip : Seg kernel Assumptions.all L g 2 183 (F 183) 185 (F 185) := by
  intro t ht
  seg_fp ht using (change Value.bits 32 ?x = b32 (BitVec.toNat ?x); simp [b32])

theorem cmp_zero (c : Cmp) (n : Nat) (hn : n < 2^32) (hc : c=.eq ∨ c=.ne) :
    PTX.compare c .b 32 (r32 (W n)) (i32 0) =
      (if c=.eq then decide (n=0) else decide (n≠0)) := by
  rcases hc with rfl|rfl <;> simp [PTX.compare,r32,i32,truncBits,W] <;> omega

private theorem shift7 (x : Nat) : Value.bits 32 (shl (W (x%2^32)) 7) = u32 (x*128) := by
  apply congrArg (Value.bits 32)
  apply BitVec.eq_of_toNat_eq
  change (truncBits 32 (r32 (W (x%2^32)) <<< 7)).toNat = _
  simp only [r32,truncBits,W,BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  omega

private theorem cap_three (n : Nat) (hn : n<2^32) :
    Value.bits 32 (if PTX.compare .lt .u 32 (r32 (W n)) (i32 3)
      then r32 (W n) else i32 3) = b32 (min 3 n) := by
  rw [r32_W hn]
  by_cases h : n<3
  · rw [Nat.min_eq_right (by omega)]
    have cmp : PTX.compare .lt .u 32 (W n) (i32 3) = true := by
      simp [PTX.compare,W,i32,truncBits]; omega
    rw [cmp]; rfl
  · rw [Nat.min_eq_left (by omega)]
    have cmp : PTX.compare .lt .u 32 (W n) (i32 3) = false := by
      simp [PTX.compare,W,i32,truncBits]; omega
    rw [cmp]; rfl

theorem seg_gate_flags : Seg kernel Assumptions.all L g 4 185 (F 185) 189 (F 189) := by
  intro t ht
  have hn : preloadN Q L g d < 2^32 := by
    dsimp only [preloadN,preload,min32]
    split <;> simp only [r32,truncBits,BitVec.toNat_ofNat] <;> omega
  seg_fp ht using first
    | exact congrArg Value.pred (cmp_zero .ne _ hn (Or.inr rfl))
    | exact cap_three _ hn
    | exact shift7 _
    | exact congrArg Value.pred (cmp_zero .eq _ (show g%L.block%128<2^32 by omega) (Or.inl rfl))

theorem gate_head {m} (hp : Pre Q L m) :
    SegU kernel Assumptions.all L g 181 (F 180) 189 (F 189) :=
  (SegU.of_seg seg_gate_numerator).comp ((quotient hp).comp
    ((SegU.of_seg seg_gate_clip).comp (SegU.of_seg seg_gate_flags)))

theorem gate_bra :
    Seg kernel Assumptions.all L g 1 189 (F 189)
      (if decide (preloadN Q L g d ≠ 0) = true then 190 else 316) (F 189) :=
  have key : 53 ∈ ctlLive 189 := by decide +kernel
  Seg.braNot (pick := decide (preloadN Q L g d≠0)) Flow.code_189
    (mem_factsFrom_eq key (by rfl : valueOf Q L g w d 53 = .pred (decide (preloadN Q L g d≠0))))
    (fun t _ => Lib.bra_rule t) (segFree (by decide))

/-- The run after the barrier of a block-free launch, up to the end of the copy tail. -/
theorem gate_to_316 {m} (hp : Pre Q L m) (hn : preloadN Q L g d = 0) :
    SegU kernel Assumptions.all L g 181 (F 180) 316 (F 316) := by
  have := (gate_head hp).comp
    (SegU.of_seg (gate_bra (Q := Q) (L := L) (g := g) (d := d) (w := w)))
  rw [show decide (preloadN Q L g d ≠ 0) = false by simp [hn]] at this
  exact this.comp (cross (by decide +kernel : crossCheck 189 316 316))

theorem step_preload_gate {m} (hp : Pre Q L m) (d : D) (hs : d.site = .bar2) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.bar2,a,b,c,won,bcast⟩
  let n := preloadN Q L g d
  let z := if n=0 then querySite (g%L.block) d 0 else Site.pb 0 0
  obtain ⟨_,qinv,qsub⟩ := query_route (Q := Q) (L := L) (g := g) (w := w) (d := d) 0
  apply straight (d := d) (z := z) Flow.code_180 rfl (fun _ => trivial) fires_barSyncN_next
    (fun _ => rfl) rfl _ _ _
  · dsimp only [z]; split <;> first | rfl | exact qsub
  · dsimp only [z]; split <;> first | exact qinv | trivial
  · by_cases hn : n=0
    · simp only [z,hn,↓reduceIte]
      exact (gate_to_316 hp hn).comp (query_start hp)
    · have := (gate_head hp).comp
        (SegU.of_seg (gate_bra (Q := Q) (L := L) (g := g) (d := d) (w := w)))
      rw [show decide (preloadN Q L g d ≠ 0) = true by simpa using hn] at this
      simp only [z,hn,↓reduceIte]
      exact this.comp block_row

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

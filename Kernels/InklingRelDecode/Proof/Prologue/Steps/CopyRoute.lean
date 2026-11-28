-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryStart
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockPointer
import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegChain
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

theorem preload_lt (d : D) (s x : Nat) : preload s x d < 2^32 := by
  dsimp only [preload,min32]
  split <;> simp only [r32,truncBits,BitVec.toNat_ofNat] <;> omega

theorem cmp_eq1 (n : Nat) (hn : n<2^32) :
    PTX.compare .eq .b 32 (truncBits 32 (W n)) (truncBits 32 (BitVec.ofInt 64 1)) =
      decide (n=1) := by
  simp [PTX.compare,truncBits,W]
  omega

theorem cmp_lt3 (n : Nat) (hn : n<2^32) :
    PTX.compare .lt .u 32 (truncBits 32 (W n)) (truncBits 32 (BitVec.ofInt 64 3)) =
      decide (n<3) := by
  simp [PTX.compare,truncBits,W]
  omega

variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {d : D}
noncomputable abbrev preloadN (Q : Params) (L : Launch) (g : Nat) (d : D) :=
  preload Q.splits ((L.ctaidOf (g/L.block)).get .x) d
local notation "n" => preloadN Q L g d
local notation "F" => facts Q L g w d

theorem tail_cmp0 : Seg kernel Assumptions.all L g 1 232 (F 231)
    233 ((63,.pred (decide (n=1)))::F 231) := by
  intro t ht
  seg_fp ht using exact congrArg Value.pred (cmp_eq1 _ (preload_lt ..))

theorem tail_cmp1 : Seg kernel Assumptions.all L g 1 274 (F 273)
    275 ((72,.pred (decide (n<3)))::F 273) := by
  intro t ht
  seg_fp ht using exact congrArg Value.pred (cmp_lt3 _ (preload_lt ..))

/-- The branch after the fourth issue, when it leaves the preload loop: up to the end of the
copy tail. -/
theorem copy_tail_316 (b : Fin 3) (h0 : b = 0 → n = 1) (h1 : b = 1 → n < 3) :
    SegU kernel Assumptions.all L g ((Site.ptc b 3).pc+1) (F (Site.ptc b 3).pc) 316 (F 316) := by
  fin_cases b
  · apply (SegU.of_seg tail_cmp0).comp
    apply (SegU.branch (decide (n=1)) Flow.code_233 Lib.bra_rule (segFree (by decide))).comp
    simp only [h0 rfl,decide_true,↓reduceIte]
    exact cross (d := d) (by decide +kernel : crossCheck 231 316 316)
  · apply (SegU.of_seg tail_cmp1).comp
    apply (SegU.branch (decide (n<3)) Flow.code_275 Lib.bra_rule (segFree (by decide))).comp
    simp only [h1 rfl,decide_true,↓reduceIte]
    exact cross (d := d) (by decide +kernel : crossCheck 273 316 316)
  · exact cross (by decide +kernel : crossCheck 315 316 316)

/-- The branch after the fourth issue tests equality on the first block and
unsigned less-than on the second. The third block falls through. -/
theorem copy_tail {m} (hp : Pre Q L m) (b : Fin 3) :
    let z := afterCopy d (g%L.block) n b 3
    SegU kernel Assumptions.all L g ((Site.ptc b 3).pc+1) (F (Site.ptc b 3).pc)
      z.pc (F z.pc) := by
  fin_cases b <;> intro z
  · apply (SegU.of_seg tail_cmp0).comp
    apply (SegU.branch (decide (n=1)) Flow.code_233 Lib.bra_rule (segFree (by decide))).comp
    by_cases h : n=1
    · simp only [h,decide_true,↓reduceIte]
      simpa [z,afterCopy,h] using
        ((cross (d := d) (by decide +kernel : crossCheck 231 316 316)).comp
          (query_start (d := d) (w := w) (g := g) hp))
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
      simpa [z,afterCopy,h,Site.pc,pbPc] using
        (block_mid_1 (Q := Q) (L := L) (g := g) (w := w) (d := d))
  · apply (SegU.of_seg tail_cmp1).comp
    apply (SegU.branch (decide (n<3)) Flow.code_275 Lib.bra_rule (segFree (by decide))).comp
    by_cases h : n<3
    · simp only [h,decide_true,↓reduceIte]
      simpa [z,afterCopy,h] using
        ((cross (d := d) (by decide +kernel : crossCheck 273 316 316)).comp
          (query_start (d := d) (w := w) (g := g) hp))
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
      simpa [z,afterCopy,h,Site.pc,pbPc] using
        (block_mid_2 (Q := Q) (L := L) (g := g) (w := w) (d := d))
  · exact (cross (by decide +kernel : crossCheck 315 316 316)).comp
      (query_start (d := d) (w := w) (g := g) hp)

def ptc3Guard (b : Fin 3) := [57,67,76][b.val]!
def ptc3Op (b : Fin 3) : Op :=
  let base := [682,702,724][b.val]!
  .cpTensor false false (base+8) 0 (.reg 1949) [.reg (base+4),.reg (base+7)]
    (613+2*b.val) 0 none .tile none

theorem ptc3_fetch (b : Fin 3) : kernel.code[(Site.ptc b 3).pc]? =
    some ⟨some (ptc3Guard b,false),ptc3Op b⟩ := by
  fin_cases b
  · exact Flow.code_231
  · exact Flow.code_273
  · exact Flow.code_315

theorem step_issue_last {m} (hp : Pre Q L m) (d : D) (b : Fin 3) (hs : d.site = .ptc b 3) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.ptc b 3,a,x,c,won,bcast⟩
  let z := afterCopy d (g%L.block) (preloadN Q L g d) b 3
  obtain ⟨_,qinv,qsub⟩ := query_route (Q := Q) (L := L) (g := g) (w := w) (d := d) 0
  apply straight (d := d) (z := z) (ptc3_fetch b) rfl _ (fun h => fires_next (by trivial) h)
    (fun _ => rfl) rfl _ _ (copy_tail hp b)
  · intro hi
    obtain ⟨eligible,elect⟩ := hi
    have keys : ∀ b, ptc3Guard b ∈ ctlLive (Site.ptc b 3).pc := by decide +kernel
    apply Code.guardTrue_factsFrom (keys b)
    have val : valueOf Q L g w d (ptc3Guard b) = .pred (decide (g%L.block%128<64) && won) := by
      fin_cases b <;> rfl
    rw [val]
    simp [eligible,show won = true from elect]
  · dsimp only [z,afterCopy]
    split_ifs <;> first | exact qsub | rfl
  · dsimp only [z,afterCopy]
    split_ifs <;> first | exact qinv | trivial

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

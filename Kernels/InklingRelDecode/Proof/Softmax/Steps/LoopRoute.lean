-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.LoopExit
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.NextBias
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Pointers
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.SkipBias
import Kernels.InklingRelDecode.Flow.Code.Part016
import Lemmas.Flow.BranchU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}
local notation "tid" => g % L.block
local notation "z" => loopSite e tid i
local notation "F" => facts e L g (D.mk z i v)

theorem loop_route (ok : e.Ok) (bound : i ≤ e.limit) :
    SegU kernel Assumptions.all L g 1049 (F 1049) (z).pc (F (z).pc) := by
  apply (loop_test (d := ⟨z,i,v⟩) ok bound).comp
  apply (SegU.branch (decide (i=e.limit)) Flow.code_1050 Lib.bra_rule (segFree (by decide))).comp
  by_cases h : i = e.limit
  · simpa only [loopSite,h,decide_true,↓reduceIte,Site.pc] using
      (loop_exit (e := e) (L := L) (g := g) (d := ⟨z,i,v⟩) ok)
  · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
    apply (next_gate (d := ⟨z,i,v⟩) ok bound).comp
    apply (next_pointers (d := ⟨z,i,v⟩)).comp
    by_cases en : nextEnabled e tid i
    · simp only [loopSite,h,en,↓reduceIte]
      exact fun t ht => .inl ⟨t,.refl,ht⟩
    · simp only [loopSite,h,en,↓reduceIte]
      have off : nextEnabled e tid i = false := Bool.eq_false_iff.mpr en
      apply (Bias.skip_all (e := e) (L := L) (g := g) (i := i) (v := v) .nxt
        (congrArg Value.pred off)).comp
      have small := limit_bound ok
      exact next_bias_tail (i := i) (v := v) (e := e) (g := g) (L := L) (by omega)

theorem loop_inv (ok : e.Ok) (thread : tid < 256) (bound : i ≤ e.limit) :
    Inv e tid ⟨z,i,v⟩ := by
  unfold loopSite
  split
  · exact ⟨ok,thread,bound,(by rintro (h|h) <;> cases h),
      fun _ => nofun,fun _ => nofun,nofun,fun h => (h rfl).elim⟩
  · rename_i cont
    split
    · rename_i en
      exact ⟨ok,thread,bound,(by rintro (h|h) <;> cases h),
        fun _ => nofun,fun _ _ => en,nofun,fun _ _ _ _ => (show i < e.limit by omega)⟩
    · exact ⟨ok,thread,bound,(by rintro (h|h) <;> cases h),
        fun _ => nofun,fun _ => nofun,nofun,fun _ _ _ _ => (show i < e.limit by omega)⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

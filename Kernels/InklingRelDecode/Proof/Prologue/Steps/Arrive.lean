-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockPointer
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Lemmas.Flow.SegPieces
import Lemmas.Flow.IssueNext
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
theorem arr_fetch (b : Fin 3) : kernel.code[(Site.arr b).pc]? =
    some ⟨some (177,false),.mbarArrive (613+2*b.val) 0 (.imm 65536) (.imm 1)
      false true .cta none⟩ := by
  fin_cases b
  · exact Flow.code_193
  · exact Flow.code_237
  · exact Flow.code_279

theorem arr_guard : ∀ b, 177 ∈ ctlLive (Site.arr b).pc := by decide +kernel

theorem arriveSeg {Q L g w} (d : D) (b : Fin 3) :
    SegU kernel Assumptions.all L g ((Site.arr b).pc+1) (facts Q L g w d (Site.arr b).pc)
      (Site.lb b 0).pc (facts Q L g w d (Site.lb b 0).pc) := by
  fin_cases b
  · exact block_arrive_0
  · exact block_arrive_1
  · exact block_arrive_2

/-- The first lane of each 128-thread group announces the bytes before the block-table reads. -/
theorem step_arrive {Q L g w} (d : D) (b : Fin 3) (hs : d.site = .arr b) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.arr b,a,x,c,won,bcast⟩
  have guardLive := arr_guard b
  apply straight (d := d) (z := .lb b 0) (arr_fetch b) rfl _
    (fun h => fires_next (by trivial) h) (fun _ => rfl) rfl rfl trivial (arriveSeg d b)
  intro hi
  apply Code.guardTrue_factsFrom guardLive
  change Value.pred (decide (g % L.block % 128 = 0)) = _
  simp [show g % L.block % 128 = 0 from hi]

theorem pb0_fetch (b : Fin 3) : kernel.code[(Site.pb b 0).pc]? =
    some ⟨none,.barSyncN (.imm 0) (.imm 128) true⟩ := by
  fin_cases b
  · exact Flow.code_192
  · exact Flow.code_236
  · exact Flow.code_278

theorem pb0_adj : ∀ b, (Site.pb b 0).pc+1 = (Site.arr b).pc ∧
    (ctlLive (Site.arr b).pc).isSublist (ctlLive (Site.pb b 0).pc) := by decide +kernel

/-- The first counted barrier of each preload leads to the arrival on lane zero
of the group. Its peers skip the guarded arrival and compute the table address. -/
theorem step_preload_head {Q L g w} (d : D) (b : Fin 3) (hs : d.site = .pb b 0) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.pb b 0,a,x,c,won,bcast⟩
  obtain ⟨pc,live⟩ := pb0_adj b
  have arrive := samePc (Q := Q) (L := L) (g := g) (w := w) (d := d) pc live
  by_cases lead : g%L.block%128=0
  · apply straight (d := d) (z := .arr b) (pb0_fetch b) rfl (fun _ => trivial)
      fires_barSyncN_next _ rfl rfl lead arrive
    intro ev
    simp [d,next,lead]
  · apply straight (d := d) (z := .lb b 0) (pb0_fetch b) rfl (fun _ => trivial)
      fires_barSyncN_next _ rfl rfl trivial _
    · intro ev
      simp [d,next,lead]
    · have key := arr_guard b
      have val : valueOf Q L g w d 177 = Value.pred false := by
        change Value.pred (decide (g%L.block%128=0)) = _
        simp [lead]
      have skip := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
        (arr_fetch b) (val ▸ mem_factsFrom (val := valueOf Q L g w d) key) rfl
      exact arrive.comp ((SegU.of_seg skip).comp (arriveSeg d b))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

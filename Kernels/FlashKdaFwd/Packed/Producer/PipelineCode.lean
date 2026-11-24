-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ProducerControl
import all Kernels.FlashKdaFwd.Packed.Decode.Scalars
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX
set_option maxRecDepth 60000
set_option maxHeartbeats 0

def inPipeline (pc : Nat) : Prop := 1411 ≤ pc ∧ pc ≤ 1881

def stays : Op → Bool
  | .bra dst _ => decide (1411 ≤ dst ∧ dst ≤ 1882)
  | .brx .. | .ret | .exit => false
  | _ => true

private def pipelineWindow (pc n : Nat) :=
  (Transfers.slice pc n).map (List.all · fun i => stays i.op)

private theorem scalar₁ : pipelineWindow 1411 1 = some true := by
  unfold pipelineWindow
  rw [Prologue.scalarSite 1411 false "%r1790" 16 2096 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

private theorem beforeWait : pipelineWindow 1412 23 = some true := by kernel_rfl

private theorem scalar₂ : pipelineWindow 1435 1 = some true := by
  unfold pipelineWindow
  rw [Prologue.scalarSite 1435 false "%r1784" 12 2090 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)]
  rfl

private theorem mainWait : pipelineWindow 1436 20 = some true := by kernel_rfl

private theorem tailWait : pipelineWindow 1863 19 = some true := by kernel_rfl

private theorem inside {pc n j : Nat} {i : Instr} (h : pipelineWindow pc n = some true)
    (fit : pc+n ≤ 3835) (lo : pc ≤ j) (hi : j < pc+n) (site : kernel.code[j]? = some i) :
    stays i.op = true := by
  unfold pipelineWindow at h
  rw [instructions fit] at h
  apply List.all_eq_true.mp (Option.some.inj h)
  apply List.mem_of_getElem?
  rw [List.getElem?_take_of_lt (show j-pc < n by omega),List.getElem?_drop,
    show pc+(j-pc)=j by omega,site]

theorem pipeline_site {pc : Nat} {i : Instr} (live : allowed pc) (region : inPipeline pc)
    (site : kernel.code[pc]? = some i) : stays i.op = true := by
  unfold allowed at live
  unfold inPipeline at region
  by_cases a : pc < 1412
  · exact inside scalar₁ (by decide) (by omega) (by omega) site
  by_cases b : pc < 1435
  · exact inside beforeWait (by decide) (by omega) (by omega) site
  by_cases c : pc < 1436
  · exact inside scalar₂ (by decide) (by omega) (by omega) site
  by_cases d : pc < 1456
  · exact inside mainWait (by decide) (by omega) (by omega) site
  exact inside tailWait (by decide) (by omega) (by omega) site

end FlashKda.Packed.ProducerControl

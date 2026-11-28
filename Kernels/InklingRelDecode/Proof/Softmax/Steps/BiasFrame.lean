-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.BiasSite
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

private def from63 (j : Fin 63) : Fin 64 := ⟨j.val,by omega⟩
private def succ63 (j : Fin 63) : Fin 64 := ⟨j.val+1,by omega⟩

private noncomputable def projects (b : Bias) (j : Fin 63) : Bool :=
  let pc := (b.site (from63 j)).pc
  let stop := (b.site (succ63 j)).pc
  (ctlLive stop).isSublist (ctlLive pc)

private noncomputable def crosses (b : Bias) (j : Fin 63) : Bool :=
  let pc := (b.site (from63 j)).pc
  let stop := (b.site (succ63 j)).pc
  Havoc.check Lib.hooks (ctlLive stop) (pc+1) stop ((kernel.code.drop (pc+1)).take 1)

private theorem pre_projects : ∀ j, projects .pre j := by decide +kernel
private theorem next_projects : ∀ j, projects .nxt j := by decide +kernel
private theorem pre_crosses : ∀ j, crosses .pre j := by decide +kernel
private theorem next_crosses : ∀ j, crosses .nxt j := by decide +kernel
private theorem code_length : kernel.code.length = 2856 := by kernel_rfl

theorem Bias.frame {e L g i v} (b : Bias) (j : Fin 63) :
    let s := b.site ⟨j.val,by omega⟩
    let z := b.site ⟨j.val+1,by omega⟩
    SegU kernel Assumptions.all L g (s.pc+1) (facts e L g ⟨s,i,v⟩ s.pc)
      z.pc (facts e L g ⟨z,i,v⟩ z.pc) := by
  let s := b.site (from63 j)
  let z := b.site (succ63 j)
  have nextPc : z.pc = s.pc+2 := by cases b <;> rfl
  have len : z.pc ≤ 2856 := by
    cases b <;> change _ + 2*(j.val+1) ≤ 2856 <;> omega
  have checked : crosses b j := by cases b <;> first | exact pre_crosses _ | exact next_crosses _
  have sub : projects b j := by cases b <;> first | exact pre_projects _ | exact next_projects _
  apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok (by change s.pc+1 ≤ z.pc; omega)
    (code_length ▸ len)
  · rw [facts,factsFrom_keys]
    change Havoc.check Lib.hooks (ctlLive z.pc) (s.pc+1) z.pc
      ((kernel.code.drop (s.pc+1)).take (z.pc-(s.pc+1))) = true
    rwa [show z.pc-(s.pc+1) = 1 by omega]
  · exact project (List.isSublist_iff_sublist.mp sub).subset

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.BiasFrame
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

private theorem guard_live : ∀ (b : Bias) (j : Fin 64), b.guard ∈ ctlLive (b.site j).pc := by
  intro b; cases b <;> decide +kernel

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

private theorem Bias.skip (b : Bias) (j : Fin 64)
    (off : valueOf e L g ⟨b.site j,i,v⟩ b.guard = .pred false) :
    let pc := (b.site j).pc
    let F := facts e L g ⟨b.site j,i,v⟩ pc
    SegU kernel Assumptions.all L g pc F (pc+1) F := by
  obtain ⟨a,hc,_⟩ := b.load j
  exact SegU.of_seg (Seg.guardSkip hc (mem_factsFrom_eq (guard_live b j) off) rfl)

/-- In an inactive bias stream every predicated load is silent. The intervening
moves can be crossed with the same frame used on the active path. -/
theorem Bias.skip_all (b : Bias)
    (off : valueOf e L g ⟨b.site 0,i,v⟩ b.guard = .pred false) :
    let s := b.site 0
    let z := b.site 63
    SegU kernel Assumptions.all L g s.pc (facts e L g ⟨s,i,v⟩ s.pc)
      (z.pc+1) (facts e L g ⟨z,i,v⟩ z.pc) := by
  have reach (j : Nat) (hj : j < 64) :
      let s := b.site 0
      let z := b.site ⟨j,hj⟩
      SegU kernel Assumptions.all L g s.pc (facts e L g ⟨s,i,v⟩ s.pc)
        z.pc (facts e L g ⟨z,i,v⟩ z.pc) := by
    induction j with
    | zero => exact fun t h => .inl ⟨t,.refl,h⟩
    | succ j ih =>
      let n : Fin 63 := ⟨j,by omega⟩
      exact ((ih (by omega)).comp (b.skip ⟨j,by omega⟩ off)).comp (b.frame n)
  exact (reach 63 (by decide)).comp (b.skip 63 off)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

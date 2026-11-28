-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Proof PTX.Flow Arith32

/-- An undefined signed quotient ends a crossing. A successful one is exactly
the signed quotient rounded toward zero of the source words. -/
theorem div_span {L g pc dst x y a b rs rs'} (V : Nat → Value)
    (fetch : kernel.code[pc]? = some ⟨none,.int ⟨.div,.int .s 32,false,[some dst],
      [.reg x,.reg y]⟩⟩) (hs : Assumptions.emuSites.contains pc = false)
    (hx : x ∈ rs) (hy : y ∈ rs) (vx : V x = .bits 32 a) (vy : V y = .bits 32 b)
    (vd : V dst = .bits 32 (intBits 32 ((intOf .s 32 (r32 a)).tdiv (intOf .s 32 (r32 b)))))
    (keys : ∀ r ∈ rs', r=dst ∨ r ∈ rs) :
    SegU kernel Assumptions.all L g pc (factsFrom rs V) (pc+1) (factsFrom rs' V) := by
  apply Lib.scalarStepU fetch rfl rfl hs _ (fun _ h => Lib.writeLive keys h)
  intro t u h he
  have readX := readBits_regBits (L := L) (g := g) (w := 32)
    (holds_mem h (mem_factsFrom_eq hx vx)) (by rfl)
  have readY := readBits_regBits (L := L) (g := g) (w := 32)
    (holds_mem h (mem_factsFrom_eq hy vy)) (by rfl)
  have lanes : (DType.int .s 32).intLanes? = some (.s,32,1) := rfl
  simp only [execInt,intResult,DType.width,lanes,readX,readY,bind,Except.bind] at he
  rw [vd]
  cases hd : intDiv .s 32 (r32 a) (r32 b) with
  | error f => simp only [r32] at hd; rw [hd] at he; contradiction
  | ok q =>
    rw [show intDiv .s 32 (truncBits 32 a) (truncBits 32 b) = .ok q from hd] at he
    simp only [intDiv] at hd
    split_ifs at hd <;> first | contradiction | (cases hd; exact (Except.ok.inj he).symm)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control

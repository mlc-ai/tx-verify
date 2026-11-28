-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Kernels.InklingRelDecode.Flow.Code.Part019
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Flow.Code.Part034
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.WaitU
import Kernels.InklingRelDecode.Proof.Lib.PollBranch

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}

theorem step_waitO : (code e L g).StepAtU ⟨.waitO,i,v⟩ := by
  apply step_of_inv
  intro hi
  let dst (ok : Bool) : D := ⟨if ok then .bar22 else .waitO,i,v⟩
  apply Code.waitU (C := code e L g) (d := ⟨.waitO,i,v⟩) (dst := dst) Flow.code_2239
  · change 2608 ∉ (factsFrom (ctlLive 2239) _).map Prod.fst
    rw [factsFrom_keys]
    decide +kernel
  · intro m q ok sc; cases ok <;> rfl
  · rfl
  · rfl
  · intro _; rfl
  · intro _; rfl
  · rintro (_ | _)
    · exact hi
    · exact body_inv hi rfl rfl
  · rintro (_ | _)
    · exact Lib.poll_branch (pc := 2240) false Flow.code_2240 (by decide)
    · apply (Lib.poll_branch (pc := 2240) true Flow.code_2240 (by decide)).comp
      exact project_seg (p := 2239) (q := 2241) (by decide +kernel)

private theorem slot_shift {d : D} :
    SegU kernel Assumptions.all L g 1259 (facts e L g d 1257) 1260 (facts e L g d 1260) := by
  apply Lib.shiftLive (valueOf e L g d) Flow.code_1259 (by decide)
    (by decide : 504 ∈ ctlLive 1257) _ (by decide +kernel)
  change b32 (d.i % 2 * 128) = .bits 32 (Arith32.shl _ 7)
  have h : d.i % 2 = 0 ∨ d.i % 2 = 1 := by omega
  rcases h with h | h <;> simp only [valueOf,scalarValue,h] <;> rfl

private theorem slot_base {d : D} :
    SegU kernel Assumptions.all L g 1260 (facts e L g d 1260) 1261 (facts e L g d 1261) :=
  Lib.sum_span true (δ := d.i%2*128) (by omega) Flow.code_1260 (by decide)
    (by decide +kernel : 463 ∈ ctlLive 1260) rfl
    (fun _ h => Lib.delta_reg h (show 942 ∈ ctlLive 1260 by decide) rfl (by omega))
    (by decide +kernel)

theorem step_waitS : (code e L g).StepAtU ⟨.waitS,i,v⟩ := by
  apply step_of_inv
  intro hi
  let dst (ok : Bool) : D := ⟨if ok then .shfl4 else .waitS,i,v⟩
  apply Code.waitU (C := code e L g) (d := ⟨.waitS,i,v⟩) (dst := dst) Flow.code_1257
  · change 2511 ∉ (factsFrom (ctlLive 1257) _).map Prod.fst
    rw [factsFrom_keys]
    decide +kernel
  · intro m q ok sc; cases ok <;> rfl
  · rfl
  · rfl
  · intro _; rfl
  · intro _; rfl
  · rintro (_ | _)
    · exact hi
    · exact body_inv hi rfl rfl
  · rintro (_ | _)
    · exact Lib.poll_branch (pc := 1258) false Flow.code_1258 (by decide)
    · apply (Lib.poll_branch (pc := 1258) true Flow.code_1258 (by decide)).comp
      exact (slot_shift (d := ⟨.waitS,i,v⟩)).comp slot_base

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.PreTail

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

theorem step_last_pre {e L g i v} : (code e L g).StepAtU ⟨.pre 63,i,v⟩ := by
  apply step_of_inv
  intro hi
  obtain ⟨eq,_⟩ := hi.pre 63 rfl
  change i = 0 at eq
  subst i
  let z := loopSite e (g % L.block) 0
  apply Bias.read_step (e := e) (L := L) (g := g) (i := 0) (v := v) .pre 63 z
  · intro h
    exact loop_inv h.entry h.thread (Nat.zero_le _)
  · intro _; rfl
  · exact (after_pre hi.entry hi.thread).comp (loop_route hi.entry (Nat.zero_le _))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control

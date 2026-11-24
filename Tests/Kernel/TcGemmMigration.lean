-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Theorem

/-! The TcGemm proof: its four goals, the protocol facts they rest on (the operand copies observed
through `bar0`, the MMA's completion observed through `bar1`, the published Tensor Memory address,
the MMA's operands and the loaded words), and the axioms of the public theorems. -/

open PTX PTX.AsyncCopy PTX.Kernels.TcGemm PTX.Kernels.TcGemm.Proof
open TcMma (byteInt s32)

#print axioms PTX.Kernels.TcGemm.correct
#print axioms PTX.Kernels.TcGemm.completed_execution
#print axioms PTX.Kernels.TcGemm.realizable_result
#print axioms PTX.Kernels.TcGemm.Proof.thread_facts
#print axioms PTX.Kernels.TcGemm.Proof.wit
#print axioms PTX.Kernels.TcGemm.Proof.wait_observes_copies
#print axioms PTX.Kernels.TcGemm.Proof.wait_observes_mma
#print axioms PTX.Kernels.TcGemm.Proof.rd_val
#print axioms PTX.Kernels.TcGemm.Proof.mma_operands
#print axioms PTX.Kernels.TcGemm.Proof.ld_vals
#print axioms PTX.Kernels.TcGemm.Proof.safe
#print axioms PTX.Kernels.TcGemm.Proof.progress_goal
#print axioms PTX.Kernels.TcGemm.Proof.bound_goal
#print axioms PTX.Kernels.TcGemm.Proof.result

/-- The safety goal, from the thread facts of every consistent execution. -/
example {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0}
    (hpre : Pre L A B D a b mem0) :
    ∀ X, Consistent L kernel [] mem0 X → ¬ Unsafe L kernel [] mem0 X :=
  fun _ hX => safe hpre (thread_facts hpre hX) hX

/-- The result goal. -/
example {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0}
    (hpre : Pre L A B D a b mem0) :
    ∀ X mf, Consistent L kernel [] mem0 X → Complete L X → IsFinal L mem0 X mf →
      Post D a b mem0 mf :=
  fun _ _ hX hc hf => result hpre (thread_facts hpre hX) hX hc hf

/-- A successful poll of `bar0` observes both operand copies' completion. -/
example {L : Launch} {A B D : Nat} {mem0 : Mem0} {X : Execution}
    {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
    (hX : Consistent L kernel [] mem0 X) (hW : Wit A B D L.sharedBase X P m u) {w : EvId} {pc : Nat}
    (he : X.get w = some ⟨pc, .wait (bar0 L.sharedBase) 0 true true .cta⟩) :
    AsyncObserved X (0, 6) (.notify .copy) w true .cta ∧
      AsyncObserved X (0, 7) (.notify .copy) w true .cta :=
  wait_observes_copies hX hW he

/-- A successful poll of `bar1` observes the MMA's completion through its commit. -/
example {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
    {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
    (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
    (hW : Wit A B D L.sharedBase X P m u) {w : EvId} {pc : Nat}
    (he : X.get w = some ⟨pc, .wait (bar1 L.sharedBase) 0 true true .cta⟩) :
    AsyncObserved X (0, hd 0 + 2 + (P 0).n0) .mmaDone w true .cta :=
  wait_observes_mma hpre hX hW he

/-- The MMA's operand bytes are the inputs' elements. -/
example {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
    {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
    (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
    (hW : Wit A B D L.sharedBase X P m u)
    (hm : hd 0 + 2 + (P 0).n0 < m 0)
    (hstart : X.async.mmaStarted (0, hd 0 + 2 + (P 0).n0) = true) :
    ∃ ab bb, X.async.mmaOperands (0, hd 0 + 2 + (P 0).n0) = some ⟨ab, bb⟩ ∧
    (∀ i < 128, ∀ k < 32, byteInt true (ab.getD (i * 32 + k) none) = some (a i k)) ∧
    (∀ j < 8, ∀ k < 32, byteInt true (bb.getD (j * 32 + k) none) = some (b k j)) :=
  mma_operands hpre hX hW hm hstart

/-- Word `j` of thread `g`'s Tensor Memory load is `D[g][j]`. -/
example {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
    {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}
    (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
    (hW : Wit A B D L.sharedBase X P m u) {g : Nat} (hg : g < 128)
    (hm : ldIdx g (P g) < m g) : ∀ j < 8, (P g).vals[j]? = some (s32 (dot a b g j)) :=
  ld_vals hpre hX hW hg hm

-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Values.FinalWord
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Lemmas.Flow.Recip
import Kernels.InklingRelDecode.Proof.Lib.SoftFold
import Kernels.InklingRelDecode.Proof.Lib.SoftRow

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

open PTX.Proof Protocol.Values

/-- The zero-block path writes the literal zero word. A nonempty iteration
range stores the f32 result, also when an individual row has no visible key. -/
noncomputable def Result.outputWord (Q : Params) (r s tok h d : Nat) : Value :=
  if Q.numIters r s=0 then b32 0 else .float .f32 (oPart Q r s tok h d)

def Result.Output.Words (Q : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → Complete L X → Follow Q L X →
    ∀ r<Q.b, ∀ s<Q.splits, ∀ tok<Q.qLen r, ∀ h<heads, ∀ d<headDim,
      StoredWord X (oLoc Q s (Q.qStart r+tok) h d) (Result.outputWord Q r s tok h d)

theorem Result.output {Q L m X mf} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (fin : IsFinal L m X mf) (rest : Result.Output.Words Q L m) (hc : Complete L X)
    (hf : Follow Q L X) :
    ∀ r<Q.b, ∀ s<Q.splits, ∀ tok<Q.qLen r, ∀ h<heads, ∀ d<headDim,
      memFloat .f32 mf (oLoc Q s (Q.qStart r+tok) h d)=.ok (oPart Q r s tok h d) := by
  classical
  intro r hr s hs tok ht h hh d hd
  have bytes := final_word hp hX fin rfl (rest X hX hc hf r hr s hs tok ht h hh d hd)
  by_cases empty : Q.numIters r s=0
  · have none : keys Q r s tok=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k member
      obtain ⟨_,i,hi,_⟩ := (Lib.numIters_spec hp.splitsPos).mp (Finset.mem_filter.mp member).2.1
      omega
    have zero : oPart Q r s tok h d=0 := by simp [oPart,rowSum,none]
    simp only [Result.outputWord,empty,ite_true] at bytes
    rw [zero,memFloat_of_bytes (fmt := .f32) (v := b32 0) (fun _ => rfl) rfl bytes]
    exact PTX.Flow.valFloat_zero
  · apply memFloat_float
    intro j hj
    have v := bytes j hj
    simp only [Result.outputWord,ite_eq_right empty] at v
    exact v

end PTX.Kernels.InklingRelDecode.Proof.Top

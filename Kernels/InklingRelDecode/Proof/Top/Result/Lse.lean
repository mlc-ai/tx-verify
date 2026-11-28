-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Values.FinalWord

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

open Protocol.Values

noncomputable def Result.lseWord (Q : Params) (r s tok h : Nat) : Value :=
  if rowSum Q r s tok h=0 then (FVal.inf true).toValue .f32 else .float .f32 (lsePart Q r s tok h)

def Result.Lse.Words (Q : Params) (L : Launch) (m : Mem0) : Prop :=
  ∀ X, Consistent L kernel Assumptions.all m X → Complete L X → Follow Q L X →
    ∀ r<Q.b, ∀ s<Q.splits, ∀ tok<Q.qLen r, ∀ h<heads,
      StoredWord X (lseLoc Q s (Q.qStart r+tok) h) (Result.lseWord Q r s tok h)

theorem Result.lse {Q L m X mf} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (fin : IsFinal L m X mf) (rest : Result.Lse.Words Q L m) (hc : Complete L X)
    (hf : Follow Q L X) :
    (∀ r<Q.b, ∀ s<Q.splits, ∀ tok<Q.qLen r, ∀ h<heads, rowSum Q r s tok h≠0 →
      memFloat .f32 mf (lseLoc Q s (Q.qStart r+tok) h)=.ok (lsePart Q r s tok h)) ∧
    (∀ r<Q.b, ∀ s<Q.splits, ∀ tok<Q.qLen r, ∀ h<heads, rowSum Q r s tok h=0 →
      ∀ j<4, mf ((lseLoc Q s (Q.qStart r+tok) h).at j)=some (some (negInfByte j))) := by
  constructor
  · intro r hr s hs tok ht h hh nz
    apply memFloat_float
    intro j hj
    have v := final_word hp hX fin rfl (rest X hX hc hf r hr s hs tok ht h hh) j hj
    simp only [Result.lseWord,ite_eq_right nz] at v
    exact v
  · intro r hr s hs tok ht h hh zero j hj
    have v := final_word hp hX fin rfl (rest X hX hc hf r hr s hs tok ht h hh) j hj
    simpa only [Result.lseWord,zero,ite_true,negInfByte] using v

end PTX.Kernels.InklingRelDecode.Proof.Top

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Visibility

@[expose] public section

/-! # The tensor loads of an input ring slot

A loader's tensor issue on slot `s`'s full barrier is determined by its CTA and its count of
earlier issues there (`issue_inj`): the CTA names the loader (`producerOf_eq`), and one thread's
issues there are numbered by their counts (`PairTmaRing.issue_index_unique`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two tensor issues on slot `s`'s full barrier by loaders of one CTA, with as many earlier issues
there, are one issue. -/
theorem issue_inj (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {g1 k1 pc1 a1 g2 k2 pc2 a2 : Nat} {sp1 sp2 : TensorCopy.Spec}
    (he1 : X.get (g1, k1) = some ⟨pc1, .tensorIssue a1 sp1⟩) (hm1 : sp1.mbar = (slot L c s).full 0)
    (he2 : X.get (g2, k2) = some ⟨pc2, .tensorIssue a2 sp2⟩) (hm2 : sp2.mbar = (slot L c s).full 0)
    (hcta : g1 / L.block = g2 / L.block)
    (hcnt : ((X.tr g1).take k1).countP (issuesTo ((slot L c s).full 0)) =
      ((X.tr g2).take k2).countP (issuesTo ((slot L c s).full 0))) : g1 = g2 ∧ k1 = k2 := by
  obtain ⟨-, -, hp1, hb1⟩ := issue_facts hX ht he1 hm1
  obtain ⟨-, -, hp2, hb2⟩ := issue_facts hX ht he2 hm2
  obtain ⟨j1, pw1, qw1, aw1, cw1, -, hw1⟩ := exists_okPoll (X := X) (g := g1) (k := k1)
    (m := (slot L c s).empty ⟨g1 / L.block % 2, Nat.mod_lt _ (by decide)⟩) (by omega)
  obtain ⟨j2, pw2, qw2, aw2, cw2, -, hw2⟩ := exists_okPoll (X := X) (g := g2) (k := k2)
    (m := (slot L c s).empty ⟨g2 / L.block % 2, Nat.mod_lt _ (by decide)⟩) (by omega)
  have hp2' : producerThread L c ⟨g1 / L.block % 2, Nat.mod_lt _ (by decide)⟩ g2 = true := by
    rw [hcta]; exact hp2
  have hw2' := hw2
  rw [show (⟨g2 / L.block % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) =
    ⟨g1 / L.block % 2, Nat.mod_lt _ (by decide)⟩ by rw [hcta]] at hw2'
  have hg : g1 = g2 := (producerOf_eq hX ht hp1 hw1).trans (producerOf_eq hX ht hp2' hw2').symm
  subst hg
  exact ⟨rfl, PairTmaRing.issue_index_unique he1 hm1 he2 hm2 hcnt⟩

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof

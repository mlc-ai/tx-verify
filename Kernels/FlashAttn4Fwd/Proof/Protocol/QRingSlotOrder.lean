-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotFacts

@[expose] public section

/-! # Two copies of one ring byte are ordered

Two copies writing one byte of a ring slot's region in CTA `cta` are its loader's (the copies of
a CTA write only its own region, `RingFacts.write`), and when the first's use (`copyUse`) is
below the second's they are ordered through an MMA read of the byte in the first's use
(`copies_ordered`, by `PairTmaRing.copies_chain`):

* the second copy follows a successful poll of the CTA's empty barrier that found the
  consumer's commit of the first copy's use (`RingFacts.issue_use`: a copy is of the use of its
  loader's last successful empty poll);
* before that commit, an MMA of the use read every byte of the slot's region in both CTAs
  (`RingFacts.cover`), after the first copy and before the second. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace Rings

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Two copies of one ring byte in distinct uses are ordered**: they are one loader's, and
the copy of the earlier use is before the other in the asynchronous chain order. -/
theorem copies_ordered (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : RingInit L X) {b : FBar}
    (hb : b.isFull) {cta g1 k1 g2 k2 x y z x' y' z' : Nat} {l : Loc} (hl : InRegion L cta b l)
    (hw1 : AsyncCovers X (g1, k1) (.write (.load x y z)) l)
    (hw2 : AsyncCovers X (g2, k2) (.write (.load x' y' z')) l)
    (hlt : copyUse L X (cta / 2) b (g1, k1) < copyUse L X (cta / 2) b (g2, k2)) :
    g1 = g2 ∧
      AsyncChain L X l ((g1, k1), .write (.load x y z)) ((g2, k2), .write (.load x' y' z')) := by
  have H := hyp hpre hX ht htm hinit hb (cta / 2)
  obtain ⟨pc1, al1, sp1, he1, hm1, hc1⟩ := write_slot ht hb hl hw1
  obtain ⟨pc2, al2, sp2, he2, hm2, hc2⟩ := write_slot ht hb hl hw2
  obtain ⟨a1, rfl, hca1, -, -⟩ := full_issue hX ht hb he1 hm1
  obtain ⟨a2, rfl, hca2, -, -⟩ := full_issue hX ht hb he2 hm2
  have ha : a1 = a2 := Fin.ext (by omega)
  subst ha
  refine ⟨rfl, ?_⟩
  set S := slot L X (cta / 2) b with hS
  have hg1 := Frame.lt_of_get hX he1
  have hemp : b.partner.loc L (ctaOf L (S.prod a1)) = S.empty a1 := by
    rw [ctaOf_lead hpre a1]; rfl
  have hu1 := ht.issue_use hg1 he1 hm1 (isFull_ring hb)
  have hu2 := ht.issue_use (Frame.lt_of_get hX he2) he2 hm2 (isFull_ring hb)
  rw [hemp] at hu1 hu2
  have hlt' : okPolls (S.empty a1) ((X.tr (S.prod a1)).take k1) <
      okPolls (S.empty a1) ((X.tr (S.prod a1)).take k2) := by
    simp only [copyUse] at hlt
    omega
  refine PairTmaRing.copies_chain hX H he1 hm1 he2 hlt' hu1 hw1 hw2 0 ?_
  intro jc pcc spc hec hmc hcjc
  have hg := Frame.lt_of_get hX hec
  have hcc : ctaOf L (S.cons 0) = 2 * (cta / 2) := ctaOf_cons hpre 0
  have hmc' : spc.mbar = b.partner.loc L (ctaOf L (S.cons 0)) := by
    rw [hmc, hcc]; rfl
  obtain ⟨kR, isB, idx, -, hT, hcnt, hcov, hpres⟩ :=
    ht.cover hg hec hb hmc' hl (by rw [hcc]; omega)
  obtain ⟨-, -, hcR, -, hbud⟩ := ht.read hcov hb hl
  rw [hmc] at hcnt
  have hfull : b.loc L (ctaOf L (S.cons 0)) = S.full := by rw [hcc]; rfl
  have hemp0 : b.partner.loc L (ctaOf L (S.cons 0)) = S.empty 0 := by rw [hcc]; rfl
  rw [hfull, hemp0] at hbud
  exact ⟨kR, isB, idx, hT, hcnt.trans hcjc, hbud, hcov, hpres⟩

end Rings

end
end PTX.Kernels.FlashAttn4Fwd.Proof

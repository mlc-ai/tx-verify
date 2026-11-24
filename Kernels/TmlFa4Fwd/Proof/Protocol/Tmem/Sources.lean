-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Core.Tc.TcMmaSafety
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.ASource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AccSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.LoadSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceFacts

@[expose] public section

/-! # Every required Tensor Memory read has its source (`source_safe`)

Given the values of the completed MMAs' results: a load reads an MMA (`soft_source`, `corr_source`),
an accumulating MMA an earlier MMA of its lane, which is complete when it is (the pipeline's
completion order), or a correction store (`accSource`), and a PV MMA's A operand a softmax store
(`pvAStore`, `p_aReadSource`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every required Tensor Memory read has a read source with a value.** -/
theorem source_safe (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hv : ∀ i d s acc mask, X.MmaIssue i d s acc mask →
      CompletedValues L Assumptions.all X i) : SourceSafe L Assumptions.all X := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  have hR : OReady L X := oready ht hH.s hH.o hH.route
  refine sourceSafe_iff.mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨h, i⟩ j cell hcell
    obtain ⟨a, vals, hld, hj, rfl⟩ := ht.loadCell hcell
    obtain ⟨hh, h12⟩ := ht.tc_role (.inl hld)
    by_cases h8 : Prologue.warpIndex L h < 8
    · obtain ⟨src, v, h1, h2, -⟩ := soft_source hp hX ht ho hH.p hH.p2 hH.s hT
        (fun hx _ _ => hv _ _ _ _ _ hx) hh h8 hld hj
      exact ⟨src, v, h1, h2⟩
    · obtain ⟨src, v, h1, h2, -⟩ := corr_source hp hX ht ho hH.p hR hT
        (fun hx _ _ => hv _ _ _ _ _ hx) hh (by omega) h12 hld hj
      exact ⟨src, v, h1, h2⟩
  · rintro i cell hd ⟨d, s, mask, row, col, hi, hrc⟩
    have hc := ht.mma_reads hi hrc
    obtain ⟨src, hsrc, ⟨hs1, hs2, hcs⟩ | ⟨-, -, -, a, vals, sh, j, hst, hj, hceq⟩⟩ :=
      accSource hp ht ho hT hH.s hH.p hH.p2 hR hi hc
    · obtain ⟨g', k'⟩ := src
      simp only at hs1 hs2
      subst hs1
      obtain ⟨dK, sK, aK, mK, rowK, colK, hiK, hposK⟩ := id hcs
      obtain ⟨hacc, hw⟩ := hT.same_write hiK hi rfl hcs hc
      have hds : X.async.mmaDone (i.1, k') = true :=
        hX.mmaCompletion (i.1, k') i ⟨rfl, hs2, mma_pipe ht hiK hi rfl hs2 hacc,
          _, _, _, _, _, _, _, _, hiK, hi, hw, rowK, colK, cell, hposK⟩ hd
      obtain ⟨v, hres⟩ := hv _ _ _ _ _ hiK hds cell hcs
      exact ⟨_, v, hsrc, .inl hres⟩
    · exact ⟨_, vals[j], hsrc,
        .inr (.inl ⟨a, vals, sh, j, hst, List.getElem?_eq_getElem hj, hceq⟩)⟩
  · rintro i cell hd ha
    obtain ⟨d, s, acc, mask, index, pos, hi, hac⟩ := id ha
    obtain ⟨cellO, st, hst, hco, hO, h, k, a, j, vals, hh, hw, hs, hj, rfl, hu⟩ :=
      pvAStore hp ht hT hH.p hi hac
    refine ⟨(h, k), vals[j], p_aReadSource hp ht ho hH.p hH.p2 hH.s hi hco hO hac hh hw hs hj hu
      (sourceLive hT.live ⟨_, _, _, _, hi⟩ (.inr (.inr ha))), .inr (.inl
      ⟨a, vals, _, j, hs, List.getElem?_eq_getElem hj, (tcDataCell_s32x32b _ _ _ _).symm⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm

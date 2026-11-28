-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Ref

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue

private theorem scalar_rank (s : Site) (hi : s.pc ≤ 315) : s.rank = 4*s.pc := by
  suffices h : s.sub=0 by simp [Site.rank,h]
  cases s <;> try rfl
  · change 526+6*_ ≤ 315 at hi; omega
  · change 571≤315 at hi; omega

theorem ref_next {Q L g d dn e c} (h : Ref d c) (pc : e.pc = d.site.pc)
    (hn : Control.next Q L g d e = some (some dn)) : Ref dn (bump c e) := by
  have lt := rank_next hn
  constructor
  · intro p lo hi
    by_cases eq : e.pc=p
    · have source := pc.symm.trans eq
      have zero := h.fresh p lo hi (by rw [scalar_rank d.site (source ▸ hi),source])
      simp [bump,eq,zero]
    · simpa [bump,beq_eq_false_iff_ne.mpr eq] using h.once p lo hi
  · intro p lo hi before
    have zero := h.fresh p lo hi (by omega)
    have ne : e.pc ≠ p := by
      intro eq
      have source := pc.symm.trans eq
      rw [scalar_rank d.site (source ▸ hi),source] at lt
      omega
    simp [bump,beq_eq_false_iff_ne.mpr ne,zero]

end PTX.Kernels.InklingRelDecode.Proof.Prologue

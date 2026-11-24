-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.Tmem1Access
public import Kernels.InklingRelDecode.Proof.Protocol.TmemAccess

/-! # ERR-TMEM-ACCESS-LIFETIME for a `cta_group::1` allocation, on Inkling's premises

`Tmem.One.no_access_unsafe` gives the conclusion of Inkling's first-tree
`Proof.Tmem1.no_access_unsafe` from the same premises: the classification of the accesses
(`AccessInfo`), the allocation before every access and the loads' and stores' waits (`TmemLife`),
and the MMAs' completion before the deallocation (`MmaDoneDealloc`). -/

namespace PTX.Tests.Tmem1Access
open PTX PTX.Proof Tmem.Pair TcMma
open PTX.Kernels.InklingRelDecode.Proof PTX.Kernels.InklingRelDecode.Proof.Tmem1

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

example (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X 0) (hinfo : AccessInfo L X)
    (hl : SO.TmemLife L X) (hmd : MmaDoneDealloc L X) : ¬ AccessUnsafe L X := by
  obtain ⟨hacc, hno_cp, hno_shift⟩ := hinfo
  refine Tmem.One.no_access_unsafe (w := 0) hX ⟨ht.warp_lt, ht.event⟩
    (fun ha => ⟨(hacc ha).1, (hacc ha).2.1, (hacc ha).2.2.1⟩) (fun {e cell} ha => ?_)
    (fun {e cell d pc a n grp} ha hd hc => ?_)
  · obtain ⟨-, hc, -, hk⟩ := hacc ha
    rw [hc, Nat.zero_mul, Nat.add_zero]
    rcases hk with hm | ⟨a, vals, sh, hld⟩ | ⟨a, vals, sh, hst⟩
    · exact hl.alloc_before (a := 0) (vals := []) (sh := .s32x32b) (.inl hm)
    · exact hl.alloc_before (.inr (.inl hld))
    · exact hl.alloc_before (.inr (.inr hst))
  · refine ⟨fun ⟨a', vals, sh, hld⟩ => (hl.ldst_before_dealloc hd hc).1 hld,
      fun ⟨a', vals, sh, hst⟩ => (hl.ldst_before_dealloc hd hc).2 hst, fun hasync => ?_⟩
    rcases hasync with hm | ⟨c, hcp⟩ | ⟨s, hsh⟩
    · exact hmd hm hd hc
    · exact (hno_cp _ _ hcp).elim
    · exact (hno_shift _ _ hsh).elim

end PTX.Tests.Tmem1Access

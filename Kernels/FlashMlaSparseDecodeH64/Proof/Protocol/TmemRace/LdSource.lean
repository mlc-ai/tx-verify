-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.SourceDone

@[expose] public section

/-! # The source of a load of warpgroup 0 is a done MMA or a store

A register of a load of warpgroup 0 reads a cell of the score columns (`[400, 464)`) or of the
chunk columns (below `256`). Its read source (`ld_src_kind`) is an MMA, which is done: the order
before the load is an observed commit, never a pipelined pair, which starts at an MMA; or a store
(the warpgroup's rescale store). No copy writes these columns (`[256, 392)`) and the kernel fires
no shift. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The source of a load register is a done MMA or a store.** -/
theorem ld_src_kind {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {j : Nat}
    {cell : TcMma.Cell} (hld : X.TLd e a vals sh) (hj : j < vals.length)
    (hc : cell = tcDataCell L e.1 sh a j) {src : EvId}
    (hs : TcMma.ReadSource L X .ld src e cell) :
    (X.MmaCell src cell ∧ X.async.mmaDone src = true) ∨ TcMma.StoreCell L X src cell := by
  have hw := hs.2.1
  rcases hw with hm | hst | hcp | ⟨sp, ⟨pc, hsh⟩, -⟩
  · refine .inl ⟨hm, ?_⟩
    obtain ⟨pcl, hl⟩ := hld
    obtain ⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, -⟩ := id hm
    rcases hs.2.2.1 with (hdn | hpl) | ⟨⟨a', vals', sh', ⟨pcs, hst⟩⟩, -⟩ | ⟨-, -, c, d, s, acc,
        mask, -, -, ⟨pc, hy⟩, -⟩
    · exact hdn.done hX.tcCommit
    · obtain ⟨-, -, d, s, acc, mask, d', s', acc', mask', -, ⟨pc, hy⟩, -⟩ := hpl
      cases get_tc_inj hl hy
    · cases get_tc_inj h0 hst
    · cases get_tc_inj hl hy
  · exact .inr hst
  · exfalso
    obtain ⟨h, k⟩ := e
    obtain ⟨pc, he⟩ := hld
    have hT := tmem_rows hp hX hFw
    have hlen := ldLen hp hX he rfl
    obtain ⟨hat, hsh, ha, hcls⟩ := ld_class hp hX hFw he
    subst hsh
    obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha (j := j)
    rw [← hc] at hcta hlane hcol
    obtain ⟨-, cw⟩ := writer_cases hp hX hT (.inr (.inr (.inl hcp)))
    obtain ⟨c, cta, index, lane, ⟨pcc, hcg⟩, -⟩ := id hcp
    rcases cw with ⟨k', ⟨pc', s', hk', he', -⟩, -⟩ | ⟨b, ⟨pc', s', acc', he', -⟩, -⟩ |
      ⟨k', ⟨pc', c', hk', he', -⟩, h1, h2⟩ | ⟨⟨pc', a', vals', he', -⟩, -, -⟩
    · cases get_tc_inj hcg he'
    · cases get_tc_inj hcg he'
    · omega
    · cases get_tc_inj hcg he'
  · exact absurd rfl (no_shift_of_code hX code_noShift hsh sp)

end

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc

@[expose] public section

/-! # The MMA warp's `.nc` reads are allocated

The MMA warp's two `.nc` reads are its length loads (pcs 1876 and 1886), whose pointers are set:
each reads the four bytes of its row of the array (`Mma.read_topk`, `Mma.read_extra`), which
`Pre` allocates (`paramTopkLen`, `paramExtraTopkLen`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The MMA warp's `.nc` read covers allocated bytes only.** -/
theorem mma_ncAlloc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MmaAt L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs)
    (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, ⟨-, hK⟩, hl, -⟩ := mma_state hJ hi hev hpcσ ⟨hlo, hhi⟩
  obtain ⟨-, ⟨-, -, ⟨-, hso⟩, -⟩, -, -⟩ := (follow_iff.mp hFw g hg k).2 _ hσ
  obtain ⟨t, ins, o, hat', hc', hf⟩ := mma_fired hp hX he hub hσ
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv, hk] at hK
  all_goals try exact absurd rfl (hl _)
  · obtain ⟨x, hx⟩ := Mma.ptr_of_ne (hso.1 rfl)
    obtain ⟨bs', hr⟩ := Mma.read_topk hp hx hat' hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_topk hp (ctaid_lt hp g).2 hx hk hr l hc
  · obtain ⟨x, hx⟩ := Mma.ptr_of_ne (hso.2.1 rfl)
    obtain ⟨bs', hr⟩ := Mma.read_extra hp hx hat' hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_extra hp (ctaid_lt hp g).2 hx hk hr l hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

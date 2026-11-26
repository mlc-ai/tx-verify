-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # What an index warp write writes, by its size

Every write of the index warp is a coordinate store (four bytes, the bytes of a 32-bit value) or a
validity store (one byte, the byte of an 8-bit value): the site's event table
(`Index.Ev`) leaves the stores as the only writes of the warp's code. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A write of the index warp** writes the bytes of a 32-bit value into four bytes, or those of
an 8-bit value into one. -/
theorem index_wr_bits (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.IndexAt L g pc) :
    (∃ z, bs = (Value.bits 32 z).toBytes ∧ a.size = 4) ∨
      ∃ z, bs = (Value.bits 8 z).toBytes ∧ a.size = 1 := by
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hr1, hr2⟩ := hat
  obtain ⟨d, n, rfl, -⟩ := index_state hJ hi hev hpc ⟨hr1, hr2⟩
  obtain ⟨⟨-, hk⟩, -, hbits, -⟩ := ix_event hp hX hFw he hσ
  obtain ⟨site, el, ac, c⟩ := d
  cases site <;>
    simp only [Index.EvK, Index.Bits, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
      Index.StoreEv] at hk hbits
  all_goals try (exfalso; simp at hk; done)
  all_goals
    rcases hk with ⟨a', bs', h, -, hs⟩ | ⟨f, h⟩
    swap
    · cases h
    obtain ⟨rfl, rfl⟩ := Kind.wr.inj h
    obtain ⟨a'', z, h''⟩ := hbits
    obtain ⟨rfl, rfl⟩ := Kind.wr.inj h''
    first | exact .inl ⟨z, rfl, hs⟩ | exact .inr ⟨z, rfl, hs⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

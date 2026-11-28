-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ChunkLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Trace
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantWords

@[expose] public section

/-! # A dequantizer lane's write is its chunk store `(r, s)`

A write of a lane of warps 8-11 at a pc of its code is at the pc `dqStorePc r s` of a chunk store
`(r, s)` and writes the 16 bytes at `dqChunk (g % 128) r s` of a dequantized tile of its CTA
(`dequant_wrSite`): the pc of the event is the site's, and the site's location is
`Dequant.store_loc`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow Dequant.Data

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A dequant lane's write is a chunk store**: its pc and its chunk. -/
theorem dequant_wrSite (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.DequantAt L g pc) :
    ∃ (b : Fin 2) (r : Fin 4) (s : Fin 8), pc = dqStorePc r s ∧
      MemRow.WsAcc L (g / L.block) ((Region.dequant b).lo + MemRow.dqChunk (g % 128) r s) 16 a := by
  obtain ⟨hw1, hw2, hlo, hhi⟩ := hat
  have hub : ∀ f, Kind.wr a bs ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, ⟨-, hk⟩, -⟩ := dequant_state hp hJ hi hev hpc ⟨hlo, hhi⟩
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | store r s =>
    rcases hk with ⟨a', bs', hk, hl, hs⟩ | ⟨f, hk⟩
    · simp only [Kind.wr.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [Dequant.store_loc hp] at hl
      refine ⟨Dequant.slotF sb, r, s, ?_, hl, hs⟩
      exact hpc.trans (store_pc r s)
    · cases hk
  | lenA | lenB => rcases hk with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | scale r => rcases hk with ⟨_, _, hk, -⟩ | ⟨_, hk⟩ <;> cases hk
  | raw r s => rcases hk with ⟨_, _, hk, -⟩ | ⟨_, hk⟩ <;> cases hk
  | wq | wraw | wsv => rcases hk with ⟨_, hk⟩ | ⟨_, hk⟩ <;> cases hk
  | smr => obtain ⟨_, hk⟩ := hk; cases hk
  | fpx | arrD | arrF | bar | exit => cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

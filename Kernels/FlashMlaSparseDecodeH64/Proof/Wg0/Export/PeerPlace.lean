-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr

@[expose] public section

/-! # The row-maximum exchange's places

A lane of warpgroup 0 at pc 566 or 1155 writes the four bytes of its own word of `rowMax`
(`221184 + 4 t`), at pc 572 or 1157 it reads the four bytes of its partner's (`221184 + (4 t ^^^
256)`): the kind of the event and its exact place, from the shape table. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem peer_site {s : Wg0.Site}
    (h : s.pc = 566 ∨ s.pc = 572 ∨ s.pc = 1155 ∨ s.pc = 1157) :
    s = .mst ∨ s = .mld ∨ s = .est ∨ s = .eld := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **The exchange's place**: the event at pc 566 or 1155 of lane `g` is a write of its own word
of `rowMax`, the event at 572 or 1157 a read of its partner's. -/
theorem wg0_peerPlace (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hat : MbarRow.Wg0At L g e.pc)
    (hs : e.pc = 566 ∨ e.pc = 572 ∨ e.pc = 1155 ∨ e.pc = 1157) :
    ((e.pc = 566 ∨ e.pc = 1155) → ∃ a bs, e.kind = .wr a bs ∧
      MemRow.WsAcc L (g / L.block) (221184 + 4 * (L.tidOf g).x) 4 a) ∧
    ((e.pc = 572 ∨ e.pc = 1157) → ∃ a bs, e.kind = .rd a bs ∧
      MemRow.WsAcc L (g / L.block) (221184 + (4 * (L.tidOf g).x ^^^ 256)) 4 a) := by
  have ht : tidOf L g < 128 := MemRow.wg0_tid hat.1
  obtain ⟨d, -, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he hub hat.2
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hs
  subst hpc
  rcases peer_site hs with rfl | rfl | rfl | rfl
  · refine ⟨fun _ => ?_, fun h => by simp [Wg0.Site.pc] at h⟩
    rcases hE with ⟨a, bs, hk, hl, hw⟩ | ⟨f, hf⟩
    · exact ⟨a, bs, hk, by rw [hl, Wg0.r13_loc hp ht, Wg0.wsLoc_at]; rfl, hw⟩
    · exact absurd hf (hub f)
  · refine ⟨fun h => by simp [Wg0.Site.pc] at h, fun _ => ?_⟩
    rcases hE with ⟨a, bs, hk, hl, hw⟩ | ⟨f, hf⟩
    · exact ⟨a, bs, hk, by rw [hl, Wg0.r14_loc hp ht, Wg0.wsLoc_at]; rfl, hw⟩
    · exact absurd hf (hub f)
  · refine ⟨fun _ => ?_, fun h => by simp [Wg0.Site.pc] at h⟩
    rcases hE with ⟨a, bs, hk, hl, hw⟩ | ⟨f, hf⟩
    · exact ⟨a, bs, hk, by rw [hl, Wg0.r13_loc hp ht, Wg0.wsLoc_at]; rfl, hw⟩
    · exact absurd hf (hub f)
  · refine ⟨fun h => by simp [Wg0.Site.pc] at h, fun _ => ?_⟩
    rcases hE with ⟨a, bs, hk, hl, hw⟩ | ⟨f, hf⟩
    · exact ⟨a, bs, hk, by rw [hl, Wg0.r14_loc hp ht, Wg0.wsLoc_at]; rfl, hw⟩
    · exact absurd hf (hub f)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

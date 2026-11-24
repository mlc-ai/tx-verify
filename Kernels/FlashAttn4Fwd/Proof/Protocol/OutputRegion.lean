-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Protocol.Region
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The other proxies at the statistics words and the staging buffers

An access of another proxy covering a shared byte is an MMA operand read, a tensor store's
source read, a tensor load's write, a CLC response write or a bulk copy's access
(`Execution.shared_intent`). The kernel has no CLC request or bulk copy (`TmemFacts`); a tensor
load writes a Q or KV ring region (`RingFacts.write`); a tensor store reads a staging buffer
(`OutputFacts.store_tma`); and an MMA operand read of shared memory reads a Q or KV ring region
(`MmaReadsRings`, the region layer's premise: the MMA warp's shared-memory descriptors name only
the ring stages, P being read from Tensor Memory). The ring regions start at offset `68608`, past
the statistics words (`332` to `1356`) and the staging buffers (`3072` to `68608`).

So no access of another proxy touches a statistics byte (`statsAsync`, the premise `hasync` of
`Stats.stats_ordered`), and the accesses of another proxy to a staging byte are tensor-store
source reads (`stagingAsync`, the premise `hasync` of `Output.staging_ordered`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy

noncomputable section

/-- **The MMA region premise**: an MMA operand read of a shared byte reads a Q or KV ring
region. -/
def MmaReadsRings (L : Launch) (X : Execution) : Prop :=
  ∀ i isB idx l, AsyncCovers X i (.mmaRead isB idx) l → l.space = .shared →
    ∃ c b, FBar.isFull b ∧ InRegion L c b l

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A ring region lies past the staging buffers. -/
theorem region_past {c : Nat} {b : FBar} {l : Loc} (hb : b.isFull) (h : InRegion L c b l) :
    L.sharedBase + 68608 ≤ l.addr := by
  obtain ⟨-, -, h1, -⟩ := h
  cases b <;> simp only [FBar.isFull, Bool.false_eq_true] at hb <;>
    simp only [FBar.regionOff] at h1 <;> omega

/-- **An access of another proxy to a shared byte** is past the staging buffers, or a tensor
store's source read of a staging byte. -/
theorem async_shared (hX : Consistent L K A mem0 X) (hr : RingFacts L X) (ho : OutputFacts L X)
    (htm : TmemFacts L X) (hmma : MmaReadsRings L X) {i : EvId} {p : Part} {a : Acc} {w : Bool}
    {l : Loc} (h : X.Intent (.async i p) a w) (hc : a.Covers l) (hs : l.space = .shared) :
    L.sharedBase + 68608 ≤ l.addr ∨ (∃ x y k, p = .read (.store x y k)) ∧ InStaging L l := by
  rcases Execution.shared_intent h hc hs with ⟨e, he, -⟩ | ⟨i', isB, idx, he⟩ |
    ⟨i', x, y, k, he⟩ | ⟨i', x, y, k, he⟩ | ⟨i', c, s, tg, he, ⟨pc, hci⟩, -⟩ |
    ⟨i', q, s, -, ⟨pc, hb⟩⟩ | ⟨i', -, ⟨pc, hb⟩⟩
  · cases he
  · cases he
    obtain ⟨c, b, hb, hreg⟩ := hmma i isB idx l ⟨a, w, h, hc⟩ hs
    exact .inl (region_past hb hreg)
  · cases he
    obtain ⟨-, sp, addr, ⟨pc, hget⟩, hloc, hsz⟩ := h
    obtain ⟨-, st, hst, hsrc⟩ := ho.store_tma (event_thread_lt hX hget) hget
    have hl' := hsrc.2.1 x y k a.loc hloc
    have hla : l = a.loc := by
      obtain ⟨h1, h2, h3, h4⟩ := hc
      rw [hsz] at h4
      cases l
      cases ha : a.loc
      rw [ha] at h1 h2 h3 h4
      simp only at h1 h2 h3 h4
      rw [h1, h2, show _ = _ from Nat.le_antisymm (by omega) h3]
    rw [← hla] at hl'
    obtain ⟨h1, -, h3, h4⟩ := hl'
    exact .inr ⟨⟨x, y, k, rfl⟩, h1, by omega, by omega⟩
  · cases he
    obtain ⟨-, -, -, b, -, hb, -, hreg⟩ := hr.write (g := i.1) (k := i.2) ⟨a, w, h, hc⟩
    exact .inl (region_past hb hreg)
  · exact (htm.no_clc hci).elim
  · exact (htm.no_bulk hb).elim
  · exact (htm.no_prefetch hb).elim

/-- **No access of another proxy touches a statistics byte.** -/
theorem statsAsync (hX : Consistent L K A mem0 X) (hr : RingFacts L X) (ho : OutputFacts L X)
    (htm : TmemFacts L X) (hmma : MmaReadsRings L X) :
    ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStatsArea L l → False := by
  intro i p a w l h hc ⟨hs, h1, h2⟩
  rcases async_shared hX hr ho htm hmma h hc hs with h3 | ⟨-, -, h3, -⟩ <;> omega

/-- **The accesses of another proxy to a staging byte are tensor-store source reads.** -/
theorem stagingAsync (hX : Consistent L K A mem0 X) (hr : RingFacts L X) (ho : OutputFacts L X)
    (htm : TmemFacts L X) (hmma : MmaReadsRings L X) :
    ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStaging L l →
      ∃ x y k, p = .read (.store x y k) := by
  intro i p a w l h hc ⟨hs, h1, h2⟩
  rcases async_shared hX hr ho htm hmma h hc hs with h3 | ⟨hp, -⟩
  · omega
  · exact hp

end
end PTX.Kernels.FlashAttn4Fwd.Proof

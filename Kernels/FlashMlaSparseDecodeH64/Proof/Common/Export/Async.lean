-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorIn
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.MmaPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Foot
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Store
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsyncRef
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutDest

@[expose] public section

/-! # The asynchronous accesses of shared memory, placed

`async_below`: a shared byte an asynchronous stage accesses is a byte of the issuing lane's CTA
between the shared base and the first mbarrier. The stage is an MMA operand read, a tensor
store's source read or a tensor load's destination write (`async_shared_ref`); an MMA or copy is
the MMA warp's (the Tensor Memory rows), a tensor store warpgroup 0's and a tensor load the MMA
or TMA warp's (`tensor_place`, `store_pc`, `load_pc`); their footprints are the rows
`memRow_mmaFoot` (a dequantized tile or the P tile), `wg0_store_below`, `memRow_mmaLoad` (the
query tile) and `tma_gather_raw` (a raw tile). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A byte in a region below the mbarriers. -/
private theorem locIn_below {c : Nat} {r : Region} {l : Loc} (h : MemRow.LocIn L c r l)
    (hr : r.lo + r.size ≤ Region.mbars.lo) :
    l.cta = c ∧ L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + Region.mbars.lo := by
  obtain ⟨-, hc, hlo, hhi⟩ := h
  exact ⟨hc, by omega, by omega⟩

/-- The region of an asynchronous byte, from its accessor (`async_region`). -/
private theorem region_of_ref (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {p : AsyncCopy.Part} {a : Acc}
    (href : AsyncShRef X (g, k) p a) {b : Loc} (hc : a.Covers b) :
    (∃ r, MemRow.LocIn L (g / L.block) (.dequant r) b) ∨
      (MemRow.LocIn L (g / L.block) .pExchange b ∧ ∃ pc bb s acc mask idx,
        X.get (g, k) = some ⟨pc, .tc (.mma bb s acc mask)⟩ ∧ bb < 256 ∧ MmaAt L g pc ∧
          p = .mmaRead false idx ∧ X.MmaFootprint (g, k) false idx b) ∨
      ∃ r, MemRow.LocIn L (g / L.block) (.raw r) b ∧
        ∃ x y j e addr, X.get (g, k) = some e ∧
          ((∃ s, p = .write (.load x y j) ∧ e.kind = .tensorIssue addr s ∧ TmaAt L g e.pc ∧
            TensorCopy.writeLoc s x y j = some b) ∨
          ∃ s, e.kind = .tensorStore addr s ∧ Wg0At L g e.pc ∧
            TensorStore.readLoc s x y j = some b) := by
  have hb : a.size = 1 → b = a.loc := cover_one hc
  rcases href with ⟨isB, idx, hpp, hsz, hf⟩ |
    ⟨x, y, j, s, addr, -, ⟨pc, he⟩, hl, hsz⟩ | ⟨x, y, j, s, addr, hpe, ⟨pc, he⟩, hl, hsz⟩ <;>
    rw [hb hsz]
  · have hR := tmem_rows hp hX hFw
    have hat : ∃ e, X.get (g, k) = some e ∧ MmaAt L g e.pc := by
      rcases hf with ⟨d, s, acc, mk, ⟨pc, he⟩, -⟩ | ⟨c, -, -, ⟨pc, he⟩, -⟩
      · exact ⟨_, he, mma_place hR (Frame.lt_of_get hX he) he rfl (.inl ⟨d, s, acc, mk, rfl⟩)⟩
      · exact ⟨_, he, mma_place hR (Frame.lt_of_get hX he) he rfl (.inr ⟨c, rfl⟩)⟩
    obtain ⟨e, he, hat⟩ := hat
    rcases mmaFoot_pv hp hX hFw (Frame.lt_of_get hX he) he hat hf with
        hr | ⟨hr, -, pc, bb, s, acc, mask, hev, hb, hisB⟩
    · exact .inl hr
    · subst hisB hpp hev
      exact .inr (.inl ⟨hr, pc, bb, s, acc, mask, idx, he, hb, hat, rfl, hf⟩)
  · have hpc : 103 ≤ pc ∧ pc < 1842 := store_pc hX he rfl
    rcases tensor_place hp hX hFw he (.inr ⟨addr, s, rfl⟩) with h | h | h | h | h | h | h
    rotate_left
    · have hw := h.1
      obtain ⟨c, hc4, -, h1, h2, h3, h4⟩ := wg0_store_read hp hX hFw he h rfl hl
      have hoff : MemRow.wg0OutOff c + 8192 ≤ 49152 := by
        have h4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
        rcases h4 with rfl | rfl | rfl | rfl <;> simp [MemRow.wg0OutOff]
      have hw4 : MbarRow.warp L g < 4 := hw
      by_cases hlt : a.loc.addr < L.sharedBase + 65536 + 65536
      · have e1 : (Region.dequant 1).lo = 65536 := rfl
        have e2 : (Region.dequant 1).size = 65536 := rfl
        refine .inl ⟨1, h1, h2, ?_, ?_⟩
        · rw [e1]; omega
        · rw [e1, e2]; exact hlt
      · refine .inr (.inr ⟨0, ⟨h1, h2, ?_, ?_⟩, x, y, j, _, addr, he, .inr ⟨s, rfl, h, hl⟩⟩) <;>
          simp only [Region.lo, Region.size, Fin.val_zero] <;> omega
    all_goals simp only [StartupAt, Wg1At, MmaAt, TmaAt, IndexAt, DequantAt] at h; omega
  · have hpc : 1850 ≤ pc ∧ pc < 2332 := load_pc hX he rfl
    rcases tensor_place hp hX hFw he (.inl ⟨addr, s, rfl⟩) with h | h | h | h | h | h | h
    · simp only [StartupAt] at h; omega
    · simp only [Wg0At] at h; omega
    · simp only [Wg1At] at h; omega
    · exact .inl ⟨0, (memRow_mmaLoad hp hX hFw (Frame.lt_of_get hX he) he h rfl).2 hl⟩
    · obtain ⟨r, hr⟩ := tma_gather_raw hp hX hFw he h rfl hl
      exact .inr (.inr ⟨r, hr, x, y, j, _, addr, he, .inl ⟨s, hpe, rfl, h, hl⟩⟩)
    · simp only [IndexAt] at h; omega
    · simp only [DequantAt] at h; omega

/-- **The region of an asynchronous shared access**: a shared byte an asynchronous stage of event
`(g, k)` accesses is a byte of CTA `g / L.block` in a dequantized tile (an MMA operand, the query
tile or a tensor store's staging source), in the P tile of `pExchange` (an MMA operand), or in a
raw tile (a gather's destination; for the staging source, the row `wg0_store_read` places the
tile by the issuing warp, which this statement does not bound below 2). A raw byte's access is
a TMA gather's write or a staging source read of warpgroup 0. -/
theorem async_region (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {p : AsyncCopy.Part} {a : Acc} {w : Bool}
    (h : X.Intent (.async (g, k) p) a w) {b : Loc} (hc : a.Covers b) (hs : b.space = .shared) :
    (∃ r, MemRow.LocIn L (g / L.block) (.dequant r) b) ∨
      (MemRow.LocIn L (g / L.block) .pExchange b ∧ ∃ pc bb s acc mask idx,
        X.get (g, k) = some ⟨pc, .tc (.mma bb s acc mask)⟩ ∧ bb < 256 ∧ MmaAt L g pc ∧
          p = .mmaRead false idx ∧ X.MmaFootprint (g, k) false idx b) ∨
      ∃ r, MemRow.LocIn L (g / L.block) (.raw r) b ∧
        ∃ x y j e addr, X.get (g, k) = some e ∧
          ((∃ s, p = .write (.load x y j) ∧ e.kind = .tensorIssue addr s ∧ TmaAt L g e.pc ∧
            TensorCopy.writeLoc s x y j = some b) ∨
          ∃ s, e.kind = .tensorStore addr s ∧ Wg0At L g e.pc ∧
            TensorStore.readLoc s x y j = some b) :=
  region_of_ref hp hX hFw (async_shared_ref hX h hc hs) hc

/-- **A shared-memory stage's byte is shared**: a byte an asynchronous stage of the kinds that
`async_region` covers (`AsyncShRef`) accesses is shared. -/
theorem async_shRef_shared (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {p : AsyncCopy.Part} {a : Acc}
    (href : AsyncShRef X (g, k) p a) {b : Loc} (hc : a.Covers b) : b.space = .shared := by
  rcases region_of_ref hp hX hFw href hc with ⟨r, hr⟩ | hr | ⟨r, hr, -⟩
  · exact hr.1
  · exact hr.1.1
  · exact hr.1

/-- **An asynchronous shared access lies below the mbarriers**: a shared byte an asynchronous
stage of event `(g, k)` accesses is a byte of CTA `g / L.block` between the shared base and the
first mbarrier (`async_region`). -/
theorem async_below (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {p : AsyncCopy.Part} {a : Acc} {w : Bool}
    (h : X.Intent (.async (g, k) p) a w) {b : Loc} (hc : a.Covers b) (hs : b.space = .shared) :
    b.cta = g / L.block ∧ L.sharedBase ≤ b.addr ∧ b.addr < L.sharedBase + Region.mbars.lo := by
  rcases async_region hp hX hFw h hc hs with ⟨r, hr⟩ | ⟨hr, -⟩ | ⟨r, hr, -⟩
  · exact locIn_below hr ((by decide : ∀ r : Fin 2,
      (Region.dequant r).lo + (Region.dequant r).size ≤ Region.mbars.lo) r)
  · exact locIn_below hr (by decide)
  · exact locIn_below hr ((by decide : ∀ r : Fin 2,
      (Region.raw r).lo + (Region.raw r).size ≤ Region.mbars.lo) r)

/-- **The map of a tensor load**: the query map (an MMA-warp load, `memRow_mmaLoad`) or the
four-row form of a cache map (a TMA gather, `tma_gather_map`). -/
theorem tensor_load_map (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : EvId} {a : Nat} {s : TensorCopy.Spec}
    (h : X.TensorIssue i a s) :
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩ ∨
      ∃ d0, s.descriptor = TensorMode.fourRows.transfer d0 ∧ KvMap P ⟨s.outer, d0⟩ := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := h
  have hpc : 1850 ≤ pc ∧ pc < 2332 := load_pc hX he rfl
  rcases tensor_place hp hX hFw he (.inl ⟨a, s, rfl⟩) with h | h | h | h | h | h | h
  · simp only [StartupAt] at h; omega
  · simp only [Wg0At] at h; omega
  · simp only [Wg1At] at h; omega
  · exact .inl (memRow_mmaLoad hp hX hFw (Frame.lt_of_get hX he) he h rfl).1
  · exact .inr (tma_gather_map hp hX hFw he h rfl)
  · simp only [IndexAt] at h; omega
  · simp only [DequantAt] at h; omega

/-- **The map of a tensor store**: the output map (a store of warpgroup 0,
`wg0_tensorStore_src`). -/
theorem tensor_store_map (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : EvId} {a : Nat} {s : TensorStore.Spec}
    (h : X.TensorStoreIssue i a s) :
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩ := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := h
  have hpc : 103 ≤ pc ∧ pc < 1842 := store_pc hX he rfl
  rcases tensor_place hp hX hFw he (.inr ⟨a, s, rfl⟩) with h | h | h | h | h | h | h
  rotate_left
  · obtain ⟨-, -, -, -, h⟩ := wg0_tensorStore_src hp hX hFw he h rfl
    exact h
  all_goals simp only [StartupAt, Wg1At, MmaAt, TmaAt, IndexAt, DequantAt] at h; omega

/-- The geometry of a four-row copy is its map's. -/
theorem fourRows_geometry {o : Nat} (d : TensorDescriptor.Descriptor o) :
    TensorDescriptor.geometry (TensorMode.fourRows.transfer d) = TensorDescriptor.geometry d :=
  rfl

/-- **A global byte of an asynchronous stage is allocated**: a tensor load reads, and a tensor
store writes, only in-bounds bytes of its map (`readLoc_lookup`, `writeLoc_lookup`), which are
`Pre`'s input bytes (`tiled_in`, `kv_in`) and allocated output bytes; every other stage's byte
is shared (`async_region`). -/
theorem async_global (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {p : AsyncCopy.Part} {a : Acc} {w : Bool}
    (h : X.Intent (.async (g, k) p) a w) {b : Loc} (hc : a.Covers b)
    (hs : b.space ≠ .shared) : m b ≠ none := by
  rcases async_ref hX h with hr | ⟨x, y, j, s, addr, -, hi, hl, hsz⟩ |
    ⟨x, y, j, s, addr, -, hi, hl, hsz⟩
  · exact absurd (async_shRef_shared hp hX hFw hr hc) hs
  · obtain ⟨coord, byte, ad, hlk, hloc⟩ := writeLoc_lookup hl
    obtain ⟨e, he, q, hq, hh, hhh, t, ht, y', hy', rfl⟩ :=
      tiled_in (d := s.descriptor) (tensor_store_map hp hX hFw hi) hlk
    rw [cover_one hc hsz, hloc]
    rw [Nat.add_assoc]
    exact hp.oAllocated _ (by unfold tensorBytes; exact view_lt he hq hhh ht hy')
  · obtain ⟨coord, byte, ad, hlk, hloc⟩ := readLoc_lookup hl
    rw [cover_one hc hsz, hloc]
    rcases tensor_load_map hp hX hFw hi with hq | ⟨d0, hd, hK⟩
    · obtain ⟨e, he, q, hq, hh, hhh, t, ht, y', hy', rfl⟩ := tiled_in (d := s.descriptor) hq hlk
      intro hn
      have := hp.qInput e he q hq hh hhh t ht y' hy'
      simp only [Loc.at] at this
      rw [hn] at this
      cases this
    · rw [hd, fourRows_geometry] at hlk
      rcases hK with hK | ⟨-, hK⟩
      · obtain ⟨r, hr, y', hy', rfl⟩ := kv_in (d := d0) hK hlk
        intro hn
        have := hp.kvInput r hr y' hy'
        rw [hn] at this
        cases this
      · obtain ⟨r, hr, y', hy', rfl⟩ := kv_in (d := d0) hK hlk
        intro hn
        have := hp.extraKvInput r hr y' hy'
        rw [hn] at this
        cases this

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

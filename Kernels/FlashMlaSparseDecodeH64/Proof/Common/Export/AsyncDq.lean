-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorIn
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.MmaPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Foot
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsyncRef

@[expose] public section

/-! # The asynchronous accesses of a dequantized tile, by kind

`async_dequant` refines `async_region` for a byte of the dequantized tile `r` of the accessing
CTA: the asynchronous access is one of

* an MMA operand read (`mmaRead`; any tile),
* a copy's source read (`mmaRead` of a `tcgen05.cp`; tile 0, the query tile),
* a tensor load's destination write (the query load of the MMA warp; tile 0),
* a tensor store's source read (warpgroup 0's output staging; tile 1).

The only thread accesses of a dequantized byte are writes (a dequant lane's chunk store, any
tile; warpgroup 0's staging store, tile 1), which `Dequant/Export/Mem.lean` and
`Wg0/Export/Mem.lean` state. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The asynchronous accesses of a dequantized tile, by kind.** -/
theorem async_dequant (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {p : AsyncCopy.Part} {a : Acc} {w : Bool}
    (h : X.Intent (.async (g, k) p) a w) {b : Loc} (hc : a.Covers b) {r : Fin 2}
    (hl : MemRow.LocIn L (g / L.block) (.dequant r) b) :
    (w = false ∧ ∃ pc bb s acc mask isB idx,
      X.get (g, k) = some ⟨pc, .tc (.mma bb s acc mask)⟩ ∧ MmaAt L g pc ∧
        p = .mmaRead isB idx ∧ X.MmaFootprint (g, k) isB idx b) ∨
    (w = false ∧ r = 0 ∧ ∃ pc s isB idx, X.get (g, k) = some ⟨pc, .tc (.cp s)⟩ ∧ MmaAt L g pc ∧
        p = .mmaRead isB idx ∧ X.MmaFootprint (g, k) isB idx b) ∨
    (w = true ∧ r = 0 ∧ ∃ x y j pc s addr, X.get (g, k) = some ⟨pc, .tensorIssue addr s⟩ ∧
        MmaAt L g pc ∧ p = .write (.load x y j) ∧ TensorCopy.writeLoc s x y j = some b) ∨
    (w = false ∧ r = 1 ∧ ∃ x y j pc s addr, X.get (g, k) = some ⟨pc, .tensorStore addr s⟩ ∧
        Wg0At L g pc ∧ p = .read (.store x y j) ∧ TensorStore.readLoc s x y j = some b) := by
  have hww : w = p.writes := h.1
  rcases async_shared_ref hX h hc hl.1 with ⟨isB, idx, hpp, hsz, hf⟩ |
    ⟨x, y, j, s, addr, hpp, ⟨pc, he⟩, hrl, hsz⟩ | ⟨x, y, j, s, addr, hpp, ⟨pc, he⟩, hrl, hsz⟩
  · obtain rfl := cover_one hc hsz
    have hwf : w = false := by rw [hww, hpp]; rfl
    have hR := tmem_rows hp hX hFw
    rcases id hf with ⟨d, s, acc, mk, ⟨pc, he⟩, -⟩ | ⟨c, k', cta, ⟨pc, he⟩, -⟩
    · exact .inl ⟨hwf, pc, d, s, acc, mk, isB, idx, he,
        mma_place hR (Frame.lt_of_get hX he) he rfl (.inl ⟨d, s, acc, mk, rfl⟩), hpp, hf⟩
    · have hat := mma_place hR (Frame.lt_of_get hX he) he rfl (.inr ⟨c, rfl⟩)
      have h0 := mmaFoot_cp hp hX hFw (Frame.lt_of_get hX he) he hat hf
      obtain rfl : r = 0 := by
        have h1 := (locIn_eq h0 hl).2
        injection h1 with h2
        exact h2.symm
      exact .inr (.inl ⟨hwf, rfl, pc, c, isB, idx, he, hat, hpp, hf⟩)
  · obtain rfl := cover_one hc hsz
    have hwf : w = false := by rw [hww, hpp]; rfl
    have hpc : 103 ≤ pc ∧ pc < 1842 := store_pc hX he rfl
    rcases tensor_place hp hX hFw he (.inr ⟨addr, s, rfl⟩) with h | h | h | h | h | h | h
    rotate_left
    · obtain ⟨c, hc4, -, h1, h2, h3, h4⟩ := wg0_store_read hp hX hFw he h rfl hrl
      have hr1 : r = 1 := by
        obtain ⟨-, -, hlo, hhi⟩ := hl
        rcases r with ⟨_ | _ | n, hr⟩
        · simp only [Region.lo, Region.size] at hlo hhi
          omega
        · rfl
        · omega
      subst hr1
      exact .inr (.inr (.inr ⟨hwf, rfl, x, y, j, pc, s, addr, he, h, hpp, hrl⟩))
    all_goals simp only [StartupAt, Wg1At, MmaAt, TmaAt, IndexAt, DequantAt] at h; omega
  · obtain rfl := cover_one hc hsz
    have hwf : w = true := by rw [hww, hpp]; rfl
    have hpc : 1850 ≤ pc ∧ pc < 2332 := load_pc hX he rfl
    rcases tensor_place hp hX hFw he (.inl ⟨addr, s, rfl⟩) with h | h | h | h | h | h | h
    · simp only [StartupAt] at h; omega
    · simp only [Wg0At] at h; omega
    · simp only [Wg1At] at h; omega
    · obtain rfl : r = 0 := by
        have h0 := (memRow_mmaLoad hp hX hFw (Frame.lt_of_get hX he) he h rfl).2 hrl
        have h1 := (locIn_eq h0 hl).2
        injection h1 with h2
        exact h2.symm
      exact .inr (.inr (.inl ⟨hwf, rfl, x, y, j, pc, s, addr, he, h, hpp, hrl⟩))
    · obtain ⟨r', hr⟩ := tma_gather_raw hp hX hFw he h rfl hrl
      exact absurd (locIn_eq hr hl).2 (by simp)
    · simp only [IndexAt] at h; omega
    · simp only [DequantAt] at h; omega

/-- **The thread accesses of a dequantized tile are writes**: a store of a dequant lane (any tile)
or a staging store of warpgroup 0 (tile 1, at its place). -/
theorem access_dequant (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {w : Bool} (hI : X.Access (g, k) a w) {b : Loc}
    (hc : a.Covers b) {r : Fin 2} (hl : MemRow.LocIn L (g / L.block) (.dequant r) b) :
    w = true ∧ ∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ ∧
      ((Wg0At L g pc ∧ r = 1 ∧ MemRow.Wg0Stage L g pc a) ∨ DequantAt L g pc) := by
  obtain ⟨e, he, hcase⟩ := access_region hp hX hFw hI hc hl.1
  obtain ⟨ev, hget, -, hm⟩ := access_event hI
  rw [he] at hget
  cases hget
  have hg := Frame.lt_of_get hX he
  have hno : ∀ {r' : Region}, MemRow.LocIn L (g / L.block) r' b → r' ≠ .dequant r → False :=
    fun h hne => hne (locIn_eq h hl).2
  rcases hcase with ⟨-, h⟩ | ⟨hat, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨hat, r', h⟩
  · exact (hno h (by simp)).elim
  · rcases hI with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
      rw [h'] at he <;> cases he
    · rcases memRow_wg0 hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, hr⟩ | ⟨_, _, hk, -⟩ |
        ⟨_, _, hk, -⟩ <;> cases hk
      rcases MemRow.wg0Rd_in hat.1 hr with h1 | h1 | h1 <;>
        exact (hno (h1.locIn hc) (by simp)).elim
    · rcases memRow_wg0 hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, hk, hr⟩ |
        ⟨_, _, hk, hr⟩ <;> cases hk
      · rcases MemRow.wg0Wr_in hat.1 hr with h1 | h1 <;> exact (hno (h1.locIn hc) (by simp)).elim
      · rcases hr with hr | hr
        · have h1 := hc.1
          obtain ⟨-, hs, -⟩ := hr
          rw [hs] at h1
          have := hl.1
          rw [h1] at this
          cases this
        · have h1 := (locIn_eq ((MemRow.wg0Stage_in hat.1 hr).locIn hc) hl).2
          injection h1 with h2
          exact ⟨rfl, _, _, h', .inl ⟨hat, h2.symm, hr⟩⟩
    · rcases memRow_wg0 hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
        ⟨_, _, hk, -⟩ <;> cases hk
  · exact (hno h (by simp)).elim
  · rcases h with h | h
    · exact (hno h (by simp)).elim
    · exact (hno h (by simp)).elim
  · rcases hI with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
      rw [h'] at he <;> cases he
    · rcases memRow_dequant hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, _, hk, hS⟩ |
        ⟨_, _, _, _, _, hk, -⟩ <;> cases hk
      exact (hno (hS.locIn hc) (by simp)).elim
    · exact ⟨rfl, _, _, h', .inr hat⟩
    · rcases memRow_dequant hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, _, hk, -⟩ |
        ⟨_, _, _, _, _, hk, -⟩ <;> cases hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

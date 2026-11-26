-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutBox
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutBoxEq

@[expose] public section

/-! # Warpgroup 0's memory accesses

`memRow_wg0` (`MemRow.Wg0`): from the shape table (`Wg0/Ev.lean`, through `wg0_at`), case by
site; the shared address words are workspace offsets by `Wg0/Addr.lean`, the valid-mask slot is
the block's (`Ref`'s `LoopOk`).

The consumers' facts: `wg0_mem_region` (each shared access lies in `tokenValid`, `pExchange`,
`rowMax` or `dequant 1` of the lane's CTA; the LSE store is its global word) and
`wg0_mem_noMbar` (no access of the lane covers a byte of the mbarriers: the wg0 part of
`bytes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `MemRow.Wg0`**. -/
theorem memRow_wg0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Wg0 P L X := by
  intro g k e _ he hat hm
  obtain ⟨hw4, hr⟩ := hat
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw4
  obtain ⟨d, hR, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (Wg0.memEvent_noUb hm) hr
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc
  subst hpc
  cases s
  case vm =>
    obtain ⟨r, ⟨-, -, -, -, -, hv, -⟩, -⟩ := hc
    obtain ⟨a, bs, hk, hw⟩ := Wg0.rdAt_ws hm hE (Wg0.vm_loc hp ht (d := ⟨.vm, el, a0, l0, l1, cnt,
      bi, vs, pv, sl, ps, vt⟩) hv (Nat.mod_lt _ (by decide)))
    exact .inr (.inl ⟨a, bs, hk, .inl ⟨rfl, r % 4, Nat.mod_lt _ (by decide), hw⟩⟩)
  case pld k =>
    obtain ⟨hel, hE⟩ := hE
    obtain ⟨a, bs, hk, hw⟩ := Wg0.rdAt_ws hm hE (Wg0.r17_loc hp ht k.isLt)
    exact .inr (.inl ⟨a, bs, hk, .inr (.inl ⟨k.val, k.isLt, el, hel, rfl, hw⟩)⟩)
  case mld | eld =>
    obtain ⟨a, bs, hk, hw⟩ := Wg0.rdAt_ws hm hE (Wg0.r14_loc hp ht)
    exact .inr (.inl ⟨a, bs, hk, .inr (.inr ⟨by simp [Wg0.Site.pc], hw⟩)⟩)
  case pst k =>
    obtain ⟨a, bs, hk, hw⟩ := Wg0.wrAt_ws hm hE (Wg0.pst_loc hp ht k)
    exact .inr (.inr (.inl ⟨a, bs, hk, .inl ⟨k.val, k.isLt, rfl, hw⟩⟩))
  case mst | est =>
    obtain ⟨a, bs, hk, hw⟩ := Wg0.wrAt_ws hm hE (Wg0.r13_loc hp ht)
    exact .inr (.inr (.inl ⟨a, bs, hk, .inr (.inl ⟨by simp [Wg0.Site.pc], hw⟩)⟩))
  case ost k =>
    obtain ⟨hel, hE⟩ := hE
    obtain ⟨a, bs, hk, hw⟩ := Wg0.wrAt_ws hm hE (Wg0.r16_loc hp ht k.isLt)
    exact .inr (.inr (.inl ⟨a, bs, hk, .inr (.inr ⟨k.val, k.isLt, el, hel, rfl, hw⟩)⟩))
  case lse =>
    rcases hE with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hf⟩
    · refine .inr (.inr (.inr ⟨a, bs, hk, .inl ⟨rfl, ?_, hs⟩⟩))
      rw [hl, Wg0.lseAddr_eq hp]
      simp only [Arith32.W, BitVec.toNat_ofNat]
      rfl
    · exact absurd hf (Wg0.memEvent_noUb hm f)
  case ost2 c j =>
    obtain ⟨hel, hE⟩ := hE
    rcases hE with ⟨a, bs, hk, hl, hs⟩ | ⟨f, hf⟩
    · refine .inr (.inr (.inr ⟨a, bs, hk, .inr ⟨c.val, c.isLt, j.val, j.isLt, el, hel, rfl, ?_,
        hs⟩⟩))
      have e := Wg0.stW_eq hp ht j.isLt
      have ho : Wg0.ost2Off c = MemRow.wg0OutOff c.val := rfl
      simp only [tidOf] at e
      rw [hl, e, ho]
      simp only [Loc.at, wsLoc, Loc.mk.injEq, true_and]
      omega
    · exact absurd hf (Wg0.memEvent_noUb hm f)
  all_goals
    rcases hm with ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ <;>
    simp [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, Wg0.PollEv, Wg0.ArrEv] at hE ⊢

/-- **Each access lies in an allocated region**: a memory event of a lane of warpgroup 0 is a
non-coherent read, the LSE's global write at its word, or a shared read or write lying in
`tokenValid`, `pExchange`, `rowMax` or (the staging stores) `dequant 1` of the lane's CTA. -/
theorem wg0_mem_region (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hat : MbarRow.Wg0At L g e.pc) (hm : MemRow.MemEvent e) :
    (∃ a bs, e.kind = .nc a bs) ∨ (∃ a bs, e.kind = .wr a bs ∧ MemRow.Wg0Lse P L g e.pc a) ∨
      ∃ (a : Acc) (r : Region), ((∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs) ∧
      ((r = .tokenValid ∨ r = .pExchange ∨ r = .rowMax) ∨ r = .dequant 1) ∧
      MemRow.SharedIn L (g / L.block) r a := by
  have hw := hat.1
  rcases memRow_wg0 hp hX hFw hg he hat hm with h | ⟨a, bs, hk, h⟩ | ⟨a, bs, hk, h⟩ |
    ⟨a, bs, hk, h | h⟩
  · exact .inl h
  · rcases MemRow.wg0Rd_in hw h with h | h | h
    · exact .inr (.inr ⟨a, _, .inl ⟨bs, hk⟩, .inl (.inl rfl), h⟩)
    · exact .inr (.inr ⟨a, _, .inl ⟨bs, hk⟩, .inl (.inr (.inl rfl)), h⟩)
    · exact .inr (.inr ⟨a, _, .inl ⟨bs, hk⟩, .inl (.inr (.inr rfl)), h⟩)
  · rcases MemRow.wg0Wr_in hw h with h | h
    · exact .inr (.inr ⟨a, _, .inr ⟨bs, hk⟩, .inl (.inr (.inl rfl)), h⟩)
    · exact .inr (.inr ⟨a, _, .inr ⟨bs, hk⟩, .inl (.inr (.inr rfl)), h⟩)
  · exact .inr (.inl ⟨a, bs, hk, h⟩)
  · exact .inr (.inr ⟨a, _, .inr ⟨bs, hk⟩, .inr rfl, MemRow.wg0Stage_in hw h⟩)

/-- **No access covers an mbarrier's bytes** (the warpgroup-0 part of `bytes`): a memory event
of a lane of warpgroup 0 is a non-coherent read, a global write, or a shared access ending at or
below the first mbarrier of the lane's CTA. -/
theorem wg0_mem_noMbar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hat : MbarRow.Wg0At L g e.pc) (hm : MemRow.MemEvent e) :
    (∃ a bs, e.kind = .nc a bs) ∨ (∃ a bs, e.kind = .wr a bs ∧ a.loc.space = .global) ∨
      ∃ a : Acc, ((∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs) ∧ a.loc.space = .shared ∧
      a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  rcases wg0_mem_region hp hX hFw hg he hat hm with h | ⟨a, bs, hk, -, hl, -⟩ |
    ⟨a, r, hk, hr | rfl, h⟩
  · exact .inl h
  · exact .inr (.inl ⟨a, bs, hk, by rw [hl]⟩)
  · exact .inr (.inr ⟨a, hk, MemRow.sharedIn_below h hr⟩)
  · obtain ⟨hs, hc, hlo, hhi⟩ := h
    refine .inr (.inr ⟨a, hk, hs, hc, by omega, ?_⟩)
    simp only [Region.lo, Region.size] at hhi ⊢
    omega

/-- **The source of an output TMA store**: a tensor store of a lane of warpgroup 0 is chunk `c`'s
(pcs 1358, 1516, 1673, 1831), reads from `65536 + 16384 w + wg0OutOff c` of the lane's CTA
(`w` the lane's warp) and writes through the O map (`Pre.mapOBind`). -/
theorem wg0_tensorStore_src (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.Wg0At L g e.pc) {a : Nat} {s : TensorStore.Spec}
    (hk : e.kind = .tensorStore a s) :
    ∃ c < 4, e.pc = [1358, 1516, 1673, 1831].getD c 0 ∧
      s.sharedBase =
        wsLoc L (g / L.block) (65536 + 16384 * MbarRow.warp L g + MemRow.wg0OutOff c) ∧
      (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩ := by
  obtain ⟨hw4, hr⟩ := hat
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw4
  obtain ⟨d, -, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (fun f h => by rw [hk] at h; cases h) hr
  obtain ⟨st, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk
  subst hpc hk
  cases st
  case otma c =>
    rcases hE with ⟨a', s', hk', hs', ha, d, hmap, hd, -⟩ | ⟨f, hf⟩
    · cases hk'
      refine ⟨c.val, c.isLt, by fin_cases c <;> rfl, by rw [hs', Wg0.otma_loc hp ht c]; rfl, ?_⟩
      have hr := hp.param1Range
      have ha' : a = P.param1Base + 512 := by
        rw [ha, Flow.Arith32.W, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [ha', hp.mapOBind, Option.some.injEq] at hmap
      rw [hd, hmap]
    · cases hf
  all_goals simp [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, Wg0.PollEv, Wg0.ArrEv, RdAt, WrAt,
    GenWrAt, GWrAt] at hE

/-- **The source bytes of an output TMA store**: chunk `c`'s store of a lane of warpgroup 0 reads
slot `(x, y, z)` (column, row, byte) from the byte
`128 y + 16 ((x / 8) ^^^ y % 8) + 2 (x % 8) + z` of its 8192-byte tile at
`65536 + 16384 w + wg0OutOff c` (`w` the lane's warp), the place of the staging store `x / 8`,
element `(2 (x % 8) + z) / 4` of thread `64 w + y` (`MemRow.Wg0Stage`). -/
theorem wg0_store_readEq (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.Wg0At L g e.pc) {a : Nat} {s : TensorStore.Spec}
    (hk : e.kind = .tensorStore a s) :
    ∃ c < 4, e.pc = [1358, 1516, 1673, 1831].getD c 0 ∧ ∀ x y z, x < 64 → y < 64 → z < 2 →
      TensorStore.readLoc s x y z = some (wsLoc L (g / L.block) (65536 + 16384 *
        MbarRow.warp L g + MemRow.wg0OutOff c +
        (128 * y + 16 * ((x / 8) ^^^ (y % 8)) + 2 * (x % 8) + z))) := by
  obtain ⟨hw4, hr⟩ := hat
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw4
  obtain ⟨d, -, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (fun f h => by rw [hk] at h; cases h) hr
  obtain ⟨st, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk
  subst hpc hk
  cases st
  case otma c =>
    rcases hE with ⟨a', s', hk', hs', ha, dd, hdd, hde, -⟩ | ⟨f, hf⟩
    · cases hk'
      have hW : (Flow.Arith32.W (P.param1Base + 512)).toNat = P.param1Base + 512 :=
        Nat.mod_eq_of_lt (by have := hp.param1Range; omega)
      rw [ha, hW, hp.mapOBind, Option.some.injEq] at hdd
      have hsb : s.sharedBase =
          wsLoc L (g / L.block) (65536 + 16384 * MbarRow.warp L g + MemRow.wg0OutOff c) := by
        rw [hs', Wg0.otma_loc hp ht c]
        rfl
      have hal : s.sharedBase.addr % 1024 = 0 := by
        have h1 := hp.sharedAlignment
        have h2 : MemRow.wg0OutOff c % 1024 = 0 := by fin_cases c <;> decide
        rw [hsb]
        simp only [wsLoc, hp.sharedBase]
        omega
      have hd : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
          ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩ := by
        rw [hde]
        exact hdd.symm
      refine ⟨c.val, c.isLt, by fin_cases c <;> rfl, fun x y z hx hy hz => ?_⟩
      obtain ⟨slot, h1, h2, h3, hsl⟩ := outDesc_slot hd hx hy hz
      have hl := outBox_sharedLoc_eq hd hal slot
      simp only [TensorStore.readLoc, hsl, Option.map_some, Option.some.injEq]
      rw [hl, h1, h2, h3]
      simp only [hsb, wsLoc, Loc.mk.injEq, true_and]
      omega
    · cases hf
  all_goals simp [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, Wg0.PollEv, Wg0.ArrEv, RdAt, WrAt,
    GenWrAt, GWrAt] at hE

/-- **The source bytes of an output TMA store**: chunk `c`'s store of a lane of warpgroup 0 reads
each slot from byte `y` of element `el` of the 16-byte chunk `k ^^^ h % 8` of row `h` of its
8192-byte tile at `65536 + 16384 w + wg0OutOff c` (`w` the lane's warp), the place of the
staging store `k`, element `el` of thread `64 w + h` (`MemRow.Wg0Stage`). -/
theorem wg0_tensorStore_slot (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.Wg0At L g e.pc) {a : Nat} {s : TensorStore.Spec}
    (hk : e.kind = .tensorStore a s) :
    ∃ c < 4, e.pc = [1358, 1516, 1673, 1831].getD c 0 ∧ ∀ slot, ∃ h < 64, ∃ k < 8, ∃ el < 4,
      ∃ y < 4, s.sharedLoc slot = wsLoc L (g / L.block) (65536 + 16384 * MbarRow.warp L g +
        MemRow.wg0OutOff c + (128 * h + 16 * (k ^^^ h % 8) + 4 * el + y)) := by
  obtain ⟨hw4, hr⟩ := hat
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw4
  obtain ⟨d, -, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (fun f h => by rw [hk] at h; cases h) hr
  obtain ⟨st, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk
  subst hpc hk
  cases st
  case otma c =>
    rcases hE with ⟨a', s', hk', hs', ha, dd, hdd, hde, -⟩ | ⟨f, hf⟩
    · cases hk'
      have hW : (Flow.Arith32.W (P.param1Base + 512)).toNat = P.param1Base + 512 :=
        Nat.mod_eq_of_lt (by have := hp.param1Range; omega)
      rw [ha, hW, hp.mapOBind, Option.some.injEq] at hdd
      have hsb : s.sharedBase =
          wsLoc L (g / L.block) (65536 + 16384 * MbarRow.warp L g + MemRow.wg0OutOff c) := by
        rw [hs', Wg0.otma_loc hp ht c]
        rfl
      have hal : s.sharedBase.addr % 1024 = 0 := by
        have h1 := hp.sharedAlignment
        have h2 : MemRow.wg0OutOff c % 1024 = 0 := by fin_cases c <;> decide
        rw [hsb]
        simp only [wsLoc, hp.sharedBase]
        omega
      have hd : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
          ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩ := by
        rw [hde]
        exact hdd.symm
      refine ⟨c.val, c.isLt, by fin_cases c <;> rfl, fun slot => ?_⟩
      obtain ⟨h, hh, k, hk8, el, hel, y, hy, hl⟩ := outBox_sharedLoc hd hal slot
      refine ⟨h, hh, k, hk8, el, hel, y, hy, ?_⟩
      rw [hl]
      simp only [hsb, wsLoc, Loc.mk.injEq, true_and]
      omega
    · cases hf
  all_goals simp [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, Wg0.PollEv, Wg0.ArrEv, RdAt, WrAt,
    GenWrAt, GWrAt] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

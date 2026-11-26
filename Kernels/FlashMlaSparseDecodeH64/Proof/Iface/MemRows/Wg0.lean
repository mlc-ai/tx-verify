-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Wg0 producer=W1 status=row-proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0

@[expose] public section

/-! # Warpgroup 0: memory classification row

Warpgroup 0's code (pcs 103–1841) makes non-coherent reads (the sink and the two lengths),
shared reads (the valid mask, the P exchange, the row sums), shared writes (the P tile stores,
the row-sum exchange, the output staging stores) and the LSE's global write (`Wg0/Ev.lean`), and
no read-modify-write: `MemRow.Wg0`, proved by `memRow_wg0` (`Wg0/Export/Mem.lean`).

## Inventory of the access sites (read from the PTX)

Notation: `S` the dynamic shared base, `t` the thread's index in the warpgroup (`%r5`, below 128),
`w = t / 32` the warp (`%r7`), `l = t % 32` the lane (`%r8`), `vs` the valid-mask slot (below 4),
`el` the element of a vector access. Offsets are bytes from `S`; regions are `Iface/Regions.lean`'s.

Each entry: site, pc, kind and bytes, region, address as the code computes it.

* `sink` (156), `.nc` 4 B global: `sinkBase + 4 (t % 64)` (`%rd149`, pcs 150–155);
* `lenA` (168), `lenB` (181), `.nc` 4 B global: `topkLenBase + 4 ctaid.y`,
  `extraTopkLenBase + 4 ctaid.y` (`%rd151`, `%rd153`);
* `vm` (289), shared read 4 B, `tokenValid`: `221696 + 8 vs + 4 [w > 1]` (`%r543`);
* `pst k` (403 + 10 k), shared write 16 B (`b128`), `pExchange`:
  `204800 + 4096 (w ^^^ 2) + 16 l + 512 k` (`%r530 + k`: the other warp pair's quadrant);
* `pld k` (477 + 5 k), shared read 2 × 8 B (`v2.b64`), `pExchange`:
  `204800 + 4096 w + 16 l + 512 k + 8 el` (`%r17` plus the offset);
* `mst` (566) and `est` (1155), shared write 4 B, `rowMax`: `221184 + 4 t` (`%r13`);
* `mld` (572) and `eld` (1157), shared read 4 B, `rowMax`: `221184 + (4 t ^^^ 256)` (`%r14`,
  the other warp pair's row);
* `ost k` (704 + k), shared write 4 × 4 B (`v4.b32`), `pExchange` (the P tile, its first 8192
  bytes): `204800 + 4096 (w / 2) + 512 (w % 2) + 16 l + 1024 k + 4 el` (`%r16`);
* `lse` (1178), global write 4 B: `lseBase + 4 (s_q · 64 · ctaid.y + 64 · ctaid.x + t)`
  (`%rd585`);
* `ost2 c k` (`ost2Base c + k`), generic write to shared 4 × 4 B (`v4.b32`), `dequant 1` (the
  `qo` member's output staging): `65536 + 16384 (t / 64) + 128 (t % 64) + 16 (k ^^^ t % 8) +
  [0, 8192, 32768, 40960][c] + 4 el` (`%rd3 + k`: `cvta.shared` at 110, the swizzle 114–145);
* `otma c` (1358, 1516, 1673, 1831), tensor store reading 8192 B of shared, `dequant 1`:
  `65536 + 16384 w + [0, 8192, 32768, 40960][c]` (`%r25`; warps 0 and 1, the elected lane).

The rescale arm's loads and stores (`rld`, `rst`) and the score and output loads (`sld`, `old`)
are Tensor Memory accesses, not memory events. The mbarrier sites name objects in `mbars`
(`arrL` 222768, `wv`/`arrV` 222840/222872 + 8 vs, `wq`/`arrS`/`wsv` 222904/222920/222936 + 8 sl).
The two P writers of the `pExchange` bytes: `pst` writes the other warp pair's quadrant
(`w ^^^ 2`), `ost` the P tile `[204800, 212992)`, which overlaps quadrants 0 and 1; the protocol
orders them by the named barriers.

## The row

`MemRow.Wg0`: every memory event of a lane of warpgroup 0 at a pc of its code is a non-coherent
read (`sink`, `lenA`, `lenB`), a shared read at its exact place (`MemRow.Wg0Rd`: `vm`, `pld`,
`mld`, `eld`), a shared write at its exact place (`MemRow.Wg0Wr`: `pst`, `mst`, `est`, `ost`),
the LSE's global write at its word (`MemRow.Wg0Lse`; inside the LSE output for `t < 64`,
`wg0Lse_in`), or a staging store at its swizzled place (`MemRow.Wg0Stage`: in `dequant 1`,
`wg0Stage_in`; inside its chunk's TMA source box, `wg0Stage_box`; pairwise disjoint,
`wg0Ost2_inj`). The exact places lie in `tokenValid`, `pExchange` and
`rowMax`, below the mbarriers (`wg0Rd_in`, `wg0Wr_in`, `wg0Rd_below`, `wg0Wr_below`).

**What the row does not say**: the tensor stores' sources (`wg0_tensorStore_src`), the `.nc`
reads' addresses; that the LSE store's lane has `t < 64`; no value. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

namespace MemRow

/-- The shared reads of warpgroup 0's lane `g` at pc `pc`, by site family (`t` the thread's index,
`w = t / 32` its warp, `t % 32` its lane): the valid-mask word of a slot `v`, the peer read `k`'s
element `el`, the other warp pair's row. -/
def Wg0Rd (L : Launch) (g pc : Nat) (a : Acc) : Prop :=
  (pc = 289 ∧ ∃ v < 4, WsAcc L (g / L.block)
    (221696 + 8 * v + 4 * ((L.tidOf g).x / 32 / 2)) 4 a) ∨
  (∃ k < 8, ∃ el < 2, pc = 477 + 5 * k ∧ WsAcc L (g / L.block)
    (204800 + 4096 * ((L.tidOf g).x / 32) + 16 * ((L.tidOf g).x % 32) + 512 * k + 8 * el) 8 a) ∨
  ((pc = 572 ∨ pc = 1157) ∧ WsAcc L (g / L.block) (221184 + (4 * (L.tidOf g).x ^^^ 256)) 4 a)

/-- The shared writes of warpgroup 0's lane `g` at pc `pc`, by site family: the peer store `k`
(the other warp pair's quadrant), the row maximum or sum, the P store `k`'s element `el`. -/
def Wg0Wr (L : Launch) (g pc : Nat) (a : Acc) : Prop :=
  (∃ k < 8, pc = 403 + 10 * k ∧ WsAcc L (g / L.block)
    (204800 + 4096 * ((L.tidOf g).x / 32 ^^^ 2) + 16 * ((L.tidOf g).x % 32) + 512 * k) 16 a) ∨
  ((pc = 566 ∨ pc = 1155) ∧ WsAcc L (g / L.block) (221184 + 4 * (L.tidOf g).x) 4 a) ∨
  (∃ k < 4, ∃ el < 4, pc = 704 + k ∧ WsAcc L (g / L.block)
    (204800 + 4096 * ((L.tidOf g).x / 32 / 2) + 512 * ((L.tidOf g).x / 32 % 2) +
      16 * ((L.tidOf g).x % 32) + 1024 * k + 4 * el) 4 a)

/-- The offset of output chunk `c`'s 8192-byte staging tile from the warp's (the TMA store's
source, `[0, 8192, 32768, 40960]`). -/
def wg0OutOff (c : Nat) : Nat := [0, 8192, 32768, 40960].getD c 0

/-- The staging stores of lane `g` at pc `pc`: chunk `c`'s store `k`, element `el`, at its row
of the warp quadrant `t / 64` (`t` the thread's index), its 16-byte chunk swizzled by the row's
three low bits (SW128). -/
def Wg0Stage (L : Launch) (g pc : Nat) (a : Acc) : Prop :=
  ∃ c < 4, ∃ k < 8, ∃ el < 4, pc = [1331, 1491, 1649, 1806].getD c 0 + k ∧
    WsAcc L (g / L.block) (65536 + 16384 * ((L.tidOf g).x / 64) + 128 * ((L.tidOf g).x % 64) +
      16 * (k ^^^ (L.tidOf g).x % 8) + wg0OutOff c + 4 * el) 4 a

/-- The LSE's global write of lane `g` (pc 1178): the 4-byte word of row
`64 (s_q ctaid.y + ctaid.x) + t` of the LSE output, as the 64-bit address word wraps it. -/
def Wg0Lse (P : Params) (L : Launch) (g pc : Nat) (a : Acc) : Prop :=
  pc = 1178 ∧ a.loc = ⟨.global, 0, (P.lseBase + 4 * (((L.ctaidOf (g / L.block)).y % 2 ^ 32 *
    P.s_q + (L.ctaidOf (g / L.block)).x % 2 ^ 32) * 64 + (L.tidOf g).x % 128)) % 2 ^ 64⟩ ∧
    a.size = 4

/-- A thread of the warpgroup has an index below 128. -/
theorem wg0_tid {L : Launch} {g : Nat} (h : warp L g < 4) : (L.tidOf g).x < 128 := by
  unfold warp at h
  omega

/-- **A read's place lies in its region**: `tokenValid`, `pExchange` or `rowMax`. -/
theorem wg0Rd_in {L : Launch} {g pc : Nat} {a : Acc} (hw : warp L g < 4) (h : Wg0Rd L g pc a) :
    SharedIn L (g / L.block) .tokenValid a ∨ SharedIn L (g / L.block) .pExchange a ∨
      SharedIn L (g / L.block) .rowMax a := by
  have ht := wg0_tid hw
  rcases h with ⟨-, v, hv, h⟩ | ⟨k, hk, el, hel, -, h⟩ | ⟨-, h⟩
  · exact .inl (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega))
  · exact .inr (.inl (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega)))
  · have hx : 4 * (L.tidOf g).x ^^^ 256 < 512 :=
      Nat.xor_lt_two_pow (n := 9) (by omega) (by omega)
    have h4 : (4 * (L.tidOf g).x ^^^ 256) % 2 ^ 2 = 0 := by
      rw [Nat.xor_mod_two_pow]
      simp only [Nat.reducePow, Nat.reduceMod, Nat.mul_mod_right, Nat.xor_self]
    exact .inr (.inr (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega)))

/-- **A write's place lies in its region**: `pExchange` or `rowMax`. -/
theorem wg0Wr_in {L : Launch} {g pc : Nat} {a : Acc} (hw : warp L g < 4) (h : Wg0Wr L g pc a) :
    SharedIn L (g / L.block) .pExchange a ∨ SharedIn L (g / L.block) .rowMax a := by
  have ht := wg0_tid hw
  rcases h with ⟨k, hk, -, h⟩ | ⟨-, h⟩ | ⟨k, hk, el, hel, -, h⟩
  · have hx : (L.tidOf g).x / 32 ^^^ 2 < 4 := Nat.xor_lt_two_pow (n := 2) (by omega) (by omega)
    exact .inl (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega))
  · exact .inr (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega))
  · exact .inl (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega))

/-- A place in `tokenValid`, `pExchange` or `rowMax` ends below the mbarriers. -/
theorem sharedIn_below {L : Launch} {c : Nat} {r : Region} {a : Acc} (h : SharedIn L c r a)
    (hr : r = .tokenValid ∨ r = .pExchange ∨ r = .rowMax) :
    a.loc.space = .shared ∧ a.loc.cta = c ∧ L.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  obtain ⟨hs, hc, hlo, hhi⟩ := h
  refine ⟨hs, hc, by omega, ?_⟩
  rcases hr with rfl | rfl | rfl <;> simp only [Region.lo, Region.size] at hhi ⊢ <;> omega

/-- **The peer stores of a warpgroup are pairwise disjoint**: two threads' 16-byte stores `k`, `k'`
at the same place are the same thread's same store (so, 16-aligned, distinct places are
disjoint). -/
theorem wg0Pst_inj {t t' k k' : Nat} (ht : t < 128) (ht' : t' < 128) (hk : k < 8) (hk' : k' < 8)
    (h : 4096 * (t / 32 ^^^ 2) + 16 * (t % 32) + 512 * k =
      4096 * (t' / 32 ^^^ 2) + 16 * (t' % 32) + 512 * k') : t = t' ∧ k = k' := by
  have hw : ∀ u < 128, u / 32 ^^^ 2 = [2, 3, 0, 1].getD (u / 32) 0 := by
    intro u hu
    rcases (by omega : u / 32 = 0 ∨ u / 32 = 1 ∨ u / 32 = 2 ∨ u / 32 = 3) with e | e | e | e <;>
      simp [e]
  rw [hw t ht, hw t' ht'] at h
  rcases (by omega : t / 32 = 0 ∨ t / 32 = 1 ∨ t / 32 = 2 ∨ t / 32 = 3) with e | e | e | e <;>
  rcases (by omega : t' / 32 = 0 ∨ t' / 32 = 1 ∨ t' / 32 = 2 ∨ t' / 32 = 3) with
    e' | e' | e' | e' <;>
  simp only [e, e', List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at h <;> omega

/-- **The P stores of a warpgroup are pairwise disjoint**: two threads' 4-byte elements at the same
place are the same thread's same store and element. -/
theorem wg0Ost_inj {t t' k k' el el' : Nat} (ht : t < 128) (ht' : t' < 128) (hk : k < 4)
    (hk' : k' < 4) (he : el < 4) (he' : el' < 4)
    (h : 4096 * (t / 32 / 2) + 512 * (t / 32 % 2) + 16 * (t % 32) + 1024 * k + 4 * el =
      4096 * (t' / 32 / 2) + 512 * (t' / 32 % 2) + 16 * (t' % 32) + 1024 * k' + 4 * el') :
    t = t' ∧ k = k' ∧ el = el' := by
  omega

/-- **The LSE store lies in the LSE output** for a lane of the first two warps (the code stores
the LSE only there, `t < 64`) of a CTA of the `(s_q, b)` grid. -/
theorem wg0Lse_in {P : Params} {L : Launch} {g pc : Nat} {a : Acc}
    (hr : P.lseBase + lseBytes P ≤ 2 ^ 64) (hy : (L.ctaidOf (g / L.block)).y % 2 ^ 32 < P.b)
    (hx : (L.ctaidOf (g / L.block)).x % 2 ^ 32 < P.s_q) (ht : (L.tidOf g).x % 128 < 64)
    (h : Wg0Lse P L g pc a) : LseIn P a := by
  obtain ⟨-, hl, hs⟩ := h
  generalize (L.ctaidOf (g / L.block)).y % 2 ^ 32 = y at hy hl
  generalize (L.ctaidOf (g / L.block)).x % 2 ^ 32 = x at hx hl
  generalize (L.tidOf g).x % 128 = t at ht hl
  have hrow : (y * P.s_q + x) * 64 + t + 1 ≤ P.b * P.s_q * 64 := by
    have : y * P.s_q + x + 1 ≤ P.b * P.s_q := by
      calc y * P.s_q + x + 1 ≤ y * P.s_q + P.s_q := by omega
        _ = (y + 1) * P.s_q := by ring
        _ ≤ P.b * P.s_q := Nat.mul_le_mul_right _ hy
    nlinarith
  unfold lseBytes at hr
  have hlt : P.lseBase + 4 * ((y * P.s_q + x) * 64 + t) < 2 ^ 64 := by nlinarith
  rw [Nat.mod_eq_of_lt hlt] at hl
  refine ⟨by rw [hl], by rw [hl]; dsimp only; omega, ?_⟩
  rw [hl, hs]
  dsimp only
  unfold lseBytes
  nlinarith

/-- The swizzled chunk index is below 8. -/
theorem swz_lt {k t : Nat} (hk : k < 8) : k ^^^ t % 8 < 8 :=
  Nat.xor_lt_two_pow (n := 3) hk (Nat.mod_lt _ (by decide))

/-- **A staging store lies in `dequant 1`** (the `qo` member's output staging). -/
theorem wg0Stage_in {L : Launch} {g pc : Nat} {a : Acc} (hw : warp L g < 4)
    (h : Wg0Stage L g pc a) : SharedIn L (g / L.block) (.dequant 1) a := by
  have ht := wg0_tid hw
  obtain ⟨c, hc, k, hk, el, hel, -, h⟩ := h
  have hx := swz_lt (t := (L.tidOf g).x) hk
  have ho : wg0OutOff c ≤ 40960 := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> decide
  exact wsAcc_in h (by simp only [Region.lo]; omega)
    (by simp only [Region.lo, Region.size]; omega)

/-- **The staging stores of a warpgroup are pairwise disjoint**: two threads' 4-byte elements at
the same place are the same thread's same chunk, store and element. -/
theorem wg0Ost2_inj {t t' c c' k k' el el' : Nat} (ht : t < 128) (ht' : t' < 128) (hc : c < 4)
    (hc' : c' < 4) (hk : k < 8) (hk' : k' < 8) (he : el < 4) (he' : el' < 4)
    (h : 16384 * (t / 64) + 128 * (t % 64) + 16 * (k ^^^ t % 8) + wg0OutOff c + 4 * el =
      16384 * (t' / 64) + 128 * (t' % 64) + 16 * (k' ^^^ t' % 8) + wg0OutOff c' + 4 * el') :
    t = t' ∧ c = c' ∧ k = k' ∧ el = el' := by
  have hx := swz_lt (t := t) hk
  have hx' := swz_lt (t := t') hk'
  have hcc : c = c' := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c' = 0 ∨ c' = 1 ∨ c' = 2 ∨ c' = 3) with rfl | rfl | rfl | rfl <;>
    simp only [wg0OutOff, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some] at h <;> omega
  subst hcc
  have htt : t = t' := by omega
  subst htt
  have hkk : k ^^^ t % 8 = k' ^^^ t % 8 := by omega
  have key : ∀ a < 8, ∀ b < 8, ∀ h < 8, a ^^^ h = b ^^^ h → a = b := by decide
  exact ⟨rfl, rfl, key k hk k' hk' (t % 8) (Nat.mod_lt _ (by decide)) hkk, by omega⟩

end MemRow

/-- **Row `MemRow.Wg0`**: a memory event of warpgroup 0 is a non-coherent read, a shared read or
write at its exact place, the LSE's global write at its word or a staging store at its swizzled
place; never a read-modify-write. -/
def MemRow.Wg0 (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → Wg0At L g e.pc →
    MemRow.MemEvent e → (∃ a bs, e.kind = .nc a bs) ∨
      (∃ a bs, e.kind = .rd a bs ∧ MemRow.Wg0Rd L g e.pc a) ∨
      (∃ a bs, e.kind = .wr a bs ∧ MemRow.Wg0Wr L g e.pc a) ∨
      ∃ a bs, e.kind = .wr a bs ∧ (MemRow.Wg0Lse P L g e.pc a ∨ MemRow.Wg0Stage L g e.pc a)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Flow.Counted
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Cnt9
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0CntP
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region

@[expose] public section

/-! # Warpgroup 0's accesses of the P exchange between the barriers' events

The bytes of `pExchange` (204800 + `o`) are accessed by warpgroup 0's threads at three families of
sites (`pst`, `pld`, `ost`; the other warpgroup-0 accesses lie in other regions). Block `r` of the
lane (`r` below the CTA's block count) has them between its barriers (ordinals `3 r`: barrier 9,
`3 r + 1`: the warp pair's barrier `10 + p`, `3 r + 2`: barrier 9):

* `pst k` (403 + 10 k): after `2 r + 1` barrier-9 events and `r` of the pair's, writing the 16
  bytes `4096 (w ^^^ 2) + 16 l + 512 k` (`w` the warp, `l` the lane);
* `pld k` (477 + 5 k): after `2 r + 1` and `r + 1`, reading 8 bytes `4096 w + 16 l + 512 k + 8 el`;
* `ost k` (704 + k): after `2 r + 2` and `r + 1`, writing 4 bytes
  `4096 (w / 2) + 512 (w % 2) + 16 l + 1024 k + 4 el`.

`PexUse` states the place and the counts of one access; `wg0_pexUse` proves it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **One access of the P exchange**: the lane `t` of the CTA (its thread index), a write or a
read of the byte at offset `o` of the region, after `n9` barrier-9 events and `np` of its pair's. -/
def PexUse (t : Nat) (w : Bool) (o r n9 np : Nat) : Prop :=
  (w = true ∧ n9 = 2 * r + 1 ∧ np = r ∧ ∃ j < 8,
    4096 * (t / 32 ^^^ 2) + 16 * (t % 32) + 512 * j ≤ o ∧
    o < 4096 * (t / 32 ^^^ 2) + 16 * (t % 32) + 512 * j + 16) ∨
  (w = false ∧ n9 = 2 * r + 1 ∧ np = r + 1 ∧ ∃ j < 8, ∃ el < 2,
    4096 * (t / 32) + 16 * (t % 32) + 512 * j + 8 * el ≤ o ∧
    o < 4096 * (t / 32) + 16 * (t % 32) + 512 * j + 8 * el + 8) ∨
  (w = true ∧ n9 = 2 * r + 2 ∧ np = r + 1 ∧ ∃ j < 4, ∃ el < 4,
    4096 * (t / 32 / 2) + 512 * (t / 32 % 2) + 16 * (t % 32) + 1024 * j + 4 * el ≤ o ∧
    o < 4096 * (t / 32 / 2) + 512 * (t / 32 % 2) + 16 * (t % 32) + 1024 * j + 4 * el + 4)

/-- **The score ring's uses at block `r`'s exchange sites**: the lane's successful polls of
`qkDone j` are the uses of slot `j` among blocks `0 … r`, its arrivals on `soReady j` those
among blocks `0 … r - 1`. -/
def PexBlk (L : Launch) (X : Execution) (g k r : Nat) : Prop :=
  ∀ j : Fin 2, okPolls (mbarLoc L (g / L.block) (.qkDone j)) ((X.tr g).take k) =
      ringUses 2 j (r + 1) ∧
    arrivals (mbarLoc L (g / L.block) (.soReady j)) ((X.tr g).take k) = ringUses 2 j r

/-- The pcs of the exchange sites. -/
def PexPc (pc : Nat) : Prop :=
  (∃ j < 8, pc = 403 + 10 * j ∨ pc = 477 + 5 * j) ∨ ∃ j < 4, pc = 704 + j

private theorem pex_site {s : Wg0.Site} (h : PexPc s.pc) :
    (∃ j, s = .pst j) ∨ (∃ j, s = .pld j) ∨ ∃ j, s = .ost j := by
  revert h
  cases s
  case pst k => exact fun _ => .inl ⟨k, rfl⟩
  case pld k => exact fun _ => .inr (.inl ⟨k, rfl⟩)
  case ost k => exact fun _ => .inr (.inr ⟨k, rfl⟩)
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals (intro h; exfalso; revert h; unfold PexPc; decide)

/-- **The counts before an exchange site**: block `r`'s (`r` below the block count). -/
theorem pex_cnt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {kd : Kind} (hub : ∀ f, kd ≠ .ub f)
    (he : X.get (g, k) = some ⟨pc, kd⟩) (hr : 103 ≤ pc ∧ pc < 1842) (hw : warp L g < 4)
    (hs : PexPc pc) :
    ∃ r < blocksOf P L (g / L.block),
      (pc < 477 → ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 1 ∧
        ((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2)) = r) ∧
      (477 ≤ pc → pc < 704 → ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 1 ∧
        ((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1) ∧
      (704 ≤ pc → ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * r + 2 ∧
        ((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1) ∧
      PexBlk L X g k r := by
  obtain ⟨d, hRf, ⟨hpc, -⟩, hw'⟩ := wg0_at hp hX hFw he hub hr
  obtain ⟨hC, hL, -, ht⟩ := hRf (wg0_take_noUb hX he)
  have hB : w0BarCnt X g k = Wg0.barOrd d := ht
  have hp2 : warp L g % 2 < 2 := Nat.mod_lt _ (by omega)
  have h9 := w0_idCnt hp hX hFw hw (le_refl 9) (by omega) k
    (noUbBefore_of_get hX he)
  have h10 := w0_idCnt hp hX hFw hw (id := 10 + warp L g % 2) (by omega) (by omega) k
    (noUbBefore_of_get hX he)
  rw [hB] at h9 h10
  simp only at hpc
  have hsite := pex_site (s := d.site) (by rw [← hpc]; exact hs)
  have hl2 : 2 ≤ d.site.lens := by
    rcases hsite with ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, h⟩ <;> rw [h] <;> exact le_rfl
  have hk : d.site.reg = Wg0.Reg.loop := by
    rcases hsite with ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, h⟩ <;> rw [h] <;> rfl
  obtain ⟨r, hrR, ho, hq, ha⟩ := barOrd_loop hC hL hk hl2
  dsimp only at hq ha
  have hidx : 2 ≤ d.site.idx := by
    rcases hsite with ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, h⟩ <;> rw [h] <;> simp [Wg0.Site.idx]
  have hblk : PexBlk L X g k r := fun j => by
    constructor
    · rw [show mbarLoc L (g / L.block) (.qkDone j) = loc L g (.qkDone j) from rfl,
        wg0_okPolls hp hX hFw hw, hq (loc L g (.qkDone j)), Wg0.acq_qk hp]
      unfold Wg0.use Wg0.ind ringUses
      have := j.isLt
      split_ifs <;> omega
    · rw [show mbarLoc L (g / L.block) (.soReady j) = loc L g (.soReady j) from rfl,
        wg0_arrivals hp hX hFw hw, ha (loc L g (.soReady j)), Wg0.arr_so hp]
  refine ⟨r, hrR, ?_⟩
  rcases hsite with ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, h⟩ <;> rw [h] at ho hpc <;>
    simp only [Wg0.Site.bidx] at ho <;> simp only [Wg0.Site.pc] at hpc <;>
    rw [ho] at h9 h10 <;> have hj := j.isLt
  · rw [w0Cnt9_pst _ _ hrR] at h9
    rw [(w0CntP_site _ _ hrR).1] at h10
    exact ⟨fun _ => ⟨h9, h10⟩, fun h1 _ => by omega, fun h1 => by omega, hblk⟩
  · rw [(w0Cnt9_site _ _ hrR).1] at h9
    rw [(w0CntP_site _ _ hrR).2.1] at h10
    exact ⟨fun h1 => by omega, fun _ _ => ⟨h9, h10⟩, fun h1 => by omega, hblk⟩
  · rw [(w0Cnt9_site _ _ hrR).2] at h9
    rw [(w0CntP_site _ _ hrR).2.2] at h10
    exact ⟨fun h1 => by omega, fun h1 h2 => by omega, fun _ => ⟨h9, h10⟩, hblk⟩

/-- **A warpgroup-0 access of a `pExchange` byte** is a peer store, a peer load or a P store of a
block `r` of the CTA (`PexUse`), not a barrier event, of a lane of the first four warps. -/
theorem wg0_pexUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} {a : Acc} {w : Bool} {l : Loc}
    (he : X.get (g, k) = some e) (hat : Wg0At L g e.pc) (hi : X.Access (g, k) a w)
    (hc : a.Covers l) (hl : MemRow.LocIn L (g / L.block) .pExchange l) :
    warp L g < 4 ∧ Execution.isBarId 9 e = false ∧
      Execution.isBarId (10 + warp L g % 2) e = false ∧ l.cta = g / L.block ∧
      (w = true → ∃ bs, X.Writes (g, k) a bs) ∧
      (∃ r < blocksOf P L (g / L.block), PexUse (g % L.block) w (l.addr - L.sharedBase - 204800) r
        (((X.tr g).take k).countP (Execution.isBarId 9))
        (((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2))) ∧
        PexBlk L X g k r) ∧
      (w = true → (((X.tr g).take k).countP (Execution.isBarId 9) % 2 = 0 ↔
        ∃ j < 4, e.pc = 704 + j)) := by
  have hg := Frame.lt_of_get hX he
  have ht := MemRow.wg0_tid hat.1
  have htx : (L.tidOf g).x = g % L.block := by rw [tidOf_x_eq hp, hp.block]
  obtain ⟨ev, hev, -, hm⟩ := access_event hi
  rw [he] at hev
  cases hev
  have hl0 := hl
  have hc0 := hc
  obtain ⟨hls, hlc, hl1, hl2⟩ := hl
  obtain ⟨hcs, -, hc1, hc2⟩ := hc
  simp only [Region.lo, Region.size] at hl1 hl2
  rw [htx] at ht
  rcases hi with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
    rw [h'] at he <;> cases he <;>
    rcases memRow_wg0 hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, hrd⟩ |
      ⟨_, _, hk, hwr⟩ | ⟨_, _, hk, hlse | hst⟩ <;> cases hk
  · have hnb9 : Execution.isBarId 9 ⟨pc, .rd a bs⟩ = false := by simp [Execution.isBarId]
    have hnbp : Execution.isBarId (10 + warp L g % 2) ⟨pc, .rd a bs⟩ = false := by
      simp [Execution.isBarId]
    rcases hrd with ⟨-, v, hv, hl'⟩ | ⟨j, hj, el, hel, hpc, hl'⟩ | ⟨-, hl'⟩
    · obtain ⟨hl', hsz⟩ := hl'
      rw [hl', htx] at hc1 hc2
      rw [hsz] at hc2
      simp only [wsLoc] at hc1 hc2
      omega
    · simp only at hpc
      obtain ⟨r, hr, -, h2, -, hb⟩ := pex_cnt hp hX hFw (fun _ h => by cases h) h' hat.2 hat.1
        (.inl ⟨j, hj, .inr hpc⟩)
      obtain ⟨hl', hsz⟩ := hl'
      rw [hl', htx] at hc1 hc2
      rw [hsz] at hc2
      simp only [wsLoc] at hc1 hc2
      obtain ⟨h9, hP⟩ := h2 (by omega) (by omega)
      exact ⟨hat.1, hnb9, hnbp, hlc, (fun h => by cases h),
        ⟨r, hr, .inr (.inl ⟨rfl, h9, hP, j, hj, el, hel, by omega, by omega⟩), hb⟩,
        fun h => by cases h⟩
    · obtain ⟨hl', hsz⟩ := hl'
      rw [hl', htx] at hc1 hc2
      rw [hsz] at hc2
      simp only [wsLoc] at hc1 hc2
      omega
  · have hnb9 : Execution.isBarId 9 ⟨pc, .wr a bs⟩ = false := by simp [Execution.isBarId]
    have hnbp : Execution.isBarId (10 + warp L g % 2) ⟨pc, .wr a bs⟩ = false := by
      simp [Execution.isBarId]
    rcases hwr with ⟨j, hj, hpc, hl'⟩ | ⟨-, hl'⟩ | ⟨j, hj, el, hel, hpc, hl'⟩
    · simp only at hpc
      obtain ⟨r, hr, h1, -, -, hb⟩ := pex_cnt hp hX hFw (fun _ h => by cases h) h' hat.2 hat.1
        (.inl ⟨j, hj, .inl hpc⟩)
      obtain ⟨hl', hsz⟩ := hl'
      rw [hl', htx] at hc1 hc2
      rw [hsz] at hc2
      simp only [wsLoc] at hc1 hc2
      obtain ⟨h9, hP⟩ := h1 (by omega)
      exact ⟨hat.1, hnb9, hnbp, hlc, fun _ => ⟨bs, pc, h'⟩,
        ⟨r, hr, .inl ⟨rfl, h9, hP, j, hj, by omega, by omega⟩, hb⟩,
        fun _ => ⟨fun h => by omega, fun ⟨j', hj', h⟩ => by simp only at h; omega⟩⟩
    · obtain ⟨hl', hsz⟩ := hl'
      rw [hl', htx] at hc1 hc2
      rw [hsz] at hc2
      simp only [wsLoc] at hc1 hc2
      omega
    · simp only at hpc
      obtain ⟨r, hr, -, -, h3, hb⟩ := pex_cnt hp hX hFw (fun _ h => by cases h) h' hat.2 hat.1
        (.inr ⟨j, hj, hpc⟩)
      obtain ⟨hl', hsz⟩ := hl'
      rw [hl', htx] at hc1 hc2
      rw [hsz] at hc2
      simp only [wsLoc] at hc1 hc2
      obtain ⟨h9, hP⟩ := h3 (by omega)
      exact ⟨hat.1, hnb9, hnbp, hlc, fun _ => ⟨bs, pc, h'⟩,
        ⟨r, hr, .inr (.inr ⟨rfl, h9, hP, j, hj, el, hel, by omega, by omega⟩), hb⟩,
        fun _ => ⟨fun _ => ⟨j, hj, hpc⟩, fun _ => by omega⟩⟩
  · obtain ⟨-, hl', -⟩ := hlse
    have hcs' : l.space = a.loc.space := hcs
    rw [hl', hls] at hcs'
    cases hcs'
  · have := locIn_eq ((MemRow.wg0Stage_in hat.1 hst).locIn hc0) hl0
    cases this.2

/-- **An exiting lane of warpgroup 0 made all its pair barrier's events** (one per block; it
passed all `3 R + 7` role barriers, `w0_lagB`). -/
theorem wg0_pairExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {y j pcx : Nat} (hw : warp L y < 4)
    (he : X.get (y, j) = some ⟨pcx, .exit⟩) :
    blocksOf P L (y / L.block) ≤ (X.tr y).countP (Execution.isBarId (10 + warp L y % 2)) := by
  have hy := Frame.lt_of_get hX he
  have hB : 3 * blocksOf P L (y / L.block) + 7 ≤ w0BarCnt X y (X.tr y).length := by
    by_contra hlt
    exact (w0_lagB hp hX hFw hw hy (B := 3 * blocksOf P L (y / L.block) + 6) le_rfl
      (by omega) (LaneUbFree.of_exit hX hy he)).1 j pcx he
  have hp2 : warp L y % 2 < 2 := Nat.mod_lt _ (by omega)
  have hc := w0_idCnt hp hX hFw hw (id := 10 + warp L y % 2) (by omega) (by omega)
    (X.tr y).length (LaneUbFree.of_exit hX hy he)
  rw [List.take_length] at hc
  rw [hc]
  have h1 := w0IdCnt_mono (R := blocksOf P L (y / L.block)) (p := warp L y % 2)
    (id := 10 + warp L y % 2) hB
  rw [w0CntP_epi _ hp2 7 (le_refl 7)] at h1
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

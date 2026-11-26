-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorIn
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.GatherDst
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Won
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Lemmas.Tensor.BoxNone

@[expose] public section

/-! # The TMA warp's gathers: their shared destinations

`tma_gather_dst`: a byte a gather of the TMA lane writes lies in the 2304 bytes at
`131072 + 36864 b + 2304 q` of the lane's CTA (raw tile `b`, gather `q`), so in the raw region
`raw b` (`tma_gather_raw`). The gather's destination and box are `Tma.gather_dst`; its state is
`tma_gather_at` (`Common/TmaLen.lean`). A gather reads global memory (`tensor_readLoc_global`).
`tma_gatherUse`: the gather (past the election) is gather `q` of use `u` of its tile `b`, on
`rawReady b`, after
`16 u + q` loads on it and `u + 1` successful polls of `rawFree b` (the reference counts at the
gather's state, `Tma.tcnt_gather`, `Tma.tcnt_free`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The box of a TMA gather: raw tile `b`, gather `q`, unswizzled, 2304 bytes, through a cache
map (`Tma.gather_dst`, at the gather's state `tma_gather_at`). -/
private theorem gather_spec (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.TmaAt L g e.pc) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) :
    ∃ b < 2, ∃ q < 16,
      s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + (36864 * b + (131072 + 2304 * q))⟩ ∧
      s.descriptor.swizzle = .none ∧ TensorTile.rows s.descriptor.box *
        (TensorTile.count s.descriptor.box 0 * s.descriptor.format.bytes) = 2304 ∧
      ∃ d0, s.descriptor = TensorMode.fourRows.transfer d0 ∧ KvMap P ⟨s.outer, d0⟩ := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [hk] at h; cases h
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, -, -, ⟨hpc, hE⟩, hl', -⟩ := tma_at hp hX hFw he hub hr
  obtain ⟨i, hs⟩ := Tma.ev_gather hl' ⟨hpc, hE⟩ hk
  have hpcR : 2165 < e.pc ∧ e.pc < 2332 := by
    rw [hpc, hs]
    exact (by decide : ∀ i : Fin 16, 2165 < (Tma.Site.gather i).pc ∧
      (Tma.Site.gather i).pc < 2332) i
  obtain ⟨d', t, ins, o, q, hat', hs', hc, hf, hmain, hL, -⟩ := tma_gather_at hp hX hFw he hpcR hk
  obtain ⟨-, -, -, -, -, hbuf, -⟩ := hL
  obtain ⟨h1, h2, h3, d0, h4, h5⟩ :=
    Tma.gather_dst hp hat' hs' hc hf hmain (Nat.mod_lt d'.cnt.toNat (by decide)) hbuf hk
  exact ⟨_, Nat.mod_lt d'.cnt.toNat (by decide), q.val, q.isLt, h1, h2, h3, d0, h4, h5.kvMap⟩

/-- **The destination of a TMA gather**: byte `(x, y, j)` of a tensor load of the TMA lane lies in
the 2304 bytes of gather `q` of raw tile `b` of the lane's CTA. -/
theorem tma_gather_dst (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.TmaAt L g e.pc) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) {x y j : Nat} {l : Loc}
    (hl : TensorCopy.writeLoc s x y j = some l) :
    ∃ b < 2, ∃ q < 16, l.space = .shared ∧ l.cta = g / L.block ∧
      L.sharedBase + (131072 + 36864 * b + 2304 * q) ≤ l.addr ∧
      l.addr < L.sharedBase + (131072 + 36864 * b + 2304 * q) + 2304 := by
  obtain ⟨b, hb, q, hq, hsb, hsw, hsz, -⟩ := gather_spec hp hX hFw he hat hk
  obtain ⟨h1, h2, h3, h4⟩ := TensorCopy.writeLoc_none hsw hl
  rw [hsz, hsb] at h4
  rw [hsb] at h1 h2 h3
  refine ⟨b, hb, q, hq, h1, h2, ?_, ?_⟩ <;> simp only at h3 h4 <;> omega

/-- **A TMA gather reads through a cache map**: its descriptor is the four-row form of the main
cache's map or, with the extra cache on, the extra cache's (`Pre.mapKVBind`,
`Pre.mapExtraKvBind`). -/
theorem tma_gather_map (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.TmaAt L g e.pc) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) :
    ∃ d0, s.descriptor = TensorMode.fourRows.transfer d0 ∧ KvMap P ⟨s.outer, d0⟩ := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := gather_spec hp hX hFw he hat hk
  exact h

/-- **A TMA gather writes its raw tile**: every byte a tensor load of the TMA lane writes lies in
`raw b` of the lane's CTA for some `b`. -/
theorem tma_gather_raw (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.TmaAt L g e.pc) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) {x y j : Nat} {l : Loc}
    (hl : TensorCopy.writeLoc s x y j = some l) :
    ∃ b : Fin 2, MemRow.LocIn L (g / L.block) (.raw b) l := by
  obtain ⟨b, hb, q, hq, h1, h2, h3, h4⟩ := tma_gather_dst hp hX hFw he hat hk hl
  refine ⟨⟨b, hb⟩, h1, h2, ?_, ?_⟩ <;> simp only [Region.lo, Region.size] <;> omega

/-- **The use of a TMA gather**: a tensor load of the TMA lane is gather `q` of a use `u` of raw
tile `b`: its barrier is `rawReady b`, its box the 2304 unswizzled bytes of gather `q` of tile
`b`, and the lane has made `16 u + q` earlier loads on `rawReady b` and `u + 1` successful
polls of `rawFree b`. -/
theorem tma_gatherUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.TmaAt L g e.pc) {a : Nat} {s : TensorCopy.Spec}
    (hk : e.kind = .tensorIssue a s) :
    2165 < e.pc ∧ ∃ b : Fin 2, ∃ q < 16, ∃ u, s.mbar = mbarLoc L (g / L.block) (.rawReady b) ∧
      s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + (36864 * b.val + (131072 + 2304 * q))⟩ ∧
      s.descriptor.swizzle = .none ∧ TensorTile.rows s.descriptor.box *
        (TensorTile.count s.descriptor.box 0 * s.descriptor.format.bytes) = 2304 ∧
      ((X.tr g).take k).countP (issuesTo (mbarLoc L (g / L.block) (.rawReady b))) = 16 * u + q ∧
      okPolls (mbarLoc L (g / L.block) (.rawFree b)) ((X.tr g).take k) = u + 1 := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [hk] at h; cases h
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, -, -, ⟨hpc, hE⟩, hl', hw⟩ := tma_at hp hX hFw he hub hr
  obtain ⟨i, hs⟩ := Tma.ev_gather hl' ⟨hpc, hE⟩ hk
  have hpcR : 2165 < e.pc ∧ e.pc < 2332 := by
    rw [hpc, hs]
    exact (by decide : ∀ i : Fin 16, 2165 < (Tma.Site.gather i).pc ∧
      (Tma.Site.gather i).pc < 2332) i
  obtain ⟨d', t, ins, o, q, hat', hs', hc, hf, hmain, hL, hev, hn⟩ :=
    tma_gather_at hp hX hFw he hpcR hk
  have hL' := hL
  obtain ⟨-, -, -, -, -, hbuf, -⟩ := hL'
  have hb2 := Nat.mod_lt d'.cnt.toNat (by decide : 0 < 2)
  obtain ⟨hsb, hsw, hsz, -⟩ := Tma.gather_dst hp hat' hs' hc hf hmain hb2 hbuf hk
  obtain ⟨-, hK⟩ := hev
  simp only [Tma.EvK, hs'] at hK
  obtain ⟨a', s', hK, hmb⟩ | ⟨f, hK⟩ := hK
  · rw [hk] at hK
    simp only [Kind.tensorIssue.injEq] at hK
    obtain ⟨-, rfl⟩ := hK
    refine ⟨hpcR.1, MbarRow.slot2 d'.cnt.toNat, q.val, q.isLt,
      ringUses 2 (MbarRow.slot2 d'.cnt.toNat) d'.cnt.toNat,
      hmb.trans ((Tma.raw_of hbuf).trans (Tma.raw_loc hp (MbarRow.slot2 d'.cnt.toNat))), hsb, hsw,
      hsz, ?_, ?_⟩
    · show ((X.tr g).take k).countP
        (issuesTo (MbarRow.loc L g (.rawReady (MbarRow.slot2 d'.cnt.toNat)))) = _
      rw [lane5_issues hp hX hFw hw, hn _ (by simp), Tma.tcnt_gather hp]
      simp [Tma.ind, hs', Tma.Site.gN, MbarRow.slot2]
    · show okPolls (MbarRow.loc L g (.rawFree (MbarRow.slot2 d'.cnt.toNat))) _ = _
      rw [lane5_okPolls hp hX hFw hw, hn _ (by simp), Tma.tcnt_free hp]
      simp [Tma.useAt, Tma.ind, hs', Tma.Site.stage, MbarRow.slot2]
  · rw [hk] at hK
    cases hK

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

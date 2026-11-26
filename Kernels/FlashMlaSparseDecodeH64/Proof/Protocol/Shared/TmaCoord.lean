-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.Handoff
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Use
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Use

@[expose] public section

/-! # The TMA coordinates are ordered

The bytes of `tmaCoord` (`221728 + 256 s + o`, `o < 256`, slot `s < 4` of the index ring) are
accessed only by threads (`region_thread`): the index lanes' writes of their coordinate pairs
(`access_region`, `index_wrUse`; lane `t` writes the bytes `8 (t % 32) … + 8` of each slot) and the
TMA thread's coordinate reads (`tma_rdUse`). By the per-use counts of these exports, a byte of slot
`s` of CTA `c` is a ring byte of `coordReady s` / `coordFree s` (`coordReady_handoff`,
`coordFree_handoff`) with the CTA's index lanes as producers and its consumers (warpgroup 0's
lanes and the TMA thread) as consumers; two writes of a byte are one lane's (the byte names the
lane). So `ring_ordered` orders the region (`tmaCoord_ordered`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The ring slot of a byte of `tmaCoord`. -/
def coordSlotOf (L : Launch) (l : Loc) : Fin 4 :=
  ⟨(l.addr - L.sharedBase - 221728) / 256 % 4, Nat.mod_lt _ (by decide)⟩

/-- The index lane writing a byte of `tmaCoord`, as its lane in the warp. -/
def coordLaneOf (L : Launch) (l : Loc) : Nat := (l.addr - L.sharedBase - 221728) % 256 / 8

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)

include hp hX hFw hN in
/-- **The classes of an access of `tmaCoord`**: an index lane's write of the byte's slot with its
write counts, naming the lane by the byte; or a consumer's read of the byte's slot with its read
counts. -/
theorem coord_cls {c g k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access (g, k) a w) (hc : a.Covers l) (hl : MemRow.LocIn L c .tmaCoord l) :
    (w = true ∧ IdxOf L l.cta g ∧ g % L.block % 32 = coordLaneOf L l ∧
      (∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ ∧ MbarRow.IndexAt L g pc) ∧
      ∃ u, arrivals (mbarLoc L l.cta (.coordReady (coordSlotOf L l))) ((X.tr g).take k) = u ∧
        okPolls (mbarLoc L l.cta (.coordFree (coordSlotOf L l))) ((X.tr g).take k) = u + 1) ∨
    (w = false ∧ ConsOf L X l.cta g ∧
      ∃ u, okPolls (mbarLoc L l.cta (.coordReady (coordSlotOf L l))) ((X.tr g).take k) = u + 1 ∧
        arrivals (mbarLoc L l.cta (.coordFree (coordSlotOf L l))) ((X.tr g).take k) = u) := by
  obtain ⟨e, he, hr⟩ := access_region hp hX hFw hi hc hl.1
  have hg := Frame.lt_of_get hX he
  have hl0 := hl
  obtain ⟨-, hlc, hl1, hl2⟩ := hl
  obtain ⟨-, hcc, hc1, hc2⟩ := hc
  simp only [Region.lo, Region.size] at hl1 hl2
  obtain ⟨ev, hev, -, hm⟩ := access_event hi
  rw [he] at hev
  cases hev
  rcases hr with ⟨-, h⟩ | ⟨-, (h | h | h) | h⟩ | ⟨hat, h⟩ | ⟨hat, h | h⟩ | ⟨-, b, h | h⟩
  rotate_left 5
  -- the TMA thread's read
  · have hcta : l.cta = g / L.block := hlc.trans (locIn_eq h hl0).1.symm
    rcases hi with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
      rw [h'] at he <;> cases he
    · obtain ⟨hpc, s, ⟨q, hq, j, hj, hl', hsz⟩, u, h1, h2⟩ := tma_rdUse hp hX hFw h' hat
      have hs : coordSlotOf L l = s := by
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc, coordSlotOf, Fin.ext_iff] at hc1 hc2 ⊢
        omega
      rw [hs, hcta]
      refine .inr ⟨rfl, ⟨hg, ⟨128, by omega⟩, ?_⟩, u, h1, h2⟩
      simp only [coordCons, show ¬ (128 < 128) from by omega, ↓reduceIte]
      exact tma_thread_on hN.tmaOne h' (fun _ h => by cases h) ⟨hat, hpc⟩
    all_goals
      rcases memRow_tma hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, -⟩ <;> cases hk
  -- an index lane's write
  · have hcta : l.cta = g / L.block := hlc.trans (locIn_eq h hl0).1.symm
    rcases hi with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
      rw [h'] at he <;> cases he
    rotate_left
    · obtain ⟨s, hpl, u, h1, h2⟩ := index_wrUse hp hX hFw h' hat
      rw [tidOf_x_eq hp] at hpl
      rcases hpl with ⟨j, hj, hl', hsz⟩ | hl'
      · have hs : coordSlotOf L l = s ∧ g % L.block % 32 = coordLaneOf L l := by
          rw [hl'] at hc1 hc2
          rw [hsz] at hc2
          simp only [wsLoc, coordSlotOf, coordLaneOf, Fin.ext_iff, hp.block] at hc1 hc2 ⊢
          omega
        obtain ⟨hs, hln⟩ := hs
        rw [hs, hcta]
        exact .inl ⟨rfl, ⟨hg, idx_lane hp hat⟩, hln, ⟨pc, bs, h', hat⟩, u, h1, h2⟩
      · obtain ⟨⟨hl', hsz⟩, -⟩ := hl'
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc] at hc1 hc2
        omega
    all_goals
      rcases memRow_index hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, -⟩ <;> cases hk
  all_goals exact absurd (locIn_eq h hl0).2 (by simp)

include hp hX hFw hN in
/-- Two writes of a byte of `tmaCoord` are one index lane's: the byte names the lane. -/
theorem coord_ww {c g k g' k' : Nat} {a b : Acc} {l : Loc} (hi : X.Access (g, k) a true)
    (hj : X.Access (g', k') b true) (ha : a.Covers l) (hb : b.Covers l)
    (hl : MemRow.LocIn L c .tmaCoord l) : g = g' := by
  rcases coord_cls hp hX hFw hN hi ha hl with ⟨-, ⟨-, a1, rfl⟩, h1, -⟩ | ⟨h, -⟩
  · rcases coord_cls hp hX hFw hN hj hb hl with ⟨-, ⟨-, a2, rfl⟩, h2, -⟩ | ⟨h, -⟩
    · have := a1.isLt
      have := a2.isLt
      simp only [idxLane, hp.block] at h1 h2 ⊢
      omega
    · cases h
  · cases h

include hp hX hFw hR hI hB hN in
/-- **The TMA coordinates are ordered.** -/
theorem tmaCoord_ordered : RegionOrdered L X .tmaCoord :=
  ring_ordered (F := fun l => mbarLoc L l.cta (.coordReady (coordSlotOf L l)))
    (E := fun l => mbarLoc L l.cta (.coordFree (coordSlotOf L l)))
    (prod := fun l => IdxOf L l.cta) (cons := fun l => ConsOf L X l.cta)
    (fun l _ => coordReady_handoff hp hX hFw hR hI hB hN l.cta _)
    (fun l _ => coordFree_handoff hp hX hFw hR hI hB hN l.cta _)
    (fun _ _ _ _ hi hc ⟨_, hl⟩ =>
      region_thread hp hX hFw (by simp) (by simp) (by simp) hi hc hl)
    (fun _ _ _ _ _ hi hc ⟨_, hl⟩ => (coord_cls hp hX hFw hN hi hc hl).imp
      (fun ⟨h1, h2, _, _, h3⟩ => ⟨h1, h2, h3⟩) id)
    (fun _ _ _ _ _ _ _ hi hj ha hb ⟨_, hl⟩ => coord_ww hp hX hFw hN hi hj ha hb hl)

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

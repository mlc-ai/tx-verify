-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.Handoff
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Use
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Use

@[expose] public section

/-! # The token-validity bytes are ordered

The bytes of `tokenValid` (`221696 + 8 s + o`, `o < 8`, slot `s < 4` of the index ring) are
accessed only by threads (`region_thread`): the index lanes' validity stores (`index_wrUse`: lane
`t` with `t % 4 = 0` writes the byte `(t % 32) / 4` of each slot) and warpgroup 0's validity reads
at pc 289 (`wg0_vmUse`; the other reads and writes of warpgroup 0 lie in `pExchange`, `rowMax`,
`dequant 1` or global memory). As for `tmaCoord` (`Protocol/Shared/TmaCoord.lean`), a byte of slot
`s` of CTA `c` is a ring byte of `coordReady s` / `coordFree s`, and two writes of a byte are one
lane's (the byte names the lane `4 o`), so `ring_ordered` orders the region
(`tokenValid_ordered`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The ring slot of a byte of `tokenValid`. -/
def validSlotOf (L : Launch) (l : Loc) : Fin 4 :=
  ⟨(l.addr - L.sharedBase - 221696) / 8 % 4, Nat.mod_lt _ (by decide)⟩

/-- The index lane writing a byte of `tokenValid`, as its lane in the warp. -/
def validLaneOf (L : Launch) (l : Loc) : Nat := 4 * ((l.addr - L.sharedBase - 221696) % 8)

/-- A read of warpgroup 0 covering a validity byte is the validity read at 289. -/
private theorem rd_vm {g pc c : Nat} {a : Acc} {l : Loc} (hw : MbarRow.warp L g < 4)
    (h : MemRow.Wg0Rd L g pc a) (hc : a.Covers l) (hl : MemRow.LocIn L c .tokenValid l) :
    pc = 289 := by
  have ht := MemRow.wg0_tid hw
  obtain ⟨-, -, hl1, hl2⟩ := hl
  obtain ⟨-, -, hc1, hc2⟩ := hc
  simp only [Region.lo, Region.size] at hl1 hl2
  rcases h with ⟨h, -⟩ | ⟨k, hk, el, hel, -, hl', hsz⟩ | ⟨-, hl', hsz⟩
  · exact h
  · rw [hl'] at hc1 hc2
    rw [hsz] at hc2
    simp only [wsLoc] at hc1 hc2
    omega
  · have hx : 4 * (L.tidOf g).x ^^^ 256 < 512 :=
      Nat.xor_lt_two_pow (n := 9) (by omega) (by omega)
    have h4 : (4 * (L.tidOf g).x ^^^ 256) % 2 ^ 2 = 0 := by
      rw [Nat.xor_mod_two_pow]
      simp only [Nat.reducePow, Nat.reduceMod, Nat.mul_mod_right, Nat.xor_self]
    rw [hl'] at hc1 hc2
    rw [hsz] at hc2
    simp only [wsLoc] at hc1 hc2
    omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)

include hp hX hFw hN in
/-- **The classes of an access of `tokenValid`**: an index lane's write of the byte's slot with
its write counts, naming the lane by the byte; or a consumer's read of the byte's slot with its
read counts. -/
theorem valid_cls {c g k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access (g, k) a w) (hc : a.Covers l) (hl : MemRow.LocIn L c .tokenValid l) :
    (w = true ∧ IdxOf L l.cta g ∧ g % L.block % 32 = validLaneOf L l ∧
      (∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ ∧ MbarRow.IndexAt L g pc) ∧ ∃ u,
        arrivals (mbarLoc L l.cta (.coordReady (validSlotOf L l))) ((X.tr g).take k) = u ∧
        okPolls (mbarLoc L l.cta (.coordFree (validSlotOf L l))) ((X.tr g).take k) = u + 1) ∨
    (w = false ∧ ConsOf L X l.cta g ∧
      ∃ u, okPolls (mbarLoc L l.cta (.coordReady (validSlotOf L l))) ((X.tr g).take k) = u + 1 ∧
        arrivals (mbarLoc L l.cta (.coordFree (validSlotOf L l))) ((X.tr g).take k) = u) := by
  obtain ⟨e, he, hr⟩ := access_region hp hX hFw hi hc hl.1
  have hg := Frame.lt_of_get hX he
  have hl0 := hl
  have hc0 := hc
  obtain ⟨hls, hlc, hl1, hl2⟩ := hl
  obtain ⟨hcs, hcc, hc1, hc2⟩ := hc
  simp only [Region.lo, Region.size] at hl1 hl2
  obtain ⟨ev, hev, -, hm⟩ := access_event hi
  rw [he] at hev
  cases hev
  have hout : ∀ {r : Region} {a' : Acc}, r ≠ .tokenValid →
      MemRow.SharedIn L (g / L.block) r a' → a'.Covers l → False := fun hne h hc' =>
    hne (locIn_eq (h.locIn hc') hl0).2
  rcases hr with ⟨-, h⟩ | ⟨hat, (h | h | h) | h⟩ | ⟨hat, h⟩ | ⟨hat, h | h⟩ | ⟨-, b, h | h⟩
  rotate_left
  -- warpgroup 0's read
  · have hcta : l.cta = g / L.block := hlc.trans (locIn_eq h hl0).1.symm
    rcases hi with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
      rw [h'] at he <;> cases he <;>
      rcases memRow_wg0 hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, hrd⟩ |
        ⟨_, _, hk, hwr⟩ | ⟨_, _, hk, hlse | hst⟩ <;> cases hk
    · obtain ⟨s, hws, u, h1, h2⟩ := wg0_vmUse hp hX hFw h' hat (rd_vm hat.1 hrd hc0 hl0)
      obtain ⟨hl', hsz⟩ := hws
      have hs : validSlotOf L l = s := by
        rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        have ht := MemRow.wg0_tid hat.1
        simp only [wsLoc, validSlotOf, Fin.ext_iff] at hc1 hc2 ⊢
        omega
      obtain ⟨b, hb⟩ := coord_cons (l := l) hp hN.tmaOne h' (fun _ h => by cases h) (.inl hat)
      rw [hs, hcta]
      exact .inr ⟨rfl, ⟨hg, b, hb⟩, u, h1, h2⟩
    · rcases MemRow.wg0Wr_in hat.1 hwr with h1 | h1 <;> exact (hout (by simp) h1 hc0).elim
    · obtain ⟨-, hl', -⟩ := hlse
      rw [hl'] at hcs
      simp only at hcs
      rw [hcs] at hls
      cases hls
    · exact (hout (by simp) (MemRow.wg0Stage_in hat.1 hst) hc0).elim
  rotate_left 5
  -- an index lane's write
  · have hcta : l.cta = g / L.block := hlc.trans (locIn_eq h hl0).1.symm
    rcases hi with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
      rw [h'] at he <;> cases he
    rotate_left
    · obtain ⟨s, hpl, u, h1, h2⟩ := index_wrUse hp hX hFw h' hat
      rw [tidOf_x_eq hp] at hpl
      rcases hpl with ⟨j, hj, hl', hsz⟩ | ⟨⟨hl', hsz⟩, h4⟩
      · rw [hl'] at hc1 hc2
        rw [hsz] at hc2
        simp only [wsLoc] at hc1 hc2
        omega
      · have hs : validSlotOf L l = s ∧ g % L.block % 32 = validLaneOf L l := by
          rw [hl'] at hc1 hc2
          rw [hsz] at hc2
          simp only [wsLoc, validSlotOf, validLaneOf, Fin.ext_iff, hp.block] at hc1 hc2 ⊢
          omega
        obtain ⟨hs, hln⟩ := hs
        rw [hs, hcta]
        exact .inl ⟨rfl, ⟨hg, idx_lane hp hat⟩, hln, ⟨pc, bs, h', hat⟩, u, h1, h2⟩
    all_goals
      rcases memRow_index hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, hk, -⟩ <;> cases hk
  all_goals exact absurd (locIn_eq h hl0).2 (by simp)

include hp hX hFw hN in
/-- Two writes of a validity byte are one index lane's: the byte names the lane. -/
theorem valid_ww {c g k g' k' : Nat} {a b : Acc} {l : Loc} (hi : X.Access (g, k) a true)
    (hj : X.Access (g', k') b true) (ha : a.Covers l) (hb : b.Covers l)
    (hl : MemRow.LocIn L c .tokenValid l) : g = g' := by
  rcases valid_cls hp hX hFw hN hi ha hl with ⟨-, ⟨-, a1, rfl⟩, h1, -⟩ | ⟨h, -⟩
  · rcases valid_cls hp hX hFw hN hj hb hl with ⟨-, ⟨-, a2, rfl⟩, h2, -⟩ | ⟨h, -⟩
    · have := a1.isLt
      have := a2.isLt
      simp only [idxLane, hp.block] at h1 h2 ⊢
      omega
    · cases h
  · cases h

include hp hX hFw hR hI hB hN in
/-- **The token-validity bytes are ordered.** -/
theorem tokenValid_ordered : RegionOrdered L X .tokenValid :=
  ring_ordered (F := fun l => mbarLoc L l.cta (.coordReady (validSlotOf L l)))
    (E := fun l => mbarLoc L l.cta (.coordFree (validSlotOf L l)))
    (prod := fun l => IdxOf L l.cta) (cons := fun l => ConsOf L X l.cta)
    (fun l _ => coordReady_handoff hp hX hFw hR hI hB hN l.cta _)
    (fun l _ => coordFree_handoff hp hX hFw hR hI hB hN l.cta _)
    (fun _ _ _ _ hi hc ⟨_, hl⟩ =>
      region_thread hp hX hFw (by simp) (by simp) (by simp) hi hc hl)
    (fun _ _ _ _ _ hi hc ⟨_, hl⟩ => (valid_cls hp hX hFw hN hi hc hl).imp
      (fun ⟨h1, h2, _, _, h3⟩ => ⟨h1, h2, h3⟩) id)
    (fun _ _ _ _ _ _ _ hi hj ha hb ⟨_, hl⟩ => valid_ww hp hX hFw hN hi hj ha hb hl)

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

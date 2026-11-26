-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Dealloc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkBlock
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.LdWait
public import Lemmas.Tcgen05.TcProgramOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Live
public import Lemmas.Tcgen05.TmemLatestSource

@[expose] public section

/-! # A Tensor Memory load is ordered with every write of its cells

A load `e` of warpgroup 0 and a write `w` of one of its cells are ordered (`ld_ordered`): the
write is before the load, or the load's `tcgen05.wait::ld` (or its pipelined pair with a later
store of its thread) is before the write. By the column class of the cell (`writer_cases`):

* an MMA `x` of the MMA lane, a QK MMA of block `d` (`mma_qkMmaBlock`) or a PV MMA of block `d`
  (`mma_pvBlock`), against a load of block `r` of the loop (`wg0_ldPlace`; the lane's polls of
  `qkDone` and arrivals on `soReady` by the block): the lane's commits to `qkDone (r % 2)`
  and polls of `soReady (r % 2)` before `x` are the uses before a block `t` (`d` for a QK MMA,
  `d + 1` for a PV MMA). For `t ≤ r` the commit of use `r / 2` comes after `x` and the load's poll
  of `qkDone` observes it: `x` is done before the load (`mma_first_obs`). For `r < t` the load's
  `wait::ld` is before the lane's arrival of use `r / 2` on `soReady (r % 2)`, which the MMA lane's
  poll before `x` observes (`soReady_after`): the wait is before `x`;
* the same for an output load of the epilogue, every MMA of which is done before the load, after
  the lane's poll of `svDone` (`done_after_svPoll`);
* a store of warpgroup 0 to the cell is of the loading thread (its lane), so before or after the
  load in the thread's program order: a store pipelined to the load, or the load pipelined to
  the store. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section
set_option maxRecDepth 4000

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The uses of a slot before a block `t ≤ r` are at most those before block `r`. -/
private theorem ru_before {r t : Nat} (h : t ≤ r) : ringUses 2 (r % 2) t ≤ r / 2 := by
  unfold ringUses; omega

/-- The uses of a slot before a block `r < t` are at least those up to block `r`. -/
private theorem ru_after {r t : Nat} (h : r < t) : r / 2 + 1 ≤ ringUses 2 (r % 2) t := by
  unfold ringUses; omega

/-- The uses of the slot of block `r` before block `r`. -/
private theorem ru_own (r : Nat) : ringUses 2 (r % 2) r = r / 2 := by
  unfold ringUses; omega

/-- The uses of the slot of block `r` up to block `r`. -/
private theorem ru_own' (r : Nat) : ringUses 2 (r % 2) (r + 1) = r / 2 + 1 := by
  unfold ringUses; omega

/-- **A store of warpgroup 0 and a load of its thread are ordered**: the store is pipelined to a
later load, a load to a later store. -/
theorem ld_st_order {h k y pc a pc' a' : Nat} {vals vals' : List Value} {sh sh' : TcShape}
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩)
    (hy : X.get (h, y) = some ⟨pc', .tc (.st a' vals' sh')⟩) :
    TcMma.WriteBefore L X (h, y) (h, k) ∨ TcMma.ReadBefore L X .ld (h, k) (h, y) := by
  have hg : h < L.threads := Frame.lt_of_get hX he
  rcases Nat.lt_trichotomy y k with hlt | heq | hgt
  · exact .inl (.inr (.inl ⟨⟨a', vals', sh', pc', hy⟩, .inr (.inl ⟨TcMma.sameWarp_self hg,
      .inl (TcMma.baseCausality_of_tc_po hy rfl hlt (len_of_get he)), ⟨a', vals', sh', pc', hy⟩,
      ⟨a, vals, sh, pc, he⟩⟩)⟩))
  · subst heq
    rw [he] at hy
    cases hy
  · exact .inr (.inr ⟨TcMma.sameWarp_self hg,
      .inl (TcMma.baseCausality_of_tc_po he rfl hgt (len_of_get hy)), ⟨a, vals, sh, pc, he⟩,
      ⟨a', vals', sh', pc', hy⟩⟩)

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **The load first**: a load of lane `h` with `r / 2` earlier arrivals on `soReady (r % 2)` has
its wait before an event of the MMA lane after its poll of that slot for use `r / 2`. -/
theorem ld_first {g i h k r pc a : Nat} {vals : List Value} {sh : TcShape}
    (hld : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : Wg0At L h pc)
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hi : i < (X.tr g).length)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr g).take i))
    (harr : arrivals (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr h).take k) =
      r / 2) :
    TcMma.WaitBefore L X .waitLd (h, k) (g, i) := by
  have hh : h < L.threads := Frame.lt_of_get hX hld
  obtain ⟨ia, pca, hga, hq, hbc⟩ := soReady_after hp hX hFw hR hI hB hh hat.1 hg hc hi hpol
  have hki : k ≤ ia := by
    rcases hq _ le_rfl k harr with h1 | h1
    · exact h1
    · omega
  have hki' : k < ia := by
    rcases Nat.lt_or_eq_of_le hki with h1 | rfl
    · exact h1
    · rw [hld] at hga
      cases hga
  obtain ⟨w, pcw, hkw, hwi, hw⟩ := wg0_ldWaitAt hp hX hFw hld hat hga (fun _ h => by cases h)
    (fun _ h => by cases h) hki'
  exact ⟨(h, w), ⟨pcw, hw⟩, rfl, hkw, .inl (hbc w hwi.le)⟩

/-- **The MMA first**: an MMA of the MMA lane with at most `r / 2` earlier commits to
`qkDone (r % 2)` is done before a load of warpgroup 0 after its poll of that slot for use
`r / 2`. -/
theorem ld_second {g i h k r pc pc' b a : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {vals : List Value} {sh : TcShape}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma b s acc mask)⟩)
    (hld : X.get (h, k) = some ⟨pc', .tc (.ld a vals sh)⟩) (hat : Wg0At L h pc')
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hcm : ((X.tr g).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) ≤ r / 2)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r))) ((X.tr h).take k)) :
    TcMma.DoneBefore L X (g, i) (h, k) := by
  obtain ⟨j, -, ws, ho, hs, hb⟩ := mma_first_obs hp hX hFw hR hI hB hx (Frame.lt_of_get hX hld)
    hat.1 (List.getElem?_eq_some_iff.mp hld).1 hg hc hcm hpol
  exact .inl ⟨(h, j), ws, ho, hs, hb⟩

/-- **A load of the loop and an MMA of the MMA lane are ordered**: the lane's commits to
`qkDone (r % 2)` and polls of `soReady (r % 2)` before the MMA are the uses before a block `t`. -/
theorem ld_mma {g i h k r t pc pc' b a : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {vals : List Value} {sh : TcShape}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma b s acc mask)⟩)
    (hld : X.get (h, k) = some ⟨pc', .tc (.ld a vals sh)⟩) (hat : Wg0At L h pc')
    (hg : g = mmaLane L X (h / L.block)) (hc : g / L.block = h / L.block)
    (hcm : ((X.tr g).take i).countP
      (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) = ringUses 2 (r % 2) t)
    (hso : okPolls (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr g).take i) =
      ringUses 2 (r % 2) t)
    (hqk : okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r))) ((X.tr h).take k) =
      ringUses 2 (r % 2) (r + 1))
    (har : arrivals (mbarLoc L (h / L.block) (.soReady (slot2 r))) ((X.tr h).take k) =
      ringUses 2 (r % 2) r) :
    TcMma.DoneBefore L X (g, i) (h, k) ∨ TcMma.WaitBefore L X .waitLd (h, k) (g, i) := by
  by_cases ht : t ≤ r
  · exact .inl (ld_second hp hX hFw hR hI hB hx hld hat hg hc (by rw [hcm]; exact ru_before ht)
      (by rw [hqk, ru_own']))
  · exact .inr (ld_first hp hX hFw hR hI hB hld hat hg hc (List.getElem?_eq_some_iff.mp hx).1
      (by rw [hso]; exact ru_after (by omega)) (by rw [har, ru_own]))

omit hR hI hB in
/-- **A load of warpgroup 0**: a `32x32b` access at a score column (`400 + 32 k`) or at a chunk
column (`64 c`). -/
theorem ld_class {h k pc a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) :
    Wg0At L h pc ∧ sh = .s32x32b ∧ a < 65536 ∧ ((400 ≤ a ∧ a ≤ 432) ∨ a ≤ 192) := by
  have hg := Frame.lt_of_get hX he
  have hT := tmem_rows hp hX hFw
  rcases tc_role hT hg he rfl with ⟨hat, hrow⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc'⟩
  · refine ⟨hat, ?_⟩
    rcases hrow with h1 | h1 | h1 | h1 | ⟨k0, vs, h1⟩ | ⟨c0, vs, h1⟩ | ⟨c0, vs, h1⟩ |
      ⟨-, _, _, h1⟩ <;> try (cases h1; done)
    · simp only [Kind.tc.injEq, TcKind.ld.injEq] at h1
      obtain ⟨rfl, -, rfl⟩ := h1
      have := k0.isLt
      exact ⟨rfl, by omega, .inl ⟨by omega, by omega⟩⟩
    · simp only [Kind.tc.injEq, TcKind.ld.injEq] at h1
      obtain ⟨rfl, -, rfl⟩ := h1
      have := c0.isLt
      exact ⟨rfl, by omega, .inr (by omega)⟩
  · exfalso
    rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, -, -, h, -⟩ |
      ⟨_, _, _, -, -, h, -⟩ <;> cases h
  · cases hc'

/-- **A load of warpgroup 0 is ordered with every write of its cells.** -/
theorem ld_ordered (hN : DequantInputs L X) {e : EvId} {a : Nat}
    {vals : List Value} {sh : TcShape} {j : Nat} {cell : TcMma.Cell}
    (hld : X.TLd e a vals sh) (hj : j < vals.length) (hc : cell = tcDataCell L e.1 sh a j)
    {w : EvId} (hw : TcMma.TmemWrite L X w cell) :
    TcMma.WriteBefore L X w e ∨ TcMma.ReadBefore L X .ld e w := by
  obtain ⟨h, k⟩ := e
  obtain ⟨gw, iw⟩ := w
  obtain ⟨pc, he⟩ := hld
  have hg := Frame.lt_of_get hX he
  have hT := tmem_rows hp hX hFw
  have hlen := ldLen hp hX he rfl
  obtain ⟨hat, hsh, ha, hcls⟩ := ld_class hp hX hFw he
  subst hsh
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha (j := j)
  rw [← hc] at hcta hlane hcol
  obtain ⟨hcw, cw⟩ := writer_cases hp hX hT hw
  have hplace := wg0_ldPlace hp hX hFw he hat
  have hMma : ∀ (x : EvId) (pc' b : Nat) (s : TcMma.OperandSpec) (acc : Bool)
      (mask : List Nat) (t : Nat), X.get x = some ⟨pc', .tc (.mma b s acc mask)⟩ →
      MmaOn L x.1 pc' → x.1 / L.block = h / L.block →
      (∀ j : Fin 2, okPolls (mbarLoc L (x.1 / L.block) (.soReady j)) ((X.tr x.1).take x.2) =
          ringUses 2 j t ∧ ((X.tr x.1).take x.2).countP
          (PTX.Flow.commitsTo (mbarLoc L (x.1 / L.block) (.qkDone j))) = ringUses 2 j t) →
      TcMma.WriteBefore L X x (h, k) ∨ TcMma.ReadBefore L X .ld (h, k) x := by
    intro x pc' b s acc mask t hx hon hxc hcnt
    obtain ⟨g, i⟩ := x
    dsimp only at hxc hcnt
    rw [hxc] at hcnt
    rcases hplace with ⟨r, -, -, hr⟩ | ⟨-, jw, p, hjw, hpoll⟩
    · have hgl : g = mmaLane L X (h / L.block) := by
        rw [← hxc]
        exact laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
      obtain ⟨hq, har⟩ := hr (slot2 r)
      obtain ⟨hs1, hs2⟩ := hcnt (slot2 r)
      rcases ld_mma hp hX hFw hR hI hB hx he hat hgl hxc hs2 hs1 hq har with hd | hw'
      · exact .inl (.inl (.inl hd))
      · exact .inr (.inl hw')
    · exact .inl (.inl (.inl (done_after_svPoll hp hX hFw hR hI hB hN hx (.inl ⟨b, s, acc, mask,
        rfl⟩) hxc.symm hat.1 hpoll hjw (List.getElem?_eq_some_iff.mp he).1)))
  rcases cw with ⟨k', ⟨pc', s', hk', hgx, hon, hops⟩, h1, h2⟩ |
    ⟨b, ⟨pc', s', a', hgx, hon, hops⟩, hb, hb', h1, h2⟩ | ⟨k', ⟨-, -, hk', -⟩, h1, h2⟩ |
    ⟨⟨pc', a', vals', hgy, -⟩, h1, hl⟩
  · obtain ⟨d, hd⟩ := mma_qkMmaBlock hp hX hFw hgx hon.1
    exact hMma (gw, iw) pc' 400 s' _ _ d hgx hon (hcw.symm.trans hcta) hd
  · obtain ⟨d, hd⟩ := mma_pvBlock hp hX hFw hgx hon.1 (by omega)
    exact hMma (gw, iw) pc' b s' a' _ (d + 1) hgx hon (hcw.symm.trans hcta) hd
  · omega
  · have hb := hp.block
    have hcw' := hcw.symm.trans hcta
    simp only at hl hcw'
    rw [hb] at hcw'
    obtain rfl : gw = h := by omega
    exact ld_st_order hX he hgy

omit hR hI hB in
open Tmem.Pair Tmem.One Tmem.Access in
/-- **The source of a load is live**: the load is waited for before every release of an
allocation covering its cell, every release being a deallocation of the load's CTA. -/
theorem ld_live (hBr : BarRows P L X) (ht : Tmem1Facts L X 0) {source e : EvId}
    {cell : TcMma.Cell} {a : Nat} {vals : List Value} {sh : TcShape} (hld : X.TLd e a vals sh)
    (hc : cell.cta = e.1 / L.block) : TcMma.SourceLive L X source e cell := by
  intro cta r hr hcov rel hrel
  refine .inl ?_
  obtain ⟨⟨pc, grp, a', n, hd⟩, hdc⟩ := release_info hX ht.toTmem1Ops hr hrel
  have hown := covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX ht.toTmem1Ops hr
  have hcell : rel.1 / L.block = e.1 / L.block := by rw [hdc, ← hlc, ← hown, hc]
  obtain ⟨pce, hge⟩ := hld
  refine ⟨fun _ => ?_, fun ⟨a', vals', sh', pc', h⟩ => ?_, fun hasync => ?_⟩
  · exact (dealloc_ldst hp hX hFw hBr hd hcell).1 ⟨pce, hge⟩
  · rw [hge] at h
    cases h
  · rcases hasync with ⟨d', s', acc', mask', pc', h⟩ | ⟨c', pc', h⟩ | ⟨s', pc', h⟩ <;>
      rw [hge] at h <;> cases h

/-- **A load of warpgroup 0 with a write before it has a source**: the latest write ordered before
it (`readSourceOfCandidate`), given the order of its cell's writes with the load (`ld_ordered`), its
liveness (`ld_live`) and the order of the writes (`writes_safe`). -/
theorem ld_source (hN : DequantInputs L X) (hBr : BarRows P L X)
    (hPS : PvStoreOrder L X) (hG : SyncGuarded L kernel X)
    (ht : Tmem.One.Tmem1Facts L X 0) {e : EvId}
    {j : Nat} {cell : TcMma.Cell} (hc : TcMma.LoadCell L X e j cell)
    (hcand : ∃ w, TcMma.TmemWrite L X w cell ∧ TcMma.WriteBefore L X w e) :
    ∃ source, TcMma.ReadSource L X .ld source e cell := by
  obtain ⟨a, vals, sh, hld, hj, hcell⟩ := hc
  obtain ⟨w0, hw0, hb0⟩ := hcand
  have hT := tmem_rows hp hX hFw
  have hcta : cell.cta = e.1 / L.block := by
    rw [hcell]
    rfl
  exact TcMma.readSourceOfCandidate hX hG (writes_safe hp hX hFw hT (mmaOne hp hX hFw) hPS)
    (fun w hw => ld_ordered hp hX hFw hR hI hB hN hld hj hcell hw)
    (fun _ _ _ => ld_live hp hX hFw hBr ht hld hcta) hw0 hb0

end

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

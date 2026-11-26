-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Handoff
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Use
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Store
import Lemmas.Protocol.UnitGate
import Lemmas.Tensor.BoxNone
import Lemmas.Tensor.BoxNoneInj

@[expose] public section

/-! # The raw tiles are ordered

The bytes of `raw b` (`131072 + 36864 b`, slot `b < 2` of the raw ring) are written by the TMA
lane's gathers (asynchronous tensor loads, gather `q` of use `u` of the tile covering 2304 bytes)
and read by the dequant lanes (`Protocol/Shared/RawCls.lean`). `ring_async_ordered` orders them
(`raw_ordered`):

* write before read: a dequant lane's poll of `rawReady b` of use `u` observes the completion of
  every gather of use `u` (`rawReady_observes`: the gather's own notification, found by its count
  `16 u + q`), so the gather is finished at the poll (`raw_finished`);
* read before the next write: the lane's proxy fence before its arrival on `rawFree b`
  (`dequant_freeFence`) is after the read, and the TMA lane's poll of `rawFree b` before the
  next gather's issue observes the arrival (`rawFree_handoff`);
* two gathers of one use at a byte are one (`raw_ww`: the byte names gather `q`, and the count
  `16 u + q` names the load).

The stores of warpgroup 0 never read a raw byte (`raw_wr`). -/

/-! # The accesses of a raw tile

A byte of `raw b` of CTA `c` is accessed by two kinds of events only:

* a thread's read (`raw_rd`): a dequant lane's raw read, after `v + 1` successful polls of
  `rawReady b` and `v` arrivals on `rawFree b` (`dequant_rdUse`);
* an asynchronous write (`raw_wr`): a gather of the CTA's TMA lane, gather `q` of use `u` of the
  tile (`tma_gatherUse`), whose box covers the byte, after `16 u + q` loads on `rawReady b` and
  `u + 1` successful polls of `rawFree b`. A warpgroup-0 tensor store never reads a raw byte: its
  warp is below 2 (`wg0_outIssue`), so its source lies below `raw 0`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)

include hp hX hFw in
/-- **The thread accesses of a raw tile**: a dequant lane's read with its counts. -/
theorem raw_rd {b : Fin 2} {c g k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access (g, k) a w) (hc : a.Covers l) (hl : MemRow.LocIn L c (.raw b) l) :
    w = false ∧ RawDeq L c g ∧ ∃ v, okPolls (mbarLoc L c (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
      arrivals (mbarLoc L c (.rawFree b)) ((X.tr g).take k) = v := by
  obtain ⟨e, he, hr⟩ := access_region hp hX hFw hi hc hl.1
  have hg := Frame.lt_of_get hX he
  obtain ⟨ev, hev, -, hm⟩ := access_event hi
  rw [he] at hev
  cases hev
  have hout : ∀ {r : Region} {c' : Nat}, MemRow.LocIn L c' r l → r ≠ .raw b → False :=
    fun h hne => hne (locIn_eq h hl).2
  rcases hr with ⟨-, h⟩ | ⟨-, (h | h | h) | h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨hat, r, h | h⟩
  rotate_right 1
  · exact (hout h (by simp)).elim
  iterate 8 (exact (hout h (by simp)).elim)
  · have hcta : g / L.block = c := (locIn_eq h hl).1
    have hdl : RawDeq L c g := ⟨hg, hcta ▸ deq_lane hp hat⟩
    rcases hi with ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨bs, ⟨pc, h'⟩, rfl⟩ | ⟨o, n, pc, h'⟩ <;>
      rw [h'] at he <;> cases he
    · obtain ⟨b', hb', v, h1, h2⟩ := dequant_rdUse hp hX hFw h' hat
      obtain ⟨-, hbb⟩ := locIn_eq (hb'.locIn hc) hl
      obtain rfl : b' = b := by simpa using hbb
      rw [hcta] at h1 h2
      exact ⟨rfl, hdl, v, h1, h2⟩
    · rcases memRow_dequant hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, _, hk, -⟩ |
        ⟨a', bs', b', q, s, hk, hws⟩
      · cases hk
      · cases hk
      · cases hk
        have hlt := MemRow.dqChunk_lt (i := g % 128) (Nat.mod_lt _ (by decide)) q.isLt s.isLt
        have hin := MemRow.wsAcc_in hws (Nat.le_add_right _ _)
          (by simp only [Region.size]; omega)
        exact (hout (hin.locIn hc) (by simp)).elim
    · rcases memRow_dequant hp hX hFw hg h' hat hm with ⟨_, _, hk⟩ | ⟨_, _, _, hk, -⟩ |
        ⟨a', bs', b', q, s, hk, hws⟩ <;> cases hk

include hp hX hFw in
/-- **The asynchronous accesses of a raw tile**: a gather of the CTA's TMA lane, writing its
box's bytes (gather `q` of use `u`, `tma_gatherUse`); a tensor store never reads the tile. -/
theorem raw_wr (hO : TmaOne L X) (hnu : NoUbInner L X) {b : Fin 2} {c g k : Nat}
    {p : AsyncCopy.Part}
    {a : Acc} {w : Bool} {l : Loc} (hi : X.Intent (.async (g, k) p) a w) (hc : a.Covers l)
    (hl : MemRow.LocIn L c (.raw b) l) :
    w = true ∧ RawTma L X c g ∧ k < (X.tr g).length ∧
      ∃ x y j s al pc, p = .write (.load x y j) ∧ X.get (g, k) = some ⟨pc, .tensorIssue al s⟩ ∧
        s.mbar = mbarLoc L c (.rawReady b) ∧ s.descriptor.swizzle = .none ∧
        TensorCopy.writeLoc s x y j = some l ∧ ∃ q < 16, ∃ u,
        L.sharedBase + (131072 + 36864 * b.val + 2304 * q) ≤ l.addr ∧
        l.addr < L.sharedBase + (131072 + 36864 * b.val + 2304 * q) + 2304 ∧
        ((X.tr g).take k).countP (issuesTo (mbarLoc L c (.rawReady b))) = 16 * u + q ∧
        okPolls (mbarLoc L c (.rawFree b)) ((X.tr g).take k) = u + 1 := by
  have hw : w = p.writes := hi.1
  rcases async_region hp hX hFw hi hc hl.1 with ⟨r, hr⟩ | hr | ⟨r, hr, x, y, j, e, addr, he, hcase⟩
  · exact absurd (locIn_eq hr hl).2 (by simp)
  · exact absurd (locIn_eq hr.1 hl).2 (by simp)
  obtain ⟨hcta, hrb⟩ := locIn_eq hr hl
  obtain rfl : b = r := by simpa using hrb.symm
  have hg := Frame.lt_of_get hX he
  obtain ⟨pc, kd⟩ := e
  rcases hcase with ⟨s, hpp, hk, hat, hlw⟩ | ⟨s, hk, hat, hlr⟩
  · simp only at hk
    subst hk
    obtain ⟨hpc, b', q, hq, u, hmb, hsb, hsw, hsz, hcnt, hpoll⟩ :=
      tma_gatherUse hp hX hFw he hat rfl
    obtain ⟨-, -, h3, h4⟩ := TensorCopy.writeLoc_none hsw hlw
    rw [hsz, hsb] at h4
    rw [hsb] at h3
    obtain ⟨-, -, hl3, hl4⟩ := hl
    simp only [Region.lo, Region.size] at hl3 hl4
    simp only at h3 h4
    have hb' : b' = b := Fin.ext (by have := b.isLt; have := b'.isLt; omega)
    subst hb'
    have hon : TmaOn L g pc := ⟨hat, hpc⟩
    have hn : ∀ f, (Kind.tensorIssue addr s) ≠ .ub f := fun _ h => by cases h
    have hex : ∃ y k e, X.get (y, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L y e.pc ∧
        y / L.block = g / L.block := ⟨g, k, _, he, hn, hon, rfl⟩
    have hT : g = tmaThread L X (g / L.block) := by
      unfold tmaThread
      rw [ite_eq_left_of_eq_true _ _ (eq_true hex)]
      exact laneOn_eq hO he hn hon
    rw [← hcta]
    refine ⟨by rw [hw, hpp]; rfl, ⟨hg, hT⟩, (List.getElem?_eq_some_iff.mp he).1,
      x, y, j, s, addr, pc, hpp, he, ?_, hsw, hlw, q, hq, u, by omega, by omega, ?_, hpoll⟩
    · rw [hmb, hcta]
    · simpa [hcta] using hcnt
  · exfalso
    simp only at hk
    subst hk
    obtain ⟨hw2, -⟩ := wg0_outIssue hp hX hFw hnu ⟨pc, he⟩
    obtain ⟨c', hc4, -, -, -, h3, h4⟩ := wg0_store_read hp hX hFw he hat rfl hlr
    have ho : MemRow.wg0OutOff c' ≤ 40960 := by
      rcases (by omega : c' = 0 ∨ c' = 1 ∨ c' = 2 ∨ c' = 3) with rfl | rfl | rfl | rfl <;> decide
    obtain ⟨-, -, hl3, -⟩ := hl
    simp only [Region.lo] at hl3
    omega

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)

include hp hX hFw in
/-- A thread access of a raw byte: a dequant lane's read with its counts. -/
private theorem rd_cls {b : Fin 2} {g k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access (g, k) a w) (hc : a.Covers l) (hl : ∃ c, MemRow.LocIn L c (.raw b) l) :
    w = false ∧ RawDeq L l.cta g ∧ ∃ v, okPolls (mbarLoc L l.cta (.rawReady b)) ((X.tr g).take k) =
      v + 1 ∧ arrivals (mbarLoc L l.cta (.rawFree b)) ((X.tr g).take k) = v := by
  obtain ⟨c, hl⟩ := hl
  obtain rfl : l.cta = c := hl.2.1
  exact raw_rd hp hX hFw hi hc hl

include hp hX hFw hR hI hB hN in
/-- The completion of a gather is observed by a poll of its use: the gather is finished there. -/
theorem raw_finished {b : Fin 2} {c g k pc al h j pc' par : Nat} {s : TensorCopy.Spec}
    {x y j' q u : Nat} {acq : Bool} {sc : MbarScope} (hq : q < 16) (hT : RawTma L X c g)
    (hh : RawDeq L c h) (he : X.get (g, k) = some ⟨pc, .tensorIssue al s⟩)
    (hmb : s.mbar = mbarLoc L c (.rawReady b))
    (hcnt : ((X.tr g).take k).countP (issuesTo (mbarLoc L c (.rawReady b))) = 16 * u + q)
    (hw : X.get (h, j) = some ⟨pc', .wait (mbarLoc L c (.rawReady b)) par true acq sc⟩)
    (hu : okPolls (mbarLoc L c (.rawReady b)) ((X.tr h).take j) = u) :
    AsyncFinished L X (g, k) (.write (.load x y j')) (h, j) := by
  obtain ⟨hacq, rfl⟩ := mbarWait_cta hX hR hw
  subst hacq
  obtain ⟨-, -, hall⟩ := rawReady_observes hp hX hFw hR hI hB hN hw
  obtain ⟨i, pc2, al2, sp2, hget2, hm2, -, hc2, hobs⟩ := hall ⟨q, hq⟩
  obtain ⟨hgl, hgT⟩ := hT
  subst hgT
  have hik : i = k := nthEv_unique (p := issuesTo (mbarLoc L c (.rawReady b))) hget2
    (by rw [issuesTo_tensorIssue]; simpa using hm2) he
    (by rw [issuesTo_tensorIssue]; simpa using hmb)
    (by rw [hc2, hcnt, hu])
  subst hik
  rw [he] at hget2
  obtain ⟨-, hsp⟩ := Event.mk.inj (Option.some.inj hget2)
  obtain ⟨-, rfl⟩ := Kind.tensorIssue.inj hsp
  obtain ⟨i1, j1, r, w1, ph, hr1, hid1, -⟩ := hobs.2
  have hrec : r ∈ X.objects (mbarLoc L c (.rawReady b)) := List.mem_of_getElem? hr1
  have hpres := object_record_present hX.tma hrec
  rw [hid1] at hpres
  obtain ⟨o, ho, hn⟩ := hpres
  obtain ⟨⟨a', pc3, hget3⟩, -, -⟩ := hX.tensor _ o ho
  have hg3 := hget3
  rw [he] at hg3
  obtain ⟨-, hsp3⟩ := Event.mk.inj (Option.some.inj hg3)
  obtain ⟨-, hs3⟩ := Kind.tensorIssue.inj hsp3
  refine .inr ⟨.cta, ⟨.async _ (.notify .load), mbarLoc L c (.rawReady b),
    ⟨rfl, o, a', ho, ⟨pc3, ?_⟩, ?_, hn⟩, hobs.1, hobs.2⟩, ?_⟩
  · exact hget3
  · rw [← hs3]
    exact hmb
  · exact Unit.Gate.scopesMeet (rawTma_sameCta hp ⟨hgl, rfl⟩ hh) _ _

include hp hX hFw hR hI hB hN in
/-- An asynchronous access of a raw byte: a gather of the TMA lane, finished at every poll of
its use. -/
private theorem wr_cls (hnu : NoUbInner L X) {b : Fin 2} {g k : Nat} {p : Part} {a : Acc} {w : Bool}
    {l : Loc} (hi : X.Intent (.async (g, k) p) a w) (hc : a.Covers l)
    (hl : ∃ c, MemRow.LocIn L c (.raw b) l) :
    w = true ∧ (∃ t, p = .write t) ∧ RawTma L X l.cta g ∧ k < (X.tr g).length ∧
      ∃ u, okPolls (mbarLoc L l.cta (.rawFree b)) ((X.tr g).take k) = u + 1 ∧
        ∀ h j pc par acq sc, RawDeq L l.cta h →
          X.get (h, j) = some ⟨pc, .wait (mbarLoc L l.cta (.rawReady b)) par true acq sc⟩ →
          okPolls (mbarLoc L l.cta (.rawReady b)) ((X.tr h).take j) = u →
          AsyncFinished L X (g, k) p (h, j) := by
  obtain ⟨c, hl⟩ := hl
  obtain rfl : l.cta = c := hl.2.1
  obtain ⟨hw, hT, hlen, x, y, j, s, al, pc, rfl, he, hmb, -, -, q, hq, u, -, -, hcnt, hpoll⟩ :=
    raw_wr hp hX hFw hN.tmaOne hnu hi hc hl
  exact ⟨hw, ⟨_, rfl⟩, hT, hlen, u, hpoll, fun h j' pc' par acq sc hh hw' hu =>
    raw_finished hp hX hFw hR hI hB hN hq hT hh he hmb hcnt hw' hu⟩

include hp hX hFw hN in
/-- Two gathers of one use covering a byte are one gather and one slot. -/
private theorem raw_ww (hnu : NoUbInner L X) {b : Fin 2} {g k g' k' : Nat} {p p' : Part}
    {a a' : Acc}
    {l : Loc} (hi : X.Intent (.async (g, k) p) a true) (hi' : X.Intent (.async (g', k') p') a' true)
    (hc : a.Covers l) (hc' : a'.Covers l) (hl : ∃ c, MemRow.LocIn L c (.raw b) l)
    (hpo : okPolls (mbarLoc L l.cta (.rawFree b)) ((X.tr g).take k) =
      okPolls (mbarLoc L l.cta (.rawFree b)) ((X.tr g').take k')) :
    g = g' ∧ k = k' ∧ p = p' := by
  obtain ⟨c, hl⟩ := hl
  obtain rfl : l.cta = c := hl.2.1
  obtain ⟨-, hT, -, x, y, j, s, al, pc, rfl, he, hmb, hsw, hlw, q, hq, u, h1, h2, hcnt, hpoll⟩ :=
    raw_wr hp hX hFw hN.tmaOne hnu hi hc hl
  obtain ⟨-, hT', -, x', y', j', s', al', pc', rfl, he', hmb', -, hlw', q', hq', u', h1', h2',
    hcnt', hpoll'⟩ := raw_wr hp hX hFw hN.tmaOne hnu hi' hc' hl
  obtain rfl : g = g' := hT.2.trans hT'.2.symm
  obtain rfl : u = u' := by omega
  obtain rfl : q = q' := by omega
  have hk : k = k' := nthEv_unique (p := issuesTo (mbarLoc L l.cta (.rawReady b))) he
    (by rw [issuesTo_tensorIssue]; simpa using hmb) he'
    (by rw [issuesTo_tensorIssue]; simpa using hmb') (hcnt.trans hcnt'.symm)
  subst hk
  rw [he] at he'
  obtain ⟨-, hsp⟩ := Event.mk.inj (Option.some.inj he')
  obtain ⟨-, rfl⟩ := Kind.tensorIssue.inj hsp
  obtain ⟨rfl, rfl, rfl⟩ := TensorCopy.writeLoc_none_inj hsw hlw hlw'
  exact ⟨rfl, rfl, rfl⟩

include hX hR hN in
/-- A dequant lane's arrival on `rawFree b` follows more polls of `rawReady b` than arrivals. -/
private theorem arr_cls {b : Fin 2} {h ia pc tx cnt : Nat} {sc : MbarScope} {l : Loc}
    (hh : RawDeq L l.cta h)
    (he : X.get (h, ia) = some ⟨pc, .arrive (mbarLoc L l.cta (.rawFree b)) tx cnt true sc⟩) :
    arrivals (mbarLoc L l.cta (.rawFree b)) ((X.tr h).take ia) <
      okPolls (mbarLoc L l.cta (.rawReady b)) ((X.tr h).take ia) := by
  obtain ⟨-, y, rfl⟩ := hh
  rcases rawFree_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ | ⟨-, -, -, ⟨_, hk⟩⟩ |
    ⟨-, -, hk⟩
  · cases hk
  · cases hk
  · simp only [MbarRow.Arrive, Kind.arrive.injEq] at hk
    obtain ⟨-, rfl, rfl, -, rfl⟩ := hk
    exact hN.deqArr he

include hp hX hFw in
/-- A dequant lane's read before its arrival on `rawFree b` is before its proxy fence. -/
private theorem fence_cls {b : Fin 2} {h j ia pc tx cnt : Nat} {a : Acc} {sc : MbarScope}
    {l : Loc} (hh : RawDeq L l.cta h) (hacc : X.Access (h, j) a false) (hj : j ≤ ia)
    (he : X.get (h, ia) = some ⟨pc, .arrive (mbarLoc L l.cta (.rawFree b)) tx cnt true sc⟩) :
    ∃ jf, j < jf ∧ jf < ia ∧ X.IsProxyFence (h, jf) (.async (some (.shared .cta))) none := by
  have hw : 8 ≤ warp L h ∧ warp L h < 12 := by
    obtain ⟨-, y, rfl⟩ := hh
    have := y.isLt
    simp only [warp, tidOf_x_eq hp, deqLane, hp.block]
    omega
  obtain ⟨jf, rfl, hfe, pc', l', tx', cnt', rel', sc', hjf⟩ :=
    dequant_freeFence hp hX hFw hw he
  rcases Nat.lt_or_ge j jf with hlt | hge
  · exact ⟨jf, hlt, by omega, hfe⟩
  exfalso
  obtain ⟨ev, hev, hk, -⟩ := access_event hacc
  have hj3 : j = jf ∨ j = jf + 1 ∨ j = jf + 2 := by omega
  rcases hj3 with rfl | rfl | rfl
  · obtain ⟨pcf, hf⟩ := hfe
    rw [hf] at hev
    cases hev
    rcases hk with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, _, hk⟩ <;> cases hk
  · rw [hjf] at hev
    cases hev
    rcases hk with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, _, hk⟩ <;> cases hk
  · rw [he] at hev
    cases hev
    rcases hk with ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, _, hk⟩ <;> cases hk

include hp hX hFw hR hI hB hN in
/-- **The raw tiles' ring facts**: the producers are the TMA lane's gathers, the consumers the
dequant lanes (`AsyncRing`). -/
theorem raw_ring (hnu : NoUbInner L X) (b : Fin 2) :
    AsyncRing L X (fun l => ∃ c, MemRow.LocIn L c (.raw b) l)
      (fun l => mbarLoc L l.cta (.rawReady b)) (fun l => mbarLoc L l.cta (.rawFree b))
      (fun l => RawTma L X l.cta) (fun l => RawDeq L l.cta) where
  hE := fun l ⟨c, hl⟩ => by
    obtain rfl : l.cta = c := hl.2.1
    exact rawFree_handoff hp hX hFw hR hI hB hN _ b
  hcta := fun l g ⟨c, hl⟩ h => by
    obtain rfl : l.cta = c := hl.2.1
    rcases h with h | h
    · exact ⟨h.1, hl.1, (rawTma_cta hp h).symm⟩
    · exact ⟨h.1, hl.1, (rawDeq_cta hp h).symm⟩
  hcons := fun l g ⟨c, hl⟩ h => by
    obtain rfl : l.cta = c := hl.2.1
    exact rawTma_deq hp h
  hrd := fun _ _ _ _ _ hi hc hl => rd_cls hp hX hFw hi hc hl
  hwr := fun _ _ _ _ _ _ hi hc hl => wr_cls hp hX hFw hR hI hB hN hnu hi hc hl
  hww := fun _ _ _ _ _ _ _ _ _ hi hi' hc hc' hl hpo => raw_ww hp hX hFw hN hnu hi hi' hc hc' hl hpo
  harr := fun l _ _ _ _ _ _ hl hh he => arr_cls hX hR hN hh he
  hfence := fun l _ _ _ _ _ _ _ _ hl hh hacc hj he => fence_cls hp hX hFw hh hacc hj he

include hp hX hFw hR hI hB hN in
/-- **The raw tiles are ordered.** -/
theorem raw_ordered (hnu : ¬ HasUb X) (b : Fin 2) : RegionOrdered L X (.raw b) :=
  ring_async_ordered (raw_ring hp hX hFw hR hI hB hN hnu b)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

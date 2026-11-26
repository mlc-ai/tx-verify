-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Lemmas.Protocol.UnitHandoff
import Lemmas.Protocol.UnitGate
import Lemmas.Protocol.NoIncRingOrder
import Lemmas.Order.WaitOrderEnables
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region

@[expose] public section

/-! # A ring region of thread accesses is ordered

The shared tool of the ring regions (`tmaCoord`, `tokenValid`): a byte `l` of the region is
written by the producers `prod l` and read by the consumers `cons l` of one slot of a ring, whose
full barrier `F l` the producers arrive on once per use and the consumers poll once per use, and
whose empty barrier `E l` the consumers arrive on once per use and the producers poll once per
use, one poll ahead. A producer's write of use `u` follows `u` arrivals on `F l` and `u + 1`
successful polls of `E l`; a consumer's read of use `u` follows `u + 1` successful polls of `F l`
and `u` arrivals on `E l` (the per-use index of the access, from the roles' `Use` exports). Then
(`ring_ordered`):

* a write of use `u` is before a read of use `v ≥ u`: the read follows the consumer's poll of
  `F l` with `u` earlier ones, which observes the producer's arrival of use `u`
  (`UnitHandoff` with offset 0);
* a read of use `v` is before a write of use `u > v`: the write follows the producer's poll of
  `E l` with `v + 1` earlier ones, which observes the consumer's arrival of use `v` (offset 1);
* two writes of a byte are one thread's (`hww`), in program order (`same_thread`).

The library's `ConflictsOrdered.of_ring` (one global use number, one write per byte and use) does
not fit a region whose writes of one use are several events of one lane; this form takes the
counts directly. The handoffs come from a channel's observation lemma (`handoff_of_observes`):
its arrivals are releases and its polls acquires of CTA scope (`mbarWait_cta`).

`ring_async_ordered` is the form for a slot written by asynchronous operations (the raw tiles'
gathers) and read by threads. A write of use `u` (its issue follows `u + 1` successful polls of
`E l`) is finished for every consumer's poll of `F l` with `u` earlier ones (the channel's
observation of its completion). Then:

* a write of use `u` is before a read of use `v ≥ u`: the read follows the consumer's poll of use
  `u`, at which the write is finished (`AsyncFinished`, then program order);
* a read of use `v` is before a write of use `u > v`: the consumer's proxy fence between the read
  and its arrival of use `v` on `E l` (`ProxyBefore`), whose arrival the producer's poll before
  the issue observes;
* two writes of uses `u < u'` are ordered by a consumer's poll of use `u` (at which the first is
  finished) before its arrival of use `u` on `E l`, observed before the second issue
  (`AsyncChain`); two writes of one use at a byte are one write (`hww`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A poll of an mbarrier is an acquire of CTA scope.** -/
theorem mbarWait_cta (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {w : EvId} {pc p : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get w = some ⟨pc, .wait l p ok acq sc⟩) : acq = true ∧ sc = .cta := by
  rcases mbar_kind hX hR he rfl with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, hc, -⟩ |
    ⟨_, _, _, hc, -⟩
  · cases hc
  · cases hc
  · cases hc
    exact ⟨rfl, rfl⟩
  · cases hc
  · cases hc

/-- **A unit handoff from an observation lemma**: if a consumer's successful poll of `mb` with
`q + δ` earlier ones observes every producer's release arrival with `q` earlier ones, and the
producers and consumers are threads of one CTA, the arrivals and polls synchronize. -/
theorem handoff_of_observes (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {mb : Loc} {prod cons : Nat → Prop} {δ : Nat}
    (hcta : ∀ g h, prod g → cons h → SameCta L g h)
    (hobs : ∀ {h j pc p acq sc q}, cons h → X.get (h, j) = some ⟨pc, .wait mb p true acq sc⟩ →
      okPolls mb ((X.tr h).take j) = q + δ → ∀ g, prod g →
      ∃ i pc' sc', X.get (g, i) = some ⟨pc', .arrive mb 0 1 true sc'⟩ ∧
        arrivals mb ((X.tr g).take i) = q ∧
        AsyncCopy.WaitObserves X (.thread (g, i)) (h, j) mb acq sc) :
    UnitHandoff L X mb prod cons δ := by
  intro h j pc p acq sc q hh hw hq g hg
  obtain ⟨i, pc', sc', ha, hi, hob⟩ := hobs hh hw hq g hg
  obtain ⟨rfl, -⟩ := mbarWait_cta hX hR hw
  exact ⟨i, hi, sc', ⟨0, 1, pc', ha⟩, sc, hob, Unit.Gate.scopesMeet (hcta g h hg hh) _ _⟩

/-- **A write and a read of one ring slot are ordered** by their uses. -/
theorem ring_pair {F E : Loc} {prod cons : Nat → Prop}
    (hF : UnitHandoff L X F prod cons 0) (hE : UnitHandoff L X E cons prod 1)
    {g k h j u v : Nat} (hg : prod g) (hh : cons h)
    (hu1 : arrivals F ((X.tr g).take k) = u) (hu2 : okPolls E ((X.tr g).take k) = u + 1)
    (hv1 : okPolls F ((X.tr h).take j) = v + 1) (hv2 : arrivals E ((X.tr h).take j) = v)
    (hk : k < (X.tr g).length) (hj : j < (X.tr h).length) :
    baseCausality L X (g, k) (h, j) ∨ baseCausality L X (h, j) (g, k) := by
  by_cases huv : u ≤ v
  · exact .inl (hF.baseCausality_of_counts (q := u) hh hg hu1.le (by omega) hj)
  · exact .inr (hE.baseCausality_of_counts (q := v) hg hh hv2.le (by omega) hk)

/-- **Only threads access a region no asynchronous operation reaches** (`async_region`: the
dequantized tiles, the P exchange and the raw tiles). -/
theorem region_thread (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {r : Region} (hd : ∀ b, r ≠ .dequant b) (hx : r ≠ .pExchange)
    (hw : ∀ b, r ≠ .raw b) {c : Nat} {e} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Intent e a w) (hc : a.Covers l) (hl : MemRow.LocIn L c r l) :
    ∃ i, e = .thread i := by
  cases e with
  | thread i => exact ⟨i, rfl⟩
  | async i p =>
    exfalso
    obtain ⟨g, k⟩ := i
    rcases async_region hp hX hFw hi hc hl.1 with ⟨b, h⟩ | h | ⟨b, h, -⟩
    · exact hd b (locIn_eq h hl).2.symm
    · exact hx (locIn_eq h.1 hl).2.symm
    · exact hw b (locIn_eq h hl).2.symm

/-- **A ring region of thread accesses is ordered**: every access of a byte `l` of `R` is a
thread's; a write is a producer's of the byte's slot with its write counts, a read a consumer's
with its read counts; two writes of a byte are one thread's. -/
theorem ring_ordered {R : Loc → Prop} {F E : Loc → Loc} {prod cons : Loc → Nat → Prop}
    (hF : ∀ l, R l → UnitHandoff L X (F l) (prod l) (cons l) 0)
    (hE : ∀ l, R l → UnitHandoff L X (E l) (cons l) (prod l) 1)
    (hcov : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l → ∃ i, ref = .thread i)
    (hcls : ∀ g k a w l, X.Access (g, k) a w → a.Covers l → R l →
      (w = true ∧ prod l g ∧ ∃ u, arrivals (F l) ((X.tr g).take k) = u ∧
        okPolls (E l) ((X.tr g).take k) = u + 1) ∨
      (w = false ∧ cons l g ∧ ∃ u, okPolls (F l) ((X.tr g).take k) = u + 1 ∧
        arrivals (E l) ((X.tr g).take k) = u))
    (hww : ∀ g k g' k' a b l, X.Access (g, k) a true → X.Access (g', k') b true →
      a.Covers l → b.Covers l → R l → g = g') :
    ByteOrdered L X R := by
  intro e f a b l hcon ha hb hl _
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := hcon
  obtain ⟨⟨g, k⟩, rfl⟩ := hcov e a we l he ha hl
  obtain ⟨⟨h, j⟩, rfl⟩ := hcov f b wf l hf hb hl
  have he' : X.Access (g, k) a we := he
  have hf' : X.Access (h, j) b wf := hf
  have lift : ∀ {x y : EvId}, baseCausality L X x y →
      ByteCausality L X l (.thread x) (.thread y) := fun h => .direct (.of_base L h)
  rcases hcls g k a we l he' ha hl with ⟨rfl, hpg, u, hu1, hu2⟩ | ⟨rfl, hcg, u, hu1, hu2⟩ <;>
    rcases hcls h j b wf l hf' hb hl with ⟨rfl, hph, v, hv1, hv2⟩ | ⟨rfl, hch, v, hv1, hv2⟩
  · obtain rfl := hww g k h j a b l he' hf' ha hb hl
    exact same_thread he' hf' (fun h' => hne (by rw [h'])) hov l
  · exact (ring_pair (hF l hl) (hE l hl) hpg hch hu1 hu2 hv1 hv2 he'.lt hf'.lt).imp lift lift
  · exact (ring_pair (hF l hl) (hE l hl) hph hcg hv1 hv2 hu1 hu2 hf'.lt he'.lt).symm.imp
      lift lift
  · rcases hw with h | h <;> cases h

/-- Prefix counts of arrivals grow. -/
private theorem arrivals_mono {mb : Loc} {g a b : Nat} (h : a ≤ b) :
    arrivals mb ((X.tr g).take a) ≤ arrivals mb ((X.tr g).take b) :=
  (List.take_isPrefix_take.mpr (Or.inl h)).countP_le

/-- **The facts of a ring region written asynchronously and read by threads**: a thread access of
a byte `l` of `R` is a consumer's read with its read counts; an asynchronous access is a write of
a producer whose issue follows `u + 1` successful polls of `E l`, finished at every consumer's
poll of `F l` with `u` earlier ones; two writes of one use at a byte are one; a byte with a
producer has a consumer; a consumer's arrival on `E l` follows more successful polls of `F l` than
its earlier arrivals, and a proxy fence follows its reads before it. -/
structure AsyncRing (L : Launch) (X : Execution) (R : Loc → Prop) (F E : Loc → Loc)
    (prod cons : Loc → Nat → Prop) : Prop where
  hE : ∀ l, R l → UnitHandoff L X (E l) (cons l) (prod l) 1
  hcta : ∀ l g, R l → prod l g ∨ cons l g →
    g < L.threads ∧ l.space = .shared ∧ l.cta = g / L.block
  hcons : ∀ l g, R l → prod l g → ∃ h, cons l h
  hrd : ∀ g k a w l, X.Access (g, k) a w → a.Covers l → R l →
    w = false ∧ cons l g ∧ ∃ v, okPolls (F l) ((X.tr g).take k) = v + 1 ∧
      arrivals (E l) ((X.tr g).take k) = v
  hwr : ∀ g k p a w l, X.Intent (.async (g, k) p) a w → a.Covers l → R l →
    w = true ∧ (∃ t, p = .write t) ∧ prod l g ∧ k < (X.tr g).length ∧
    ∃ u, okPolls (E l) ((X.tr g).take k) = u + 1 ∧
      ∀ h j pc par acq sc, cons l h → X.get (h, j) = some ⟨pc, .wait (F l) par true acq sc⟩ →
        okPolls (F l) ((X.tr h).take j) = u → AsyncFinished L X (g, k) p (h, j)
  hww : ∀ g k p g' k' p' a b l, X.Intent (.async (g, k) p) a true →
    X.Intent (.async (g', k') p') b true → a.Covers l → b.Covers l → R l →
    okPolls (E l) ((X.tr g).take k) = okPolls (E l) ((X.tr g').take k') →
    g = g' ∧ k = k' ∧ p = p'
  harr : ∀ l h ia pc tx cnt sc, R l → cons l h →
    X.get (h, ia) = some ⟨pc, .arrive (E l) tx cnt true sc⟩ →
    arrivals (E l) ((X.tr h).take ia) < okPolls (F l) ((X.tr h).take ia)
  hfence : ∀ l h j ia a pc tx cnt sc, R l → cons l h → X.Access (h, j) a false → j ≤ ia →
    X.get (h, ia) = some ⟨pc, .arrive (E l) tx cnt true sc⟩ →
    ∃ jf, j < jf ∧ jf < ia ∧ X.IsProxyFence (h, jf) (.async (some (.shared .cta))) none

section
variable {R : Loc → Prop} {F E : Loc → Loc} {prod cons : Loc → Nat → Prop}

/-- **A read of use `v` and an asynchronous write of use `u` of one byte**: the write is before
the read when `u ≤ v` (the read follows the consumer's poll of use `u`, at which the write is
finished), the read before the write when `v < u` (the consumer's proxy fence between the read and
its arrival of use `v` on `E l`, observed by the producer's poll before the issue). -/
theorem AsyncRing.rw_use (h : AsyncRing L X R F E prod cons) {g k gi ki : Nat}
    {p : AsyncCopy.Part} {a' b' : Acc} {l : Loc} {u v : Nat} (hr : X.Access (g, k) a' false)
    (hwi : X.Intent (.async (gi, ki) p) b' true) (hca : a'.Covers l) (hcb : b'.Covers l)
    (hl : R l) (hv : okPolls (F l) ((X.tr g).take k) = v + 1)
    (hu : okPolls (E l) ((X.tr gi).take ki) = u + 1) :
    (u ≤ v → ByteCausality L X l (.async (gi, ki) p) (.thread (g, k))) ∧
      (v < u → ByteCausality L X l (.thread (g, k)) (.async (gi, ki) p)) := by
  obtain ⟨hE, hcta, hcons, hrd, hwr, -, harr, hfence⟩ := h
  obtain ⟨-, hc, v', hv1, hv2⟩ := hrd g k a' false l hr hca hl
  obtain ⟨-, ⟨t, rfl⟩, hpi, hil, u', hu', hobs⟩ := hwr gi ki p b' true l hwi hcb hl
  obtain rfl : v = v' := by omega
  obtain rfl : u = u' := by omega
  obtain ⟨hgt, hsp, hgc⟩ := hcta l g hl (.inr hc)
  obtain ⟨hit, -, hic⟩ := hcta l gi hl (.inl hpi)
  have hcov : AsyncCovers X (gi, ki) (.write t) l := ⟨b', true, hwi, hcb⟩
  refine ⟨fun huv => ?_, fun hvu => ?_⟩
  · obtain ⟨j', pc, par, acq, sc, hj', hw', hq⟩ :=
      UnitHandoff.exists_poll (X := X) (m := F l) (h := g) (f := k) (c := u) (by omega)
    exact .direct ⟨hcov, (g, j'), hobs g j' pc par acq sc hc hw' hq,
      .inl (base_of_poll hw' hj' hr.lt)⟩
  · obtain ⟨pp, pc, par, acq, sc, hpp, hwp, hqp⟩ :=
      UnitHandoff.exists_poll (X := X) (m := E l) (h := gi) (f := ki) (c := v + 1) (by omega)
    obtain ⟨ia, hia, rs, ⟨tx, cnt, pca, hga⟩, -⟩ :=
      hE l hl gi pp pc par acq sc v hpi hwp hqp g hc
    have hjia : k ≤ ia := arrival_index_ge hga (by simp [arrivesOn, sourceArrive]) hia hv2.le
    obtain ⟨jf, hjf, hfia, hfen⟩ := hfence l g k ia a' pca tx cnt rs hl hc hr hjia hga
    have hflen : jf < (X.tr g).length := lt_trans hfia (len_of_get hga)
    refine .direct ⟨hcov, .inl ⟨(g, jf), _, _, hfen, hgt, ⟨hsp, hgc⟩,
      ⟨hgt, hit, by rw [← hgc, ← hic]⟩, .single (.inl ⟨rfl, hjf, hflen, fun hs => ?_⟩),
      (hE l hl).hb hpi hwp hqp hc ((arrivals_mono hfia.le).trans hia.le) hpp hil⟩⟩
    have h1 := hs.1
    obtain ⟨pcf, hfg⟩ := hfen
    rw [hfg] at h1
    simp [Event.acc] at h1

/-- **Two asynchronous writes of uses `u < u'` of one byte are ordered**: a consumer's poll of use
`u` (at which the first is finished) is before its arrival of use `u` on `E l`, observed before
the second issue. -/
theorem AsyncRing.ww_use (h : AsyncRing L X R F E prod cons) {g k g' k' : Nat}
    {p p' : AsyncCopy.Part} {a' b' : Acc} {l : Loc} {u u' : Nat}
    (h1 : X.Intent (.async (g, k) p) a' true) (h2 : X.Intent (.async (g', k') p') b' true)
    (hca : a'.Covers l) (hcb : b'.Covers l) (hl : R l)
    (hu1 : okPolls (E l) ((X.tr g).take k) = u + 1)
    (hu2 : okPolls (E l) ((X.tr g').take k') = u' + 1) (huu : u < u') :
    ByteCausality L X l (.async (g, k) p) (.async (g', k') p') := by
  obtain ⟨hE, hcta, hcons, hrd, hwr, -, harr, hfence⟩ := h
  obtain ⟨-, -, hpi, -, u1, hu, hobs⟩ := hwr g k p a' true l h1 hca hl
  obtain ⟨-, -, hpi', hil', -, -, -⟩ := hwr g' k' p' b' true l h2 hcb hl
  obtain rfl : u = u1 := by omega
  obtain ⟨hit, -, hic⟩ := hcta l g hl (.inl hpi)
  obtain ⟨hit', -, hic'⟩ := hcta l g' hl (.inl hpi')
  obtain ⟨h0, hc0⟩ := hcons l g hl hpi
  obtain ⟨pp, pc, par, acq, sc, hpp, hwp, hqp⟩ :=
    UnitHandoff.exists_poll (X := X) (m := E l) (h := g') (f := k') (c := u + 1) (by omega)
  obtain ⟨ia, hia, rs, ⟨tx, cnt, pca, hga⟩, -⟩ :=
    hE l hl g' pp pc par acq sc u hpi' hwp hqp h0 hc0
  have hlt := harr l h0 ia pca tx cnt rs hl hc0 hga
  obtain ⟨j', pc2, par2, acq2, sc2, hj', hw2, hq2⟩ :=
    UnitHandoff.exists_poll (X := X) (m := F l) (h := h0) (f := ia) (c := u) (by omega)
  exact .direct ⟨.inl ⟨hit, hit', hic.symm.trans hic'⟩, .direct ⟨⟨a', true, h1, hca⟩,
    ⟨b', true, h2, hcb⟩, .inl ⟨(h0, j'), hobs h0 j' pc2 par2 acq2 sc2 hc0 hw2 hq2,
      (hE l hl).hb hpi' hwp hqp hc0 ((arrivals_mono hj'.le).trans hia.le) hpp hil'⟩⟩⟩

/-- **A ring region written asynchronously and read by threads is ordered**
(`AsyncRing`). -/
theorem ring_async_ordered (h : AsyncRing L X R F E prod cons) : ByteOrdered L X R := by
  intro e f a b l hcon ha hb hl _
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have hrd := h.hrd
  have hwr := h.hwr
  have hww := h.hww
  -- a read and a write
  have rw_ord : ∀ {g k gi ki p} {a' b' : Acc}, X.Access (g, k) a' false →
      X.Intent (.async (gi, ki) p) b' true → a'.Covers l → b'.Covers l →
      ByteCausality L X l (.thread (g, k)) (.async (gi, ki) p) ∨
        ByteCausality L X l (.async (gi, ki) p) (.thread (g, k)) := by
    intro g k gi ki p a' b' hr hwi hca hcb
    obtain ⟨-, -, v, hv1, -⟩ := hrd g k a' false l hr hca hl
    obtain ⟨-, -, -, -, u, hu, -⟩ := hwr gi ki p b' true l hwi hcb hl
    have hh := h.rw_use hr hwi hca hcb hl hv1 hu
    by_cases huv : u ≤ v
    · exact .inr (hh.1 huv)
    · exact .inl (hh.2 (by omega))
  have ww_chain : ∀ {g k p g' k' p'} {a' b' : Acc} {u u' : Nat},
      X.Intent (.async (g, k) p) a' true → X.Intent (.async (g', k') p') b' true →
      a'.Covers l → b'.Covers l → okPolls (E l) ((X.tr g).take k) = u + 1 →
      okPolls (E l) ((X.tr g').take k') = u' + 1 → u < u' →
      ByteCausality L X l (.async (g, k) p) (.async (g', k') p') :=
    fun h1 h2 hca hcb hu1 hu2 huu => h.ww_use h1 h2 hca hcb hl hu1 hu2 huu
  cases e with
  | thread x =>
    obtain ⟨g, k⟩ := x
    obtain ⟨rfl, -⟩ := hrd g k a we l he ha hl
    cases f with
    | thread y =>
      obtain ⟨h, j⟩ := y
      obtain ⟨rfl, -⟩ := hrd h j b wf l hf hb hl
      rcases hw with h | h <;> cases h
    | async i p =>
      obtain ⟨gi, ki⟩ := i
      obtain ⟨rfl, -⟩ := hwr gi ki p b wf l hf hb hl
      exact rw_ord he hf ha hb
  | async i p =>
    obtain ⟨gi, ki⟩ := i
    obtain ⟨rfl, -⟩ := hwr gi ki p a we l he ha hl
    cases f with
    | thread y =>
      obtain ⟨h, j⟩ := y
      obtain ⟨rfl, -⟩ := hrd h j b wf l hf hb hl
      exact (rw_ord hf he hb ha).symm
    | async i' p' =>
      obtain ⟨gi', ki'⟩ := i'
      obtain ⟨rfl, -⟩ := hwr gi' ki' p' b wf l hf hb hl
      obtain ⟨-, -, -, -, u, hu, -⟩ := hwr gi ki p a true l he ha hl
      obtain ⟨-, -, -, -, u', hu', -⟩ := hwr gi' ki' p' b true l hf hb hl
      rcases lt_trichotomy u u' with h | rfl | h
      · exact .inl (ww_chain he hf ha hb hu hu' h)
      · obtain ⟨rfl, rfl, rfl⟩ := hww gi ki p gi' ki' p' a b l he hf ha hb hl (hu.trans hu'.symm)
        exact (hne rfl).elim
      · exact .inr (ww_chain hf he hb ha hu' hu h)

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

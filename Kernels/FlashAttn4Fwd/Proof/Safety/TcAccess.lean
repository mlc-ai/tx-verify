-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Lemmas.Tmem.PairProtocol

@[expose] public section

/-! # The Tensor Memory access branch of `Unsafe`

The kernel's Tensor Memory accesses are the MMAs' result cells (the QK MMAs in a stage's scores,
the PV MMAs in a stage's accumulator, both CTAs of the pair: `ScoreFacts.mma_cells`), their
accumulator reads (the same cells: `TcFacts.mma_reads`), the PV MMAs' A reads (a stage's
probabilities: `ScoreFacts.pv_polls`, `TcFacts.qk_smem`), and the softmax and correction loads and
stores of their own CTA's lanes (`ScoreFacts.soft_ld`/`soft_st`, `OAccFacts.corr_ld`/`corr_st`);
no copy is issued. Every accessed cell is in the first 512 columns of a CTA of the accessing
thread's pair (`access_info`).

*Allocation* (`access_allocated`). For a cell of the accessing thread's CTA, lane 0 of warp 12 of
the CTA allocates before the access, with an event past its allocation (`AllocBefore`): the
allocation is complete and recorded in its CTA's history (`alloc_recorded`), of all 512 columns
at column 0 (`alloc_zero`). A cell of the other CTA of the pair (the leader's MMAs) is covered by
that CTA's allocation through the paired allocation (`PeerCovers`, EXT-PAIR-ALLOC-ORDER).

*Release* (`access_done`). A release of a covering allocation (`CoversWithPeer`) is a deallocation
of warp 12 of a CTA of the cell's pair (the record's own, or its paired peer's: `peer_pair`). Every
MMA is done before it (`MmaDoneDealloc`: the O-full commits observed by the correction's `oWait`,
then the correction's `bar.sync 2` and the handshake), and it comes after the barrier-2 event of
ordinal 1 of each softmax and correction thread of its pair, which follows the thread's `tcgen05`
events: what the thread did before that event happens before it (`WaitDealloc`: their barrier-2
events before the MMA warp's `bar.sync 2`, then the handshake). That event is not a `tcgen05`
event, so a load before it is finished by the `wait::ld` right after the load, a store by the
`wait::st` after it and before that event (`CompletedBefore`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof Tmem.Pair TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Lane 0 of warp 12 of CTA `cta`, which allocates the CTA's Tensor Memory. -/
abbrev allocLane (L : Launch) (cta : Nat) : Nat := cta * L.block + 12 * 32

/-- The resource operations are warp 12's (`TmemFacts.event`). -/
theorem tmemWarpOps (hpre : Pre P L mem0) (htm : TmemFacts L X) : TmemWarpOps L X 12 where
  cluster := hpre.cluster
  launch := hpre.oneDimLaunch
  warp_lt := by rw [hpre.block]; decide
  event hg he := by
    obtain ⟨h1, h2, h3, -⟩ := htm.event hg he
    exact ⟨h1, h2, h3⟩

/-- **AllocBefore**: lane 0 of warp 12 of the CTA of an accessed cell of the accessing thread's
CTA allocates before the access, and goes on past the allocation. -/
def AllocBefore (L : Launch) (X : Execution) : Prop :=
  ∀ {e : EvId} {cell : Cell}, Access L X e cell → cell.cta = ctaOf L e.1 →
    ∃ j pc grp dst n, X.get (allocLane L cell.cta, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr (allocLane L cell.cta)).length ∧
      baseCausality L X (allocLane L cell.cta, j) e

/-- **PeerCovers**: an accessed cell of the other CTA of the accessing thread's pair is covered by
an allocation of its CTA through the paired allocation (EXT-PAIR-ALLOC-ORDER). -/
def PeerCovers (L : Launch) (X : Execution) : Prop :=
  ∀ {e : EvId} {cell : Cell}, Access L X e cell → cell.cta ≠ ctaOf L e.1 →
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column

/-- The owner of a covering allocation is its record's CTA. -/
theorem covers_owner {r : Requests} {owner : Nat} {e : EvId} {col : Nat}
    (h : Covers L X r owner e col) : owner = r.own.cta :=
  let ⟨_, _, _, ho, _⟩ := h
  ho

/-- **MmaDoneDealloc**: every MMA is done before every deallocation of its pair. -/
def MmaDoneDealloc (L : Launch) (X : Execution) : Prop :=
  ∀ {i d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}, IsMma X i →
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
    ctaOf L d.1 / 2 = ctaOf L i.1 / 2 → DoneBefore L X i d

/-- **WaitDealloc**: a deallocation of the pair of a softmax or correction thread comes after a
later event of the thread than each of its `tcgen05` events, not itself a `tcgen05` event,
before which everything the thread did happens before the deallocation. -/
def WaitDealloc (L : Launch) (X : Execution) : Prop :=
  ∀ {h k pc pc' a n : Nat} {wk : TcKind} {d : EvId} {grp : CtaGroup} {dst : Option Loc},
    h < L.threads → warpOf L h < 12 → X.get (h, k) = some ⟨pc, .tc wk⟩ →
    X.get d = some ⟨pc', .tc (.resource grp dst (.dealloc a n))⟩ →
    ctaOf L d.1 / 2 = ctaOf L h / 2 → ∃ b, NonTcAfter X h k b ∧ ∀ e < b, baseCausality L X (h, e) d

/-- The cells of an MMA's results: in one stage's scores or accumulator, of its pair. -/
theorem mma_cell_info (ht : ScoreFacts L X) {i : EvId} {cell : Cell} (hc : X.MmaCell i cell) :
    i.1 < L.threads ∧ cell.cta / 2 = ctaOf L i.1 / 2 ∧ cell.column < 512 := by
  obtain ⟨d, s, acc, mask, row, col, hi, -⟩ := id hc
  obtain ⟨hg, -, hl, st, hst, h | h⟩ := ht.mma_cells hi
  · obtain ⟨hS, hc⟩ := h cell hc
    unfold InS at hS
    unfold leadCta at hc hl
    exact ⟨hg, by omega, by omega⟩
  · obtain ⟨hO, hc⟩ := h cell hc
    unfold InO at hO
    unfold leadCta at hc hl
    exact ⟨hg, by omega, by omega⟩

/-- The completions an access needs: an MMA's, a load's or a store's. -/
def AccessKind (X : Execution) (e : EvId) : Prop :=
  IsMma X e ∨ (∃ a vals, X.TLd e a vals .s32x32b) ∨ ∃ a vals, X.TSt e a vals .s32x32b

/-- **An access is an MMA, a load or a store, of a cell in the first 512 columns of a CTA of its
thread's pair.** -/
theorem access_info (ht : ScoreFacts L X) (ho : OAccFacts L X) (htc : TcFacts L X) {e : EvId}
    {cell : Cell} (hacc : Access L X e cell) :
    e.1 < L.threads ∧ cell.cta / 2 = ctaOf L e.1 / 2 ∧ cell.column < 512 ∧ AccessKind X e := by
  rcases hacc with (hm | ⟨d, s, mask, row, col, hi, hc⟩ | ⟨d, s, acc, mask, index, b, hi, ha⟩) |
      ⟨j, hlc⟩ | hsc | ⟨c, cta, idx, lane, hcp, -⟩ | ⟨sp, hsh, -⟩ | ⟨sp, hsh, -⟩
  · obtain ⟨d, s, acc, mask, -, -, hi, -⟩ := id hm
    obtain ⟨h1, h2, h3⟩ := mma_cell_info ht hm
    exact ⟨h1, h2, h3, .inl ⟨_, _, _, _, hi⟩⟩
  · obtain ⟨h1, h2, h3⟩ := mma_cell_info ht (htc.mma_reads hi hc)
    exact ⟨h1, h2, h3, .inl ⟨_, _, _, _, hi⟩⟩
  · obtain ⟨c0, hc0⟩ := htc.mma_cell hi
    obtain ⟨d0, s0, acc0, mask0, row0, col0, hi0, -⟩ := id hc0
    obtain ⟨hg, -, hl, st, hst, h | h⟩ := ht.mma_cells hi
    · have hnone := htc.qk_smem hst hi hc0 (h c0 hc0).1
      simp [aCell, hnone] at ha
    · obtain ⟨hO, -⟩ := h c0 hc0
      obtain ⟨-, -, -, hcells⟩ := ht.pv_polls hi hc0 hO
      obtain ⟨hP, hcc, -⟩ := hcells index cell b ha
      unfold InP at hP
      unfold leadCta at hcc hl
      exact ⟨hg, by omega, by omega, .inl ⟨_, _, _, _, hi⟩⟩
  · obtain ⟨a, vals, hld, hj, rfl⟩ := ht.loadCell hlc
    obtain ⟨hh, h12⟩ := ht.tc_role (.inl hld)
    refine ⟨hh, rfl, ?_, .inr (.inl ⟨_, _, hld⟩)⟩
    by_cases h8 : warpOf L e.1 < 8
    · have := (ht.soft_ld hh h8 hld).1 j hj
      unfold InS at this
      omega
    · obtain ⟨st, hst, hc, -⟩ := ho.corr_ld hh (by omega) h12 hld
      have := hc j hj
      unfold InO at this
      omega
  · obtain ⟨a, vals, j, hst, hj, rfl⟩ := ht.storeCell hsc
    obtain ⟨hh, h12⟩ := ht.tc_role (.inr hst)
    refine ⟨hh, rfl, ?_, .inr (.inr ⟨_, _, hst⟩)⟩
    by_cases h8 : warpOf L e.1 < 8
    · have := (ht.soft_st hh h8 hst).1 j hj
      unfold InP at this
      omega
    · obtain ⟨st, hst, hc, -⟩ := ho.corr_st hh (by omega) h12 hst
      have := hc j hj
      unfold InO at this
      omega
  · exact absurd hcp (ht.no_cp _ _)
  · exact absurd hsh (ht.no_shift _ _)
  · exact absurd hsh (ht.no_shift _ _)

/-- **An access of a cell of its thread's CTA is allocated by that CTA's allocation.** -/
theorem own_allocated (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) (hab : AllocBefore L X) {e : EvId} {cell : Cell}
    (hacc : Access L X e cell) (hc : cell.cta = ctaOf L e.1) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  have hto := tmemWarpOps hpre htm
  obtain ⟨j, pc, grp, dst, n, hal, hlen, hhb⟩ := hab hacc hc
  obtain ⟨r, hr, hwi, hz⟩ := alloc_recorded hX hto (cta := cell.cta)
    (hX.tmemPairBlocking.covered ⟨pc, _, _, _, hal, trivial⟩ hlen)
  obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc n base := by
    obtain ⟨-, -, -, hreq, -⟩ := record_info hX hto hr
    have hev := ((hX.tmemPair.1 _).1 r hr).2.2.2.2.1 0
    rw [hwi, hal] at hev
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hev
    exact Tmem.Action.request_eq_alloc (hreq.trans hev.2.2.2.symm)
  obtain ⟨rfl, rfl⟩ := alloc_zero hX hto hr _ _ hwa
  obtain ⟨hc, -⟩ := record_info hX hto hr
  refine ⟨cell.cta, r, hr, Covers.own ⟨512, 0, hwa, hc.symm, Nat.zero_le _, by omega, ?_⟩⟩
  rw [hwi]
  exact hhb

/-- **An access is allocated**: by its thread's CTA's allocation, or, for a cell of the other CTA
of the pair, through the paired allocation. -/
theorem access_allocated (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) (hab : AllocBefore L X) (hpc : PeerCovers L X) {e : EvId} {cell : Cell}
    (hacc : Access L X e cell) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  by_cases hc : cell.cta = ctaOf L e.1
  · exact own_allocated hpre hX htm hab hacc hc hcol
  · exact hpc hacc hc

/-- A paired peer of a record of this kernel is in its CTA pair. -/
theorem peer_pair (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    {q : WarpRequest × WarpRequest} (hq : q ∈ X.tmemPairing) : q.1.cta / 2 = q.2.cta / 2 := by
  obtain ⟨⟨⟨-, -, hc⟩, -⟩, -⟩ := (hX.tmemPair.2.1 q hq).1.2.2.2
  simpa only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster] using hc

/-- **A release of a record of CTA `cta` is a deallocation of a CTA of `cta`'s pair.** -/
theorem release_cta (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta) {d : EvId}
    (hrel : ReleaseOf L X r d) :
    ∃ pc grp a n, X.get d = some ⟨pc, .tc (.resource grp none (.dealloc a n))⟩ ∧
      ctaOf L d.1 / 2 = cta / 2 := by
  have hblock := hpre.block
  have hto := tmemWarpOps hpre htm
  obtain ⟨hlc, -⟩ := record_info hX hto hr
  have hd : ∃ s : Requests, s.own.cta / 2 = cta / 2 ∧ s.own.warp = 12 ∧ OwnRelease L X s d := by
    rcases hrel with h | ⟨q, hq, s, hs, hpair, h⟩
    · exact ⟨r, by rw [hlc], (record_info hX hto hr).2.1, h⟩
    · refine ⟨s, ?_, (record_info hX hto hs).2.1, h⟩
      have hp := peer_pair hpre hX hq
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h2, ← hlc, ← h1, hp]
      · rw [← h2, ← hlc, ← h1, hp]
  obtain ⟨s, hwc, hw12, n, base, pc, -, ⟨grp, hget⟩, hlane⟩ := hd
  refine ⟨pc, grp, base, n, hget, ?_⟩
  rw [← hwc]
  unfold ctaOf
  rcases hlane with ⟨lane, hd1, -⟩ | ⟨h, -⟩
  · simp only [WarpRequest.event, hw12] at hd1
    have := lane.isLt
    rw [hd1, hblock]
    omega
  · rw [h]

/-- **An access is complete before a deallocation of its pair.** -/
theorem access_done (ht : ScoreFacts L X) (ho : OAccFacts L X) (hmd : MmaDoneDealloc L X)
    (hwd : WaitDealloc L X) {e d : EvId} (he : e.1 < L.threads) (hk : AccessKind X e) {pc a n : Nat}
    {grp : CtaGroup} {dst : Option Loc}
    (hd : X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩)
    (hc : ctaOf L d.1 / 2 = ctaOf L e.1 / 2) : TcMma.CompletedBefore L X e d := by
  obtain ⟨g, k⟩ := e
  dsimp only at he hc
  rcases hk with ⟨dm, s, acc, mask, pcm, hm⟩ | ⟨a', vals, pcl, hl⟩ | ⟨a', vals, pcs, hs⟩
  · refine ⟨fun ⟨_, _, _, pc', h⟩ => ?_, fun ⟨_, _, _, pc', h⟩ => ?_, fun _ => ?_⟩
    · rw [hm] at h; cases h
    · rw [hm] at h; cases h
    · exact hmd ⟨_, _, _, _, pcm, hm⟩ hd hc
  · obtain ⟨-, h12⟩ := ht.tc_role (.inl ⟨pcl, hl⟩)
    obtain ⟨b, ⟨hkb, ev, hbget, hbk⟩, hbhb⟩ := hwd he h12 hl hd hc
    have hlen : k + 1 < (X.tr g).length := by
      have := (List.getElem?_eq_some_iff.mp hbget).1
      simp only at this
      omega
    have hw : ∃ pc', X.get (g, k + 1) = some ⟨pc', .tc .waitLd⟩ := by
      by_cases h8 : warpOf L g < 8
      · exact (ht.soft_ld he h8 ⟨pcl, hl⟩).2.1 hlen
      · obtain ⟨-, -, -, hw, -⟩ := ho.corr_ld he (by omega) h12 ⟨pcl, hl⟩
        exact hw hlen
    obtain ⟨pcw, hwget⟩ := hw
    have hkb1 : k + 1 < b := by
      rcases Nat.lt_or_eq_of_le (show k + 1 ≤ b by omega) with h | h
      · exact h
      · rw [h, hbget] at hwget
        cases hwget
        exact absurd rfl (hbk.1 _)
    refine ⟨fun _ => ⟨(g, k + 1), ⟨pcw, hwget⟩, rfl, Nat.lt_succ_self k,
      .inl (hbhb _ hkb1)⟩, fun ⟨_, _, _, pc', h⟩ => ?_, fun h => ?_⟩
    · rw [hl] at h; cases h
    · rcases h with ⟨_, _, _, _, pc', h⟩ | ⟨_, pc', h⟩ | ⟨_, pc', h⟩ <;> rw [hl] at h <;> cases h
  · obtain ⟨-, h12⟩ := ht.tc_role (.inr ⟨pcs, hs⟩)
    obtain ⟨b, hnb, hbhb⟩ := hwd he h12 hs hd hc
    have hw : ∃ w pc', k < w ∧ w < b ∧ X.get (g, w) = some ⟨pc', .tc .waitSt⟩ := by
      by_cases h8 : warpOf L g < 8
      · obtain ⟨-, -, -, -, -, hw⟩ := ht.soft_st he h8 ⟨pcs, hs⟩
        obtain ⟨w, pc', hkw, hwb, hwg, -⟩ := hw b hnb
        exact ⟨w, pc', hkw, hwb, hwg⟩
      · obtain ⟨st, -, -, -, -, hw⟩ := ho.corr_st he (by omega) h12 ⟨pcs, hs⟩
        obtain ⟨w, pc', hkw, hwb, hwg, -⟩ := hw b hnb
        exact ⟨w, pc', hkw, hwb, hwg⟩
    obtain ⟨w, pcw, hkw, hwb, hwget⟩ := hw
    refine ⟨fun ⟨_, _, _, pc', h⟩ => ?_, fun _ => ⟨(g, w), ⟨pcw, hwget⟩, rfl, hkw,
      .inl (hbhb _ hwb)⟩, fun h => ?_⟩
    · rw [hs] at h; cases h
    · rcases h with ⟨_, _, _, _, pc', h⟩ | ⟨_, pc', h⟩ | ⟨_, pc', h⟩ <;> rw [hs] at h <;> cases h

/-- **No Tensor Memory access is unallocated or outlives its allocation.** -/
theorem no_access_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : ScoreFacts L X) (ho : OAccFacts L X) (htc : TcFacts L X) (htm : TmemFacts L X)
    (hab : AllocBefore L X) (hpc : PeerCovers L X) (hmd : MmaDoneDealloc L X)
    (hwd : WaitDealloc L X) : ¬ AccessUnsafe L X := by
  refine fun hn => hn fun e cell hacc => ?_
  obtain ⟨he, hcta, hcol, hk⟩ := access_info ht ho htc hacc
  refine ⟨access_allocated hpre hX htm hab hpc hacc hcol, fun cta r hr hcov d hrel => ?_⟩
  have hown := covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX (tmemWarpOps hpre htm) hr
  obtain ⟨pc, grp, a, n, hd, hdc⟩ := release_cta hpre hX htm hr hrel
  exact .inl (access_done ht ho hmd hwd he hk hd (by rw [hdc, ← hlc, ← hown, hcta]))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety

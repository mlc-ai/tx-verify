-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemLifeBar
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OFullHandoff

@[expose] public section

/-! # The lifetime of the Tensor Memory allocation

The three protocol premises of the Tensor Memory access branch (`Safety/TcAccess`), stated here
by their bodies (`Safety.AllocBefore`, `Safety.MmaDoneDealloc`, `Safety.WaitDealloc`):

* **WaitDealloc** (`waitDealloc`): a softmax or correction `tcgen05` event comes before the
  thread's barrier-2 event of ordinal 1 (`wait_lt`), which every thread of warps 0-12 of the CTA
  makes once warp 12 of the CTA has passed its `bar.sync 2` of ordinal 1 (`member`), and what the
  thread did before that event happens before the deallocation. In the thread's own CTA the
  deallocation follows that `bar.sync`; in the other CTA it follows the handshake, whose arrival
  by lane 0 of warp 12 follows that lane's `bar.sync` (`peer_chain`).
* **MmaDoneDealloc** (`mmaDoneDealloc`): an MMA is in an item of its cluster
  (`TmemLifeFacts.mma_item`: the work item of its O-full commits of a stage); lane 0 of warp 8
  (a correction thread) of the deallocating CTA, at its barrier-2 event of ordinal 1, has polled
  that stage's O-full object once per item (`corr_items`), so one of its polls observes the
  commit after the MMA (`OAcc.OFullHandoff`, `oFull_done`) and comes before the barrier-2 event,
  which comes before the deallocation.
* **AllocBefore** (`allocOwn`): every access follows its thread's `bar.sync 2` of ordinal 0
  (`TmemLifeFacts.tc_sync`, `mma_sync`); lane 0 of warp 12 of the thread's CTA made its
  barrier-2 event of ordinal 0 (`member`) after its allocation (`bar2_alloc`) (`allocAt`). For an
  access of a cell of the thread's own CTA this is the cell's allocation. An MMA's access of a
  cell of the other CTA of the pair (the leader's MMAs write and read both CTAs' scores and
  accumulators) is covered through the paired allocation instead (`Protocol/PairAlloc`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma Tmem.Pair

noncomputable section

namespace TmemLife

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **WaitDealloc**: a deallocation of the pair of a softmax or correction thread comes after
the thread's barrier-2 event of ordinal 1, which follows each of its `tcgen05` events; what the
thread did before that event happens before the deallocation. -/
theorem waitDealloc (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (htm : TmemFacts L X) (hl : TmemLifeFacts L X)
    (hi : ∀ cta, TmemAlloc.HsInit L X cta) :
    ∀ {h k pc pc' a n : Nat} {wk : TcKind} {d : EvId} {grp : CtaGroup} {dst : Option Loc},
      h < L.threads → warpOf L h < 12 → X.get (h, k) = some ⟨pc, .tc wk⟩ →
      X.get d = some ⟨pc', .tc (.resource grp dst (.dealloc a n))⟩ →
      ctaOf L d.1 / 2 = ctaOf L h / 2 → ∃ b, NonTcAfter X h k b ∧ ∀ e < b, baseCausality L X (h,
          e) d := by
  intro h k pc pc' a n wk d grp dst hh h12 hk hd hpair
  obtain ⟨g, kd⟩ := d
  dsimp only at hpair
  have hg := Frame.lt_of_get hX hd
  have hdl := len_of_get hd
  dsimp only at hdl
  by_cases hc : ctaOf L h = ctaOf L g
  · obtain ⟨b, hbk, hbs⟩ := hl.dealloc_sync hg hd
    obtain ⟨i, pci, m, hi', hio⟩ := member hpre hX hst hl hbs hbk hdl (by decide) hc (by omega)
    exact ⟨i, ⟨wait_lt hl hh h12 hk hi' hio, _, hi', fun _ h => (nomatch h),
      fun _ h => (nomatch h)⟩,
      fun e he => bar2_baseCausality hpre hX hst hl hi' hio hbs hc he hbk hdl⟩
  · have hpc : pairCta (ctaOf L g) = ctaOf L h := by
      unfold pairCta
      omega
    obtain ⟨y, b, hbs, hby, hyl, hyd⟩ := peer_chain hpre hX htm hl hd (hi _)
    rw [hpc] at hbs hyl hyd
    have hc' : ctaOf L h = ctaOf L (TmemAlloc.lane0 L (ctaOf L h)) := (lane0_cta hpre _).symm
    obtain ⟨i, pci, m, hi', hio⟩ := member hpre hX hst hl hbs hby hyl (by decide) hc' (by omega)
    exact ⟨i, ⟨wait_lt hl hh h12 hk hi' hio, _, hi', fun _ h => (nomatch h),
      fun _ h => (nomatch h)⟩,
      fun e he => (bar2_baseCausality hpre hX hst hl hi' hio hbs hc' he hby hyl).trans hyd⟩

/-- An MMA before the commit that a correction poll of the O-full object observes is done before
every event the poll happens before. -/
theorem oFull_done (ht : ScoreFacts L X) (hO : OAcc.OFullHandoff L X) {h j pc p st : Nat}
    {acq : Bool} {sc : MbarScope} (hh : h < L.threads) (h8 : 8 ≤ warpOf L h)
    (h12 : warpOf L h < 12) (hst : st < 2)
    (hget : X.get (h, j) = some ⟨pc, .wait (oFullBar L (ctaOf L h) st) p true acq sc⟩)
    {x : EvId} (hx : IsMma X x) (hc : leadCta (ctaOf L x.1) = leadCta (ctaOf L h))
    (hu : OAcc.oCommits L X x.1 st x.2 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take j))
    {d : EvId} (hd : baseCausality L X (h, j) d) : DoneBefore L X x d := by
  obtain ⟨y, s, rank, ws, hcom, hcy, hmbar, hcnt, htgt, hrank, hobs, hsc⟩ :=
    hO hh h8 h12 hst hget
  have hthr : x.1 = y.1 := ht.tc_one hx (.inr ⟨s, hcom⟩) (hc.trans hcy.symm)
  obtain ⟨pcy, hy⟩ := hcom
  have hlt : x.2 < y.2 := by
    obtain ⟨_, _, _, _, _, hxp⟩ := hx.get
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · have h1 := Flow.countP_take_succ (p := commitsTo (oFullBar L (ctaOf L y.1) st)) hy
        (by simp [commitsTo, hmbar])
      have h2 := countP_take_mono (commitsTo (oFullBar L (ctaOf L y.1) st)) (X.tr y.1)
        (show y.2 + 1 ≤ x.2 by omega)
      unfold OAcc.oCommits at hcnt hu
      rw [hthr] at hu
      omega
    · have hxy : y = x := Prod.ext hthr.symm heq
      rw [hxy, hxp] at hy
      cases hy
  refine .inl ⟨(h, j), ws, ⟨.async y (.tcNotify rank), oFullBar L (ctaOf L h) st,
    ⟨y, s, rank, rfl, ⟨hthr, hlt, .inl hx, s, pcy, hy⟩, ⟨pcy, hy⟩, htgt, hrank⟩, hobs⟩, ?_, hd⟩
  rw [hthr]
  exact hsc

/-- **MmaDoneDealloc**: every MMA is done before every deallocation of its pair. -/
theorem mmaDoneDealloc (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (ht : ScoreFacts L X) (hO : OAcc.OFullHandoff L X)
    (hl : TmemLifeFacts L X) :
    ∀ {i d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}, IsMma X i →
      X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
      ctaOf L d.1 / 2 = ctaOf L i.1 / 2 → DoneBefore L X i d := by
  intro i d pc a n grp dst hi hd hpair
  obtain ⟨g, k⟩ := d
  dsimp only at hpair
  have hg := Frame.lt_of_get hX hd
  have hdl := len_of_get hd
  dsimp only at hdl
  have hblock := hpre.block
  obtain ⟨b, hbk, hbs⟩ := hl.dealloc_sync hg hd
  -- lane 0 of warp 8, a correction thread of the deallocating CTA
  have hhc : ctaOf L (ctaOf L g * L.block + 256) = ctaOf L g := by
    unfold ctaOf
    rw [hblock]
    omega
  have hw8 : warpOf L (ctaOf L g * L.block + 256) = 8 := by
    unfold warpOf
    rw [hblock]
    omega
  have hhl : ctaOf L g * L.block + 256 < L.threads := by
    have h1 : g < L.grid * 512 := by rw [← hblock]; exact hg
    unfold ctaOf Launch.threads
    rw [hblock]
    omega
  obtain ⟨ib, pci, m, hib, hio⟩ := member hpre hX hst hl hbs hbk hdl (by decide) hhc
    (by omega)
  obtain ⟨st, hst2, hwork⟩ := hl.mma_item hi
  have hwork' : workOf L (ctaOf L g * L.block + 256) (oFullCommits L X i.1 st i.2) < totOf L := by
    have hcl : clusterOf L (ctaOf L g * L.block + 256) = clusterOf L i.1 := by
      unfold clusterOf
      simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster, hhc]
      omega
    unfold workOf
    rw [hcl]
    exact hwork
  have hcnt := hl.corr_items hhl (by omega) (by omega) hib hio hst2 hwork'
  obtain ⟨j, pcj, p, acq, sc, hjb, hget, hokj⟩ := MbarRing.UnitHandoff.exists_poll hcnt
  have hlead : leadCta (ctaOf L i.1) = leadCta (ctaOf L (ctaOf L g * L.block + 256)) := by
    rw [hhc]
    unfold leadCta
    omega
  exact oFull_done ht hO hhl (by omega) (by omega) hst2 hget hi hlead (le_of_eq hokj.symm)
    (bar2_baseCausality hpre hX hst hl hib hio hbs hhc hjb hbk hdl)

/-- **The allocation of the accessing thread's CTA**: lane 0 of warp 12 of the CTA of the thread
of a Tensor Memory access allocates before the access, and goes on past the allocation. -/
theorem allocAt (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (ht : ScoreFacts L X) (hl : TmemLifeFacts L X) {e : EvId}
    {cell : Cell} (hacc : Access L X e cell) :
    ∃ j pc grp dst n, X.get (TmemAlloc.lane0 L (ctaOf L e.1), j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr (TmemAlloc.lane0 L (ctaOf L e.1))).length ∧
      baseCausality L X (TmemAlloc.lane0 L (ctaOf L e.1), j) e := by
  obtain ⟨g, k⟩ := e
  dsimp only
  have hk : ∃ b < k, Bar2Sync X g b 0 ∧ k < (X.tr g).length := by
    have hm : ∀ {d s acc mask}, X.MmaIssue (g, k) d s acc mask →
        ∃ b < k, Bar2Sync X g b 0 ∧ k < (X.tr g).length := fun hi => by
      obtain ⟨b, hb, hs⟩ := hl.mma_sync ⟨_, _, _, _, hi⟩
      exact ⟨b, hb, hs, IsMma.lt ⟨_, _, _, _, hi⟩⟩
    rcases hacc with (hc | ⟨d, s, mask, row, col, hi, -⟩ | ⟨d, s, acc, mask, index, b, hi, -⟩) |
        ⟨j, a, vals, sh, hld, -, -⟩ | ⟨a, vals, sh, j, hst', -, -⟩ | ⟨a, src, cta, idx, hcp, -⟩ |
        ⟨sp, hsh, -⟩ | ⟨sp, hsh, -⟩
    · obtain ⟨d, s, acc, mask, -, -, hi, -⟩ := id hc
      exact hm hi
    · exact hm hi
    · exact hm hi
    · obtain rfl := ht.tc_shape (.inl hld)
      obtain ⟨hh, h12⟩ := ht.tc_role (.inl hld)
      obtain ⟨b, hb, hs⟩ := hl.tc_sync hh h12 (.inl hld)
      exact ⟨b, hb, hs, Score.TLd.lt hld⟩
    · obtain rfl := ht.tc_shape (.inr hst')
      obtain ⟨hh, h12⟩ := ht.tc_role (.inr hst')
      obtain ⟨b, hb, hs⟩ := hl.tc_sync hh h12 (.inr hst')
      exact ⟨b, hb, hs, Score.TSt.lt hst'⟩
    · exact absurd hcp (ht.no_cp _ _)
    · exact absurd hsh (ht.no_shift _ _)
    · exact absurd hsh (ht.no_shift _ _)
  obtain ⟨b, hbk, hbs, hkl⟩ := hk
  have hc' : ctaOf L (TmemAlloc.lane0 L (ctaOf L g)) = ctaOf L g := lane0_cta hpre _
  obtain ⟨i, pci, m, hi, hio⟩ := member hpre hX hst hl hbs hbk hkl (by decide) hc'
    (by rw [lane0_warp hpre]; decide)
  obtain ⟨j, hji, pca, grp, dst, n, hj⟩ :=
    hl.bar2_alloc (Frame.lt_of_get hX hi) (lane0_warp hpre _) hi
  have hil := len_of_get hi
  dsimp only at hil
  exact ⟨j, pca, grp, dst, n, hj, by omega, bar2_baseCausality hpre hX hst hl hi hio hbs hc' hji hbk
      hkl⟩

/-- **AllocBefore at the accessing thread's CTA**: lane 0 of warp 12 of the CTA of an access of a
cell of that CTA allocates before the access, and goes on past the allocation. -/
theorem allocOwn (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hst : StatsFacts L X) (ht : ScoreFacts L X) (hl : TmemLifeFacts L X) {e : EvId}
    {cell : Cell} (hacc : Access L X e cell) (hcta : cell.cta = ctaOf L e.1) :
    ∃ j pc grp dst n, X.get (TmemAlloc.lane0 L cell.cta, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr (TmemAlloc.lane0 L cell.cta)).length ∧
      baseCausality L X (TmemAlloc.lane0 L cell.cta, j) e := by
  rw [hcta]
  exact allocAt hpre hX hst ht hl hacc

end TmemLife

end
end PTX.Kernels.FlashAttn4Fwd.Proof

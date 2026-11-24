-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaBlockOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaGemmTrace
import Lemmas.Protocol.NotifyBlocker
import Lemmas.Tcgen05.TcDataCell
import Lemmas.Tcgen05.TcProgramOrder

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The incoming Tensor Memory value for each output half -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvInitialAccumulator

open PTX PTX.Flow PTX.MbarRing Wg1Mma MmaDataTrace PvAccumulatorSource
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result (pvHalfIssue pvWriteCell)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The first issue of either output half overwrites the accumulator in block zero. -/
theorem first_overwrites (half : Fin 2) : pvAccum 0 (pvHalfIssue half 0) = false := by
  fin_cases half <;> rfl

/-- Every issue of the preceding block is present at a followed nonzero-block MMA state. -/
theorem actual_prior_block_issue_before {g j : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hb : 0 < d.i) (p : Fin 8) :
    ∃ i < j, Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma p, d.i - 1⟩)) ∧ Issue L X g i (d.i - 1) p := by
  let slot := rawSlot (d.i - 1)
  let m := GemmRing.empty L (ctaOf L g) slot
  have hg := Frame.lt_of_get hX he
  let trace := (hs g hg).machine.produces (hX.thr g hg)
  have hcount := Wg1MmaGemmTrace.pv_commits_before_block hpre hg slot trace hd
  change ((X.tr g).take j).countP (commitsTo m) = (d.i + (1 - slot.val)) / 2 at hcount
  obtain ⟨c, e, hcj, hc, hTick, hOrdinal⟩ := exists_nthEv (X := X) (p := commitsTo m)
    (g := g) (k := j) (n := (d.i - 1) / 2) (by
      rw [hcount]
      change (d.i - 1) / 2 < (d.i + (1 - (d.i - 1) % 2)) / 2
      omega)
  obtain ⟨sp, hKind, hMbar⟩ := Notify.commit_of_commitsTo hTick
  obtain ⟨q, hQ⟩ := FollowedPrefix.state_at hd hcj.le
  obtain ⟨state, o, hState, hFired⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine (by rw [hQ]; simp) hc
    (by intro _ h; rw [hKind] at h; cases h)
  have hSite := RingCommitEvents.commit_site hFired hKind
  have hTarget : TcCommit.target sp 0 = some m := by
    cases state <;> try exact hSite.elim
    case mma q =>
      obtain ⟨sp', he', _, hTargets⟩ := RingCommitEvents.commit_issue hpre hg hSite hFired
      obtain rfl := TcKind.commit.inj (Kind.tc.inj (hKind.symm.trans he'))
      rw [hTargets, ite_eq_left rfl, hMbar]
  obtain ⟨_, _, pv, hPvSlot, hpv, hpvState⟩ := GemmRing.actual_notification
    (obj := .svDone) (slot := slot) hpre hX hs hc hKind hTarget
  have hPvSite : pv.site = .pvCommit := by
    rcases hpv with ⟨h, _⟩ | ⟨_, h⟩
    · cases h
    · exact h
  have hPvCount := Wg1MmaGemmTrace.composed_count_here hpre hg .pv trace hpvState hPvSlot
  simp only [Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hPvCount
  change ((X.tr g).take c).countP (commitsTo m) = pv.i / 2 at hPvCount
  have hQuot : pv.i / 2 = (d.i - 1) / 2 := hPvCount.symm.trans hOrdinal
  have hBlock : pv.i = d.i - 1 := by
    change pv.i % 2 = (d.i - 1) % 2 at hPvSlot
    omega
  obtain ⟨i, hij, hState, hIssue⟩ := PvIssueHistory.pv_issue_of_commit hpre hX hs hc
    hpvState hPvSite p
  rw [hBlock] at hState hIssue
  exact ⟨i, by omega, hState, hIssue⟩

theorem prior_block_issue_before {g j : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hb : 0 < d.i) (p : Fin 8) :
    ∃ i < j, Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma p, d.i - 1⟩)) ∧ Issue L X g i (d.i - 1) p :=
  actual_prior_block_issue_before hpre hX hs he hd hb p

private theorem pv_index_order {g i j : Nat} {d d' : Wg1Mma.D} {k k' : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : Issue L X g i d.i k) (hj : Issue L X g j d'.i k')
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd' : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d')))
    (hk : d.site = .pvMma k) (hk' : d'.site = .pvMma k') (hij : i < j) :
    d.i < d'.i ∨ d.i = d'.i ∧ k.val < k'.val := by
  have hblock := Wg1Mma.block_order hij.le hd hd'
  rcases Nat.lt_or_eq_of_le hblock with h | h
  · exact .inl h
  · refine .inr ⟨h, ?_⟩
    have hg := Frame.lt_of_get hX hi.choose_spec
    have hr := Wg0ProbabilityUnique.actual_rank_strict_of_counted hpre hX (hs g hg).machine
      hi.choose_spec rfl (PTX.len_of_get hj.choose_spec).le hd hd' hij
    simp only [Bound.rank, Bound.mmaRank, Bound.mmaOrdinal, hk, hk', h] at hr
    have hkLt := k.isLt
    have hk'Lt := k'.isLt
    omega

/-- The lane and chunk of a rescale writer are pinned by its actual Tensor Memory footprint. -/
theorem rescale_coordinates {t j : Nat} {d : Wg0.D} {k : Fin 4} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hstore : RescaleStore P L X t j cell d k) :
    cell.cta = ctaOf L t ∧ cell.lane = tidOf L t ∧ cell.column / 64 = k.val := by
  have ht := Frame.lt_of_get hX hstore.store.choose_spec
  have hrole : wgOf L t = 0 := RingRoleGeometry.of_trace hX ht (hs t ht).machine hstore.state
  obtain ⟨address, words, shape, reg, ⟨_, he⟩, hr, hcell⟩ := hstore.covers
  have hk := congrArg Event.kind (Option.some.inj (he.symm.trans hstore.store.choose_spec))
  obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hk)
  have ht' : t % 384 < 128 := by
    unfold wgOf at hrole
    rw [tidOf_eq hpre] at hrole
    omega
  have hr' : reg < 64 := by simpa [Wg0.rescaleStoreValues] using hr
  have hk' := k.isLt
  have haddr : 64 * k.val < 2 ^ 16 := by omega
  rw [hcell, tcDataCell_s32x32b, tidOf_eq hpre]
  simp only [tcDataCell32, laneBase, PTX.laneOf, hpre.block, Nat.mod_eq_of_lt haddr]
  refine ⟨?_, ?_⟩
  · change t / 384 = t / L.block
    rw [hpre.block]
  · omega

private theorem rescale_index_order {t i j : Nat} {d d' : Wg0.D} {k : Fin 4} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : RescaleStore P L X t i cell d k) (hj : RescaleStore P L X t j cell d' k)
    (hij : i < j) : d.block < d'.block := by
  have hg := Frame.lt_of_get hX hi.store.choose_spec
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hi.store.choose_spec hi.state
  obtain ⟨_, _, _, _, hInv', _, _⟩ := Frame.fired_site hs hX hj.store.choose_spec hj.state
  have h := (show Wg0.Inv P L t d from hInv).subLt
  have h' := (show Wg0.Inv P L t d' from hInv').subLt
  rw [hi.site] at h
  rw [hj.site] at h'
  change d.sub < 1 at h
  change d'.sub < 1 at h'
  have hs0 : d.sub = 0 := by omega
  have hs0' : d'.sub = 0 := by omega
  have hBlock := (show Wg0.Inv P L t d from hInv).blockLt
  have hBlock' := (show Wg0.Inv P L t d' from hInv').blockLt
  have hr := Wg0ProbabilityUnique.actual_rank_strict_of_counted hpre hX (hs t hg).machine
    hi.store.choose_spec rfl (PTX.len_of_get hj.store.choose_spec).le hi.state hj.state hij
  simp only [Bound.rank, Bound.wg0Rank, Bound.wg0Ordinal, Bound.wg0Block, hi.site, hj.site,
    hs0, hs0', Nat.add_zero] at hr
  omega

/-- Two rescale writes of the same cell use the same lane and tile. -/
theorem same_rescale_lane {t t' j j' : Nat} {d d' : Wg0.D} {k k' : Fin 4}
    {cell : TcMma.Cell} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : RescaleStore P L X t j cell d k) (hj : RescaleStore P L X t' j' cell d' k') :
    t = t' ∧ k = k' := by
  obtain ⟨hc, hl, hcol⟩ := rescale_coordinates hpre hX hs hi
  obtain ⟨hc', hl', hcol'⟩ := rescale_coordinates hpre hX hs hj
  have hcta := hc.symm.trans hc'
  have htid := hl.symm.trans hl'
  rw [tidOf_eq hpre, tidOf_eq hpre] at htid
  change t / L.block = t' / L.block at hcta
  rw [hpre.block] at hcta
  exact ⟨by omega, Fin.ext (hcol.symm.trans hcol')⟩

private theorem pv_before {g i j b b' : Nat} {k k' : Fin 8}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : Issue L X g i b k) (hj : Issue L X g j b' k')
    (hlt : i < j) (hhalf : k.val % 2 = k'.val % 2) : TcMma.Before L X (g, i) (g, j) := by
  refine TcMma.Before.of_mma_po hi hj (Frame.lt_of_get hX hi.choose_spec) rfl hlt ?_
  exact ⟨congrArg (fun x => tmemO + 128 * x) hhalf, rfl, rfl, rfl, rfl⟩

private theorem read_before_pv {g i j block : Nat} {d : Wg1Mma.D} {k : Fin 8} {half : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : Issue L X g i block (pvHalfIssue half 0)) (hj : Issue L X g j d.i k)
    (hd : Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma (pvHalfIssue half 0), block⟩)))
    (hd' : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hsite : d.site = .pvMma k) (hblock : block ≤ d.i) (hhalf : k.val % 2 = half.val) :
    TcMma.ReadBefore L X .acc (g, i) (g, j) := by
  have hh := half.isLt
  have hfirst : (pvHalfIssue half 0).val = half.val := by
    simp only [pvHalfIssue, Fin.val_zero, Nat.mul_zero, Nat.zero_add]
  rcases Nat.lt_trichotomy j i with hlt | rfl | hlt
  · rcases pv_index_order hpre hX hs hj hi hd' hd hsite rfl hlt with h | ⟨_, hk⟩
    · exact (Nat.not_lt_of_ge hblock h).elim
    · rw [hfirst] at hk
      omega
  · exact .inl rfl
  · have hmatch : (pvHalfIssue half 0).val % 2 = k.val % 2 := by omega
    rcases pv_before hX hi hj hlt hmatch with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

/-- The initial value comes from the preceding block's last issue of this half or from
an actual rescale store in the current block. -/
def SourceKind (P : Params) (L : Launch) (X : Execution) (g i block : Nat) (half : Fin 2)
    (cell : TcMma.Cell) (src : EvId) : Prop :=
  (∃ j < i, src = (g, j) ∧
    Frame.stateAt (Machine.code P L) X g j =
      some (some (.mma ⟨.pvMma (pvHalfIssue half 3), block - 1⟩)) ∧
    Issue L X g j (block - 1) (pvHalfIssue half 3) ∧
    ¬ ∃ t j d r, RescaleStore P L X t j cell d r ∧ d.block = block) ∨
  ∃ t j d r, src = (t, j) ∧ RescaleStore P L X t j cell d r ∧ d.block = block

/-- The first PV issue of a later block reads the most recent writer of its accumulator cell. -/
theorem actual_from_first_issue {g i block : Nat} {half : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : Issue L X g i block (pvHalfIssue half 0))
    (hstate : Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma (pvHalfIssue half 0), block⟩)))
    (hb : 0 < block) (head : Fin 64) (col : Fin 256)
    (hHistory : StoreHistory P L X (g, i)
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩) :
    let cell : TcMma.Cell :=
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
    ∃ src, TcMma.ReadSource L X .acc src (g, i) cell ∧
      SourceKind P L X g i block half cell src := by
  dsimp only
  let cell : TcMma.Cell :=
    ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
  let first := pvHalfIssue half 0
  let last := pvHalfIssue half 3
  have hhalf := half.isLt
  have hcolMod := Nat.mod_lt col.val (by decide : 0 < 128)
  have hcol : cell.column < 256 := by
    change tmemO + 128 * half.val + col.val % 128 < 256
    unfold tmemO
    omega
  have hcolHalf : cell.column / 128 = half.val := by
    change (tmemO + 128 * half.val + col.val % 128) / 128 = half.val
    unfold tmemO
    omega
  have hFirst : first.val % 2 = half.val := by
    change (2 * 0 + half.val) % 2 = half.val
    omega
  have hLast : last.val % 2 = half.val := by
    change (2 * 3 + half.val) % 2 = half.val
    omega
  obtain ⟨issuer, hIssuer⟩ := GemmRing.exists_issuer (cta := ctaOf L g) hpre hX
    (fun t h => (hs t h).machine)
  have hg := hIssuer g i _ rfl hstate (by simp)
  subst issuer
  by_cases hRescale : ∃ t j d r, RescaleStore P L X t j cell d r ∧ d.block = block
  · obtain ⟨t, j, d, r, hwrite, hblock⟩ := hRescale
    have hne : (t, j) ≠ (g, i) := by
      intro hEq
      obtain ⟨tag, hGet⟩ := hwrite.store
      rw [hEq] at hGet
      cases congrArg Event.kind (Option.some.inj (hGet.symm.trans hi.choose_spec))
    have hcta := (rescale_coordinates hpre hX hs hwrite).1
    have hbefore := actual_earlier_rescale hpre hX hs hi hstate rfl hwrite hcta.symm hblock.le
    refine ⟨(t, j), ⟨hne, .inr (.inl hwrite.covers), hbefore, ?_,
      actual_source_live hpre hX hs hi hstate rfl rfl⟩, .inr ⟨t, j, d, r, rfl, hwrite, hblock⟩⟩
    rintro ⟨t', j'⟩ hOther
    obtain ⟨hc, ⟨q, k, hq, hsite, hp, hk⟩ | ⟨k, words, hStore, hCover, _, _, _⟩⟩ :=
      actual_output_writer hpre hX hs hcol hOther
    · have h := hIssuer t' j' q hc.symm hq (by rw [hsite]; simp)
      subst t'
      by_cases hlt : q.i < block
      · exact .inr (.inl (.of_done (actual_later_rescale hpre hX hs hp hq hsite hwrite hcta.symm
          (hblock.symm ▸ hlt))))
      · exact .inr (.inr (read_before_pv hpre hX hs hi hp hstate hq hsite (by omega)
          (hk.symm.trans hcolHalf)))
    · rcases hHistory hCover with ⟨q, k, hStore⟩ | hLate
      swap
      · exact .inr (.inr (.inr (.inl hLate)))
      obtain ⟨rfl, rfl⟩ := same_rescale_lane hpre hX hs hwrite hStore
      by_cases hlt : block < q.block
      · exact .inr (.inr (.inr (.inl (actual_later_rescale hpre hX hs hi hstate rfl hStore
          hcta.symm hlt))))
      · rcases Nat.lt_trichotomy j' j with h | rfl | h
        · exact .inr (.inl (.inr (.inl (TcMma.StoreDoneBefore.of_po hStore.store hwrite.store
            (Frame.lt_of_get hX hStore.store.choose_spec) rfl h))))
        · exact .inl rfl
        · have := rescale_index_order hpre hX hs hwrite hStore h
          omega
  · obtain ⟨prior, hprior, hpState, hp⟩ :=
      actual_prior_block_issue_before hpre hX hs hi.choose_spec hstate hb last
    have hwrite : X.MmaCell (g, prior) cell := by
      refine ⟨_, _, _, _, head.val, col.val, hp, ?_⟩
      simpa only [pvDest, hLast] using pvWriteCell L g (block - 1) last head col
    have hne : (g, prior) ≠ (g, i) := by
      intro hEq
      have h := congrArg Prod.snd hEq
      omega
    have hbefore := pv_before hX hp hi hprior (hLast.trans hFirst.symm)
    refine ⟨(g, prior), ⟨hne, .inl hwrite, .inl hbefore, ?_,
      actual_source_live hpre hX hs hi hstate rfl rfl⟩,
      .inl ⟨prior, hprior, rfl, hpState, hp, hRescale⟩⟩
    rintro ⟨t, j⟩ hOther
    obtain ⟨hc, ⟨q, k, hq, hsite, hn, hk⟩ | ⟨k, words, hStore, hCover, _, _, _⟩⟩ :=
      actual_output_writer hpre hX hs hcol hOther
    · have h := hIssuer t j q hc.symm hq (by rw [hsite]; simp)
      subst t
      have hkHalf := hk.symm.trans hcolHalf
      rcases Nat.lt_trichotomy j prior with h | rfl | h
      · exact .inr (.inl (.inl (pv_before hX hn hp h (hkHalf.trans hLast.symm))))
      · exact .inl rfl
      · have hblock : block ≤ q.i := by
          rcases pv_index_order hpre hX hs hp hn hpState hq rfl hsite h with hlt | ⟨_, hk⟩
          · change block - 1 < q.i at hlt
            omega
          · have hkLt := k.isLt
            change 2 * 3 + half.val < k.val at hk
            omega
        exact .inr (.inr (read_before_pv hpre hX hs hi hn hstate hq hsite hblock hkHalf))
    · rcases hHistory hCover with ⟨q, k, hStore⟩ | hLate
      swap
      · exact .inr (.inr (.inr (.inl hLate)))
      rcases Nat.lt_trichotomy q.block block with h | h | h
      · have hOld : q.block ≤ block - 1 := by omega
        exact .inr (.inl (actual_earlier_rescale hpre hX hs hp hpState rfl hStore hc.symm hOld))
      · exact (hRescale ⟨_, _, _, _, hStore, h⟩).elim
      · exact .inr (.inr (.inr (.inl
          (actual_later_rescale hpre hX hs hi hstate rfl hStore hc.symm h))))

theorem from_first_issue {g i block : Nat} {half : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hi : Issue L X g i block (pvHalfIssue half 0))
    (hstate : Frame.stateAt (Machine.code P L) X g i =
      some (some (.mma ⟨.pvMma (pvHalfIssue half 0), block⟩)))
    (hb : 0 < block) (head : Fin 64) (col : Fin 256) :
    let cell : TcMma.Cell :=
      ⟨ctaOf L g, head.val + 64 * (col.val / 128), tmemO + 128 * half.val + col.val % 128⟩
    ∃ src, TcMma.ReadSource L X .acc src (g, i) cell ∧
      SourceKind P L X g i block half cell src :=
  actual_from_first_issue hpre hX hs hi hstate hb head col
    (store_history_of_tracking hpre hX hs ht)

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvInitialAccumulator

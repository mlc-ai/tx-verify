-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceDef
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.OOrder
public import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

/-! # The accumulator sources of the MMAs

The last MMA of the thread before an accumulating MMA writing the cell (of the same score tile for
a QK MMA, `qk_accSource`), or, for the first PV MMA of a tile writing the cell, the rescale store of
the cell if there is one (`pv_accSource`). -/
namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

/-- A write is live until an MMA accessing its cell. -/
theorem sourceLive (hlive : TmemLive L X) {i src : EvId} {cell : Cell} (_hi : IsMma X i)
    (ha : X.MmaAccess i cell) : SourceLive L X src i cell :=
  fun cta r hr hcov release hrel => .inl (hlive (.inl ha) cta r hr hcov release hrel)

theorem sCommits_mono {g st k k' : Nat} (h : k ≤ k') :
    sCommits L X g st k ≤ sCommits L X g st k' :=
  countP_take_mono _ _ h

theorem pPolls_mono {g st k k' : Nat} (h : k ≤ k') : pPolls L X g st k ≤ pPolls L X g st k' := by
  unfold pPolls okPolls
  exact countP_take_mono _ _ h

/-- Two MMAs of one thread with the same accumulator, in program order, are a D→D pipelined
pair. -/
theorem mma_pipe (ht : ScoreFacts L X) {x y : EvId} {d d' : Nat} {s s' : OperandSpec}
    {acc acc' : Bool} {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask)
    (hy : X.MmaIssue y d' s' acc' mask') (hthr : x.1 = y.1) (hlt : x.2 < y.2)
    (hacc : SameAccumulator d s d' s') : Pipelined L X .dWrite x .dWrite y := by
  obtain ⟨hg, -⟩ := ht.mma_cells hx
  have hyl : y.2 < (X.tr y.1).length := isMma_lt ⟨_, _, _, _, hy⟩
  exact ⟨⟨⟨hg, hthr ▸ hg, by rw [hthr]⟩, by rw [hthr]⟩,
    .inl (isMma_baseCausality ⟨_, _, _, _, hx⟩ hthr hlt
        hyl), d, s, acc, mask, d', s', acc', mask', hx, hy,
    hacc⟩

/-- **The accumulator source of a QK MMA at its last writer**: the last MMA `K` of its thread
before it writing the cell, after as many commits to the stage's S-full object. -/
theorem qk_accSource_last (ht : ScoreFacts L X) (ho : OAccFacts L X) (hS : SFullHandoff L X)
    (hP : PReadyHandoff L X) (h2 : P2Gate L X) (hT : SourceFacts L X)
    {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    {st : Nat} (hst : st < 2) (hi : X.MmaIssue i d s acc mask) (hc : X.MmaCell i cell)
    (hS' : InS st cell) {K : Nat} (hK : K < i.2) (hcK : X.MmaCell (i.1, K) cell)
    (hcnt : sCommits L X i.1 st K = sCommits L X i.1 st i.2)
    (hmax : ∀ k, k < i.2 ∧ X.MmaCell (i.1, k) cell → k ≤ K) :
    ReadSource L X .acc (i.1, K) i cell := by
  obtain ⟨dK, sK, aK, mK, -, -, hiK, -⟩ := id hcK
  have hxm : IsMma X i := ⟨_, _, _, _, hi⟩
  have hKm : IsMma X (i.1, K) := ⟨_, _, _, _, hiK⟩
  have hcell : cell.cta = i.1 / L.block := (mma_s ht hi hc hS' hst cell hc).2
  refine readSource_acc.mpr ⟨fun h => by simp only [Prod.ext_iff] at h; omega, .inl hcK,
    .inl (.inr (mma_pipe ht hiK hi rfl hK (ht.mma_acc hiK hi hcK hc rfl hst (.inl ⟨hS', hS'⟩)))),
    fun other hwo => ?_, sourceLive hT.live hxm (.inl hc)⟩
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d', s', acc', mask', -, -, hoi, -⟩ := id hm
    have hco := (mma_s ht hoi hm hS' hst cell hm).2
    have hthr : other.1 = i.1 := ht.tc_one ⟨_, _, _, _, hoi⟩ (.inl hxm) (by rw [← hco, ← hcell])
    obtain ⟨g, k⟩ := other
    simp only at hthr
    subst hthr
    rcases Nat.lt_trichotomy k K with hlt | rfl | hgt
    · exact .inr (.inr (.inl (.inl (.inr (mma_pipe ht hoi hiK rfl hlt
        (ht.mma_acc hoi hiK hm hcK rfl hst (.inl ⟨hS', hS'⟩)))))))
    · exact .inl rfl
    · rcases Nat.lt_trichotomy k i.2 with h | h | h
      · exact absurd (hmax k ⟨h, hm⟩) (by omega)
      · exact .inr (.inl (Prod.ext rfl h))
      · exact .inr (.inr (.inr (.inr (mma_pipe ht hi hoi rfl h
          (ht.mma_acc hi hoi hc hm rfl hst (.inl ⟨hS', hS'⟩))))))
  · obtain ⟨g, k⟩ := other
    obtain ⟨a', vals', j', hst', hj', hceq⟩ := ht.storeCell hstc
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hst')
    by_cases h8 : 8 ≤ Prologue.warpIndex L g
    · obtain ⟨st', -, hOc, -⟩ := ho.corr_st hgl h8 hgw hst'
      have := hOc j' hj'
      rw [← hceq] at this
      unfold InO at this
      unfold InS at hS'
      omega
    have hw' : Prologue.warpIndex L g < 8 := by omega
    have hP' := (ht.soft_st hgl hw' hst').1 j' hj'
    rw [← hceq] at hP'
    have hws : Prologue.warpIndex L g / 4 = st := by
      unfold InP at hP'
      unfold InS at hS'
      omega
    have hcta : cell.cta = g / L.block := by rw [hceq]; rfl
    by_cases hle : sPolls L X g st k ≤ sCommits L X i.1 st i.2
    · obtain ⟨hq1, hq2⟩ := ht.qk_polls hst hKm hcK hS'
      simp only at hq1 hq2
      refine .inr (.inr (.inl (.inr (.inl (store_done ht hP h2 hgl hw' hst' hKm ?_ ?_ ?_)))))
      · show i.1 / L.block = _
        rw [← hcell, hcta]
      · rw [hws]
        show _ ≤ pPolls L X i.1 st K
        omega
      · intro _
        rw [hws]
        show _ ≤ p2Polls L X i.1 st K
        omega
    · exact .inr (.inr (.inr (.inl (s_doneBefore ht hS hgl hw' hxm
        (by rw [← hcell, hcta]) (by rw [hws]; omega) (tSt_lt hst')))))

/-- **The accumulator source of a QK MMA**: the last MMA of its thread before it writing the
cell. -/
theorem qk_accSource (ht : ScoreFacts L X) (ho : OAccFacts L X) (hT : SourceFacts L X)
    (hS : SFullHandoff L X) (hP : PReadyHandoff L X) (h2 : P2Gate L X)
    {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat}
    (hst : st < 2) (hi : X.MmaIssue i d s true mask) (hc : X.MmaCell i cell)
    (hS' : InS st cell) :
    ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ ReadSource L X .acc (i.1, k) i cell := by
  classical
  obtain ⟨k0, hk0, hc0, hcnt0⟩ := hT.qk_acc hst hi hc hS'
  let Q : Nat → Prop := fun k => k < i.2 ∧ X.MmaCell (i.1, k) cell
  have hQ : Q (Nat.findGreatest Q i.2) := Nat.findGreatest_spec (m := k0) hk0.le ⟨hk0, hc0⟩
  have hmax : ∀ k, Q k → k ≤ Nat.findGreatest Q i.2 := fun k hk => Nat.le_findGreatest hk.1.le hk
  obtain ⟨hK, hcK⟩ := hQ
  have hm1 := sCommits_mono (L := L) (X := X) (g := i.1) (st := st) (hmax k0 ⟨hk0, hc0⟩)
  have hm2 := sCommits_mono (L := L) (X := X) (g := i.1) (st := st) hK.le
  exact ⟨_, hK, hcK, qk_accSource_last ht ho hS hP h2 hT hst hi hc hS' hK hcK (by omega) hmax⟩

/-- **The accumulator source of a PV MMA in its tile**: the last MMA `K` of its thread before it
writing the cell, when it is of the same tile. -/
theorem pv_accSource_tile (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : PReadyHandoff L X)
    (hR : OReady L X) (hT : SourceFacts L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {cell : Cell} {st : Nat} (hst : st < 2)
    (hi : X.MmaIssue i d s acc mask) (hc : X.MmaCell i cell) (hO : InO st cell) {K : Nat}
    (hK : K < i.2) (hcK : X.MmaCell (i.1, K) cell)
    (htile : pPolls L X i.1 st K = pPolls L X i.1 st i.2)
    (hmax : ∀ k, k < i.2 ∧ X.MmaCell (i.1, k) cell → k ≤ K) :
    ReadSource L X .acc (i.1, K) i cell := by
  obtain ⟨dK, sK, aK, mK, -, -, hiK, -⟩ := id hcK
  have hxm : IsMma X i := ⟨_, _, _, _, hi⟩
  have hKm : IsMma X (i.1, K) := ⟨_, _, _, _, hiK⟩
  have hcell : cell.cta = i.1 / L.block := (mma_o ht hi hc hO cell hc).2
  refine readSource_acc.mpr ⟨fun h => by simp only [Prod.ext_iff] at h; omega, .inl hcK,
    .inl (.inr (mma_pipe ht hiK hi rfl hK (ht.mma_acc hiK hi hcK hc rfl hst (.inr ⟨hO, hO⟩)))),
    fun other hwo => ?_, sourceLive hT.live hxm (.inl hc)⟩
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d', s', acc', mask', -, -, hoi, -⟩ := id hm
    have hco := (mma_o ht hoi hm hO cell hm).2
    have hthr : other.1 = i.1 := ht.tc_one ⟨_, _, _, _, hoi⟩ (.inl hxm) (by rw [← hco, ← hcell])
    obtain ⟨g, k⟩ := other
    simp only at hthr
    subst hthr
    rcases Nat.lt_trichotomy k K with hlt | rfl | hgt
    · exact .inr (.inr (.inl (.inl (.inr (mma_pipe ht hoi hiK rfl hlt
        (ht.mma_acc hoi hiK hm hcK rfl hst (.inr ⟨hO, hO⟩)))))))
    · exact .inl rfl
    · rcases Nat.lt_trichotomy k i.2 with h | h | h
      · exact absurd (hmax k ⟨h, hm⟩) (by omega)
      · exact .inr (.inl (Prod.ext rfl h))
      · exact .inr (.inr (.inr (.inr (mma_pipe ht hi hoi rfl h
          (ht.mma_acc hi hoi hc hm rfl hst (.inr ⟨hO, hO⟩))))))
  · obtain ⟨g, k⟩ := other
    obtain ⟨a', vals', j', hst', hj', hceq⟩ := ht.storeCell hstc
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hst')
    have h8 : 8 ≤ Prologue.warpIndex L g := by
      by_contra h8
      have hP' := (ht.soft_st hgl (by omega) hst').1 j' hj'
      rw [← hceq] at hP'
      unfold InP at hP'
      unfold InO at hO
      omega
    have hO' : InO st (tcDataCell32 L g a' j') := hceq ▸ hO
    have hcta : cell.cta = g / L.block := by rw [hceq]; rfl
    by_cases hle : pArr L X g st k + 1 ≤ pPolls L X i.1 st i.2
    · exact .inr (.inr (.inl (.inr (.inl (o_store_done ht ho hP hgl h8 hgw hst hst' hj' hO'
        hKm (by show i.1 / L.block = _; rw [← hcell, hcta])
        (by show _ ≤ pPolls L X i.1 st K; omega))))))
    · exact .inr (.inr (.inr (.inl (o_done_store ho hR hgl h8 hgw hst' hj' hO' hxm
        ⟨_, hc, hO⟩ (by rw [← hcell, hcta]) (by omega)))))

/-- **The accumulator source of a PV MMA**: the last MMA of its thread before it writing the cell,
or, for the first MMA of a tile writing the cell, the rescale store of the cell. -/
theorem pv_accSource (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hT : SourceFacts L X) (hP : PReadyHandoff L X) (hR : OReady L X) {i : EvId} {d : Nat} {s :
        OperandSpec} {mask : List Nat} {cell : Cell}
    {st : Nat} (hst : st < 2) (hi : X.MmaIssue i d s true mask) (hc : X.MmaCell i cell)
    (hO : InO st cell) :
    ∃ src, ReadSource L X .acc src i cell ∧ ((src.1 = i.1 ∧ src.2 < i.2 ∧ X.MmaCell src cell) ∨
      (src.1 < L.threads ∧ 8 ≤ Prologue.warpIndex L src.1 ∧ Prologue.warpIndex L src.1 < 12 ∧
          StoreCell L X src cell)) := by
  classical
  obtain ⟨k0, hk0, hc0, hcnt0⟩ := hT.pv_acc hi hc hO
  let Q : Nat → Prop := fun k => k < i.2 ∧ X.MmaCell (i.1, k) cell
  have hQ : Q (Nat.findGreatest Q i.2) := Nat.findGreatest_spec (m := k0) hk0.le ⟨hk0, hc0⟩
  have hmax : ∀ k, Q k → k ≤ Nat.findGreatest Q i.2 := fun k hk => Nat.le_findGreatest hk.1.le hk
  set K := Nat.findGreatest Q i.2
  obtain ⟨hK, hcK⟩ := hQ
  obtain ⟨dK, sK, aK, mK, -, -, hiK, -⟩ := id hcK
  have hm1 := pPolls_mono (L := L) (X := X) (g := i.1) (st := st) (hmax k0 ⟨hk0, hc0⟩)
  have hm2 := pPolls_mono (L := L) (X := X) (g := i.1) (st := st) hK.le
  have hxm : IsMma X i := ⟨_, _, _, _, hi⟩
  have hKm : IsMma X (i.1, K) := ⟨_, _, _, _, hiK⟩
  have hcell : cell.cta = i.1 / L.block := (mma_o ht hi hc hO cell hc).2
  have hthr_of : ∀ x : EvId, IsMma X x → X.MmaCell x cell → x.1 = i.1 := by
    intro x hx hcx
    obtain ⟨d', s', acc', mask', hx'⟩ := hx
    have hco := (mma_o ht hx' hcx hO cell hcx).2
    exact ht.tc_one ⟨_, _, _, _, hx'⟩ (.inl hxm) (by rw [← hco, ← hcell])
  -- a store of the accumulator is a correction thread's
  have hcorr : ∀ {g k a j : Nat} {vals : List Value}, X.TSt (g, k) a vals .s32x32b →
    j < vals.length →
      tcDataCell32 L g a j = cell → g < L.threads ∧ 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex
          L g < 12 := by
    intro g k a j vals hs hj hceq
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hs)
    refine ⟨hgl, ?_, hgw⟩
    by_contra h8
    have hP' := (ht.soft_st hgl (by omega) hs).1 j hj
    rw [hceq] at hP'
    unfold InP at hP'
    unfold InO at hO
    omega
  by_cases htile : pPolls L X i.1 st K = pPolls L X i.1 st i.2
  · -- the last MMA writing the cell is of `i`'s tile
    exact ⟨(i.1, K), pv_accSource_tile ht ho hP hR hT hst hi hc hO hK hcK htile hmax,
      .inl ⟨rfl, hK, hcK⟩⟩
  · -- `i` is the first MMA of its tile writing the cell
    have hb1 : pPolls L X i.1 st K + 1 = pPolls L X i.1 st i.2 := by omega
    have hfirst : ∀ x, IsMma X x → X.MmaCell x cell →
        pPolls L X i.1 st K + 1 ≤ pPolls L X x.1 st x.2 → x = i ∨ i.2 < x.2 := by
      intro x hx hcx hle
      have hx1 := hthr_of x hx hcx
      rcases Nat.lt_trichotomy x.2 i.2 with h | h | h
      · exfalso
        have hq := hmax x.2 ⟨h, by rw [← hx1]; exact hcx⟩
        have := pPolls_mono (L := L) (X := X) (g := i.1) (st := st) hq
        rw [hx1] at hle
        omega
      · exact .inl (Prod.ext hx1 h)
      · exact .inr h
    by_cases hex : ∃ g k a j, ∃ vals : List Value, X.TSt (g, k) a vals .s32x32b ∧ j < vals.length ∧
        tcDataCell32 L g a j = cell ∧ pArr L X g st k = pPolls L X i.1 st K
    · -- the rescale store of the cell
      obtain ⟨g, k, a, j, vals, hs, hj, hceq, hpa⟩ := hex
      obtain ⟨hgl, h8, hgw⟩ := hcorr hs hj hceq
      subst hceq
      have hsrc := o_accSource_store hpre ht ho hP hR hgl h8 hgw hs hj hO hxm hc
        (by omega) (fun x hx hcx hle => hfirst x hx hcx (by rw [← hpa]; exact hle))
        (sourceLive hT.live hxm (.inl hc))
      exact ⟨(g, k), hsrc, .inr ⟨hgl, h8, hgw, storeCell32 hs hj⟩⟩
    · -- no rescale of the cell: the last MMA of the tile before
      have hlast : ∀ x, IsMma X x → X.MmaCell x cell →
          pPolls L X x.1 st x.2 ≤ pPolls L X (i.1, K).1 st (i.1, K).2 →
          x = (i.1, K) ∨ x.2 < (i.1, K).2 := by
        intro x hx hcx hle
        have hx1 := hthr_of x hx hcx
        simp only at hle ⊢
        rcases Nat.lt_trichotomy x.2 K with h | h | h
        · exact .inr h
        · exact .inl (Prod.ext hx1 h)
        · exfalso
          by_cases hxi : x.2 < i.2
          · exact absurd (hmax x.2 ⟨hxi, by rw [← hx1]; exact hcx⟩) (by omega)
          · have := pPolls_mono (L := L) (X := X) (g := i.1) (st := st)
              (show i.2 ≤ x.2 by omega)
            rw [hx1] at hle
            omega
      have hsrc := o_accSource_skip ht ho hP hR hO hst hKm hcK hxm hc (by simp only; omega)
        hlast (fun x hx hcx hle => hfirst x hx hcx hle)
        (fun g k a j vals hs hj hceq hpa => hex ⟨g, k, a, j, vals, hs, hj, hceq, hpa⟩)
        (sourceLive hT.live hxm (.inl hc))
      exact ⟨(i.1, K), hsrc, .inl ⟨rfl, hK, hcK⟩⟩

/-- **The accumulator source of an accumulating MMA**: an earlier MMA of its thread writing the
cell, or a correction store of the cell. -/
theorem accSource (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hT : SourceFacts L X) (hS : SFullHandoff L X) (hP : PReadyHandoff L X)
    (h2 : P2Gate L X) (hR : OReady L X) {i : EvId} {d : Nat}
    {s : OperandSpec} {mask : List Nat} {cell : Cell} (hi : X.MmaIssue i d s true mask)
    (hc : X.MmaCell i cell) :
    ∃ src, ReadSource L X .acc src i cell ∧ ((src.1 = i.1 ∧ src.2 < i.2 ∧ X.MmaCell src cell) ∨
      (src.1 < L.threads ∧ 8 ≤ Prologue.warpIndex L src.1 ∧ Prologue.warpIndex L src.1 < 12 ∧
          StoreCell L X src cell)) := by
  obtain ⟨-, -, st, hst, h | h⟩ := ht.mma_cells hi
  · obtain ⟨k, hk, hck, hsrc⟩ := qk_accSource ht ho hT hS hP h2 hst hi hc (h cell hc).1
    exact ⟨_, hsrc, .inl ⟨rfl, hk, hck⟩⟩
  · exact pv_accSource hpre ht ho hT hP hR hst hi hc (h cell hc).1

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm

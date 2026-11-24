-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.S.HandoffDef
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.POrder

@[expose] public section

/-! # The orders through the S-full objects, and the sources of the score loads -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

/-- **SFull.observes.** A softmax poll of the S-full object with `u` earlier successful polls
observes the completion of every MMA of its pair issued before `u + 1` commits to the object. -/
theorem sfull_observes (ht : ScoreFacts L X) (hS : SFullHandoff L X) {h j pc p : Nat}
    {acq : Bool} {sc : MbarScope} (hh : h < L.threads) (hw : Prologue.warpIndex L h < 8)
    (hget : X.get (h, j) = some ⟨pc, .wait (sFull L (h / L.block) (Prologue.warpIndex L h / 4)) p
        true acq sc⟩)
    {i : EvId} (hi : IsMma X i) (hc : i.1 / L.block = h / L.block)
    (hu : sCommits L X i.1 (Prologue.warpIndex L h / 4) i.2 ≤ sPolls L X h (Prologue.warpIndex L h
        / 4) j) :
    ∃ ws, AsyncCopy.AsyncObserved X i .mmaDone (h, j) true ws ∧
      ScopesMeet L .cluster i.1 ws h := by
  obtain ⟨x, s, rank, ws, hcom, hcx, hmbar, hcnt, htgt, hrank, hobs, hsc⟩ := hS hh hw hget
  have hthr : i.1 = x.1 := ht.tc_one hi (.inr ⟨s, hcom⟩) (hc.trans hcx.symm)
  obtain ⟨pcx, hx⟩ := hcom
  have hlt : i.2 < x.2 := by
    obtain ⟨_, _, _, _, _, hip⟩ := isMma_get hi
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · have h1 := countP_take_succ (p := commitsTo (sFull L (x.1 / L.block) (Prologue.warpIndex L h
        / 4)))
        hx (by simp [commitsTo, hmbar])
      have h2 := countP_take_mono (commitsTo (sFull L (x.1 / L.block) (Prologue.warpIndex L h / 4)))
        (X.tr x.1) (show x.2 + 1 ≤ i.2 by omega)
      unfold sCommits at hcnt hu
      rw [hthr] at hu
      omega
    · have hxi : x = i := Prod.ext hthr.symm heq
      rw [hxi, hip] at hx
      cases hx
  refine ⟨ws, ⟨.async x (.tcNotify rank), sFull L (h / L.block) (Prologue.warpIndex L h / 4),
    ⟨x, s, rank, rfl, ⟨hthr, hlt, .inl hi, s, pcx, hx⟩, ⟨pcx, hx⟩, htgt, hrank⟩, hobs⟩, ?_⟩
  rw [hthr]
  exact hsc

/-- **An MMA before the commit of tile `u` is done before every softmax event after its poll of
tile `u`.** -/
theorem s_doneBefore (ht : ScoreFacts L X) (hS : SFullHandoff L X) {h f : Nat}
    (hh : h < L.threads) (hw : Prologue.warpIndex L h < 8) {i : EvId} (hi : IsMma X i)
    (hc : i.1 / L.block = h / L.block)
    (hu : sCommits L X i.1 (Prologue.warpIndex L h / 4) i.2 + 1 ≤ sPolls L X h (Prologue.warpIndex
        L h / 4) f)
    (hf : f < (X.tr h).length) : DoneBefore L X i (h, f) := by
  obtain ⟨j, pc, p, acq, sc, hjf, hget, hq⟩ :=
    MbarRing.UnitHandoff.exists_poll (m := sFull L (h / L.block) (Prologue.warpIndex L h / 4)) hu
  obtain ⟨ws, ho, hsc⟩ := sfull_observes ht hS hh hw hget hi hc (by unfold sPolls; omega)
  exact .inl ⟨(h, j), ws, ho, hsc, baseCausality_src hget rfl rfl hjf hf⟩

/-- **The last QK MMA of tile `u` writing a cell is written before a softmax load of tile `u`.** -/
theorem s_writeBefore (ht : ScoreFacts L X) (hS : SFullHandoff L X) {h i a : Nat}
    {vals : List Value} (hh : h < L.threads) (hw : Prologue.warpIndex L h < 8)
    (hld : X.TLd (h, i) a vals .s32x32b)
    {src : EvId} (hsrc : IsMma X src) (hc : src.1 / L.block = h / L.block)
    (hcnt : sCommits L X src.1 (Prologue.warpIndex L h / 4) src.2 + 1 = sPolls L X h
        (Prologue.warpIndex L h / 4) i) :
    WriteBefore L X src (h, i) :=
  WriteBefore.of_done (s_doneBefore ht hS hh hw hsrc hc (by omega) (tLd_lt hld))

/-- **SLoadSource: stability.** A softmax load of tile `u` reads, at each of its cells, the last
QK MMA of tile `u` writing the cell (`hlast`), stably. -/
theorem s_loadStable (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hP : PReadyHandoff L X) (h2 : P2Gate L X) {h i a j : Nat} {vals : List Value}
    (hh : h < L.threads) (hw : Prologue.warpIndex L h < 8) (hld : X.TLd (h, i) a vals .s32x32b)
    (hj : j < vals.length) {src : EvId} (hsrc : IsMma X src)
    (hsc : X.MmaCell src (tcDataCell32 L h a j))
    (hcnt : sCommits L X src.1 (Prologue.warpIndex L h / 4) src.2 + 1 = sPolls L X h
        (Prologue.warpIndex L h / 4) i)
    (hlast : ∀ x, IsMma X x → X.MmaCell x (tcDataCell32 L h a j) →
      sCommits L X x.1 (Prologue.warpIndex L h / 4) x.2 ≤ sCommits L X src.1 (Prologue.warpIndex L
          h / 4) src.2 →
      x = src ∨ x.2 < src.2) :
    ∀ other, TmemWrite L X other (tcDataCell32 L h a j) →
      other = src ∨ WriteBefore L X other src ∨ ReadBefore L X .ld (h, i) other := by
  obtain ⟨hcells, hwait, harr⟩ := ht.soft_ld hh hw hld
  have hS := hcells j hj
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  obtain ⟨d', s', acc', mask', hsi⟩ := hsrc
  have hcs : src.1 / L.block = h / L.block := by
    rw [← (mma_s ht hsi hsc hS hst _ hsc).2]
    rfl
  obtain ⟨pcl, hldget⟩ := hld
  intro other hwo
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d, s, acc, mask, -, -, hoi, -⟩ := id hm
    have hco : other.1 / L.block = h / L.block := by
      rw [← (mma_s ht hoi hm hS hst _ hm).2]
      rfl
    have hthr : other.1 = src.1 := ht.tc_one ⟨_, _, _, _, hoi⟩ (.inl ⟨_, _, _, _, hsi⟩)
      (by rw [hco, hcs])
    by_cases hle : sCommits L X other.1 (Prologue.warpIndex L h / 4) other.2 ≤
        sCommits L X src.1 (Prologue.warpIndex L h / 4) src.2
    · rcases hlast other ⟨_, _, _, _, hoi⟩ hm hle with rfl | hlt
      · exact .inl rfl
      · exact .inr (.inl (.inl (mma_writeBefore ht hoi hsi hthr hlt
          (ht.mma_acc hoi hsi hm hsc rfl hst (.inl ⟨hS, hS⟩)))))
    · have hq := (ht.qk_polls hst ⟨_, _, _, _, hoi⟩ hm hS).1
      obtain ⟨e, hne, heq, ev, hget, ha⟩ := gate_after ht hP hst (soft_prod hh hw) hldget
        (u := sPolls L X h (Prologue.warpIndex L h / 4) i - 1) (by omega) ⟨_, _, _, _, hoi⟩ hco
        (by omega)
      obtain ⟨w, pcw, hiw, hwe, hwget⟩ := hwait e ev hne.1 hget ha
      refine .inr (.inr (ReadBefore.of_waitLd (w := (h, w)) hwget rfl hiw (.inl ?_)))
      refine overwrite_gate ht hP hst (soft_prod hh hw)
        (u := sPolls L X h (Prologue.warpIndex L h / 4) i - 1) ?_ ⟨_, _, _, _, hoi⟩ hco (by omega)
      rw [← heq]
      exact countP_take_mono _ _ hwe.le
  · obtain ⟨a', vals', j', hst', hj', hceq⟩ := ht.storeCell hstc
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hst')
    by_cases hc8 : 8 ≤ Prologue.warpIndex L other.1
    · obtain ⟨st', hst'2, hO, -⟩ := ho.corr_st hgl hc8 hgw hst'
      have := hO j' hj'
      rw [← hceq] at this
      unfold InO at this
      unfold InS at hS
      omega
    have hw' : Prologue.warpIndex L other.1 < 8 := by omega
    have hP' := (ht.soft_st hgl hw' hst').1 j' hj'
    rw [← hceq] at hP'
    have hsteq : Prologue.warpIndex L h / 4 = Prologue.warpIndex L other.1 / 4 := by
      unfold InP at hP'
      unfold InS at hS
      omega
    have hthr : h = other.1 := soft_cell_thread hpre hsteq hceq
    obtain ⟨g, k⟩ := other
    simp only at hthr
    subst hthr
    obtain ⟨pcs, hsget⟩ := hst'
    rcases Nat.lt_trichotomy k i with hlt | rfl | hlt
    · have hle := countP_take_mono (okPoll (sFull L (h / L.block) (Prologue.warpIndex L h / 4)))
        (X.tr h)
        hlt.le
      have hne : sPolls L X h (Prologue.warpIndex L h / 4) k ≠ sPolls L X h (Prologue.warpIndex L h
          / 4) i := fun he =>
        absurd (ht.soft_ld_st hh hw ⟨pcl, hldget⟩ ⟨pcs, hsget⟩ he.symm) (by omega)
      have hq := ht.qk_polls hst ⟨_, _, _, _, hsi⟩ hsc hS
      have hcnt' := hcnt
      unfold sPolls okPolls at hne hcnt'
      refine .inr (.inl (.inr (.inl (store_done ht hP h2 hh hw ⟨pcs, hsget⟩
        ⟨_, _, _, _, hsi⟩ hcs ?_ fun _ => ?_))))
      · unfold sPolls okPolls
        omega
      · unfold sPolls okPolls
        omega
    · rw [hldget] at hsget
      cases hsget
    · exact .inr (.inr (.inr ⟨⟨⟨hh, hh, rfl⟩, rfl⟩,
        .inl (baseCausality_tc hldget rfl hlt (len_of_get hsget)), ⟨a, vals, _, pcl, hldget⟩,
        a', vals', _, pcs, hsget⟩))

/-- **SLoadSource.** A softmax load of tile `u` reads, at each of its cells, the last QK MMA of
tile `u` writing the cell, given that the allocation keeps it live. -/
theorem s_readSource (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (hP : PReadyHandoff L X) (h2 : P2Gate L X) (hS : SFullHandoff L X) {h i a j : Nat}
    {vals : List Value} (hh : h < L.threads) (hw : Prologue.warpIndex L h < 8)
    (hld : X.TLd (h, i) a vals .s32x32b)
    (hj : j < vals.length) {src : EvId} (hsrc : IsMma X src)
    (hsc : X.MmaCell src (tcDataCell32 L h a j))
    (hcnt : sCommits L X src.1 (Prologue.warpIndex L h / 4) src.2 + 1 = sPolls L X h
        (Prologue.warpIndex L h / 4) i)
    (hlast : ∀ x, IsMma X x → X.MmaCell x (tcDataCell32 L h a j) →
      sCommits L X x.1 (Prologue.warpIndex L h / 4) x.2 ≤ sCommits L X src.1 (Prologue.warpIndex L
          h / 4) src.2 →
      x = src ∨ x.2 < src.2)
    (hlive : SourceLive L X src (h, i) (tcDataCell32 L h a j)) :
    ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) := by
  have hS' := (ht.soft_ld hh hw hld).1 j hj
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  obtain ⟨d, s, acc, mask, hsi⟩ := hsrc
  have hc : src.1 / L.block = h / L.block := by
    rw [← (mma_s ht hsi hsc hS' hst _ hsc).2]
    rfl
  have hne : src ≠ (h, i) := by
    rintro rfl
    obtain ⟨pc, hp⟩ := hsi
    obtain ⟨pc', hp'⟩ := hld
    rw [hp] at hp'
    cases hp'
  exact ⟨hne, .inl hsc, s_writeBefore ht hS hh hw hld ⟨_, _, _, _, hsi⟩ hc hcnt,
    s_loadStable hpre ht ho hP h2 hh hw hld hj ⟨_, _, _, _, hsi⟩ hsc hcnt hlast, hlive⟩


end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm

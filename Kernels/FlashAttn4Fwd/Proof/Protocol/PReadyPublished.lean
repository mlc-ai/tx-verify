-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreHandoff

@[expose] public section

/-! # P is published to the PV MMAs

A PV MMA of stage `st` and tile `u` (`pPolls = u + 1`) reads its A operand from Tensor Memory, from
the stage's probabilities `P` (`InP st`), which the softmax thread of each row stores in tile `u`.
**PPublished** (`p_aRead`, `p_aReadSource`): the softmax store of tile `u` of the cell is the A
operand's source (Core `ReadSource .a`, EXT-TCFIG):

* it is done before the MMA (`Score.store_done`: its `wait::st`, the arrival on the P-ready
  object, or the warp's elected arrival on the second object for columns `112 …`, and the MMA
  thread's poll of phase `u`);
* every other write of the cell is ordered: a QK MMA of a tile `u' ≤ u` is done before the store
  (the softmax's poll of tile `u` observes the commit of tile `u`, `s_doneBefore`); a QK MMA of a
  later tile is pipelined after the PV MMA (one thread, A in Tensor Memory, the A-read → D-write
  row of §9.7.18.6.2); a store of the thread in an earlier tile is pipelined before it (st→st), one
  in a later tile follows the PV MMA's completion (the commit of tile `u + 1` tracks it); the thread
  stores each cell once per tile. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

variable (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : PReadyHandoff L X)
    (h2 : P2Gate L X) (hS : SFullHandoff L X) {mma : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cellO : Cell} {st : Nat} (hmi : X.MmaIssue mma d s acc mask)
    (hmo : X.MmaCell mma cellO) (hO : InO st cellO) {index pos h i a j : Nat} {vals : List Value}
    (ha : aCell s index = some (tcDataCell32 L h a j, pos)) (hh : h < L.threads)
    (hw : warpOf L h < 8) (hs : X.TSt (h, i) a vals .s32x32b) (hj : j < vals.length)
    (htile : sPolls L X h (warpOf L h / 4) i = pPolls L X mma.1 (warpOf L h / 4) mma.2)
include hpre ht ho hP h2 hS hmi hmo hO ha hh hw hs hj htile

/-- **PPublished: order.** The softmax store of tile `u` of a cell the PV MMA of tile `u` reads is
written before the MMA, and every other write of the cell is ordered with the read. -/
theorem p_aRead :
    WriteBefore L X (h, i) mma ∧ ∀ other, TmemWrite L X other (tcDataCell32 L h a j) →
      other = (h, i) ∨ other = mma ∨ WriteBefore L X other (h, i) ∨ DoneBefore L X mma other ∨
        Pipelined L X .aRead mma .dWrite other ∨ Pipelined L X .aRead mma .cpWrite other := by
  obtain ⟨hP1, hcom, haT, hA⟩ := ht.pv_polls hmi hmo hO
  obtain ⟨hPc, hcta, hhi⟩ := hA index _ pos ha
  obtain ⟨hcells, hlh, hs1, -⟩ := ht.soft_st hh hw hs
  have hPj := hcells j hj
  have hsteq : st = warpOf L h / 4 := by
    unfold InP at hPc hPj
    omega
  subst hsteq
  have hst : warpOf L h / 4 < 2 := by omega
  have hS' : InS (warpOf L h / 4) (tcDataCell32 L h a j) := by
    unfold InP at hPc
    exact ⟨by omega, hPc.2⟩
  have hcm : ctaOf L mma.1 = leadCta (ctaOf L h) := hcta.symm
  have hlm := (mma_in ht ⟨_, _, _, _, hmi⟩).2
  refine ⟨.inr (.inl (store_done ht hP h2 hh hw hs ⟨_, _, _, _, hmi⟩ hcm (by omega)
    fun hall => by rw [htile, hhi (hall j hj)])), fun other hwo => ?_⟩
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d', s', acc', mask', -, -, hoi, -⟩ := id hm
    have hco : ctaOf L other.1 = leadCta (ctaOf L h) := by
      rw [← (mma_s ht hoi hm hS' hst _ hm).2]
      rfl
    have hthr : mma.1 = other.1 := ht.tc_one ⟨_, _, _, _, hmi⟩ (.inl ⟨_, _, _, _, hoi⟩)
      (by rw [hlm, (mma_in ht ⟨_, _, _, _, hoi⟩).2, hco, hcm])
    by_cases hle : sCommits L X other.1 (warpOf L h / 4) other.2 + 1 ≤
        sPolls L X h (warpOf L h / 4) i
    · exact .inr (.inr (.inl (.inl (.inl (s_doneBefore ht hS hh hw ⟨_, _, _, _, hoi⟩
        (by rw [hco, leadCta_idem]) hle (TSt.lt hs))))))
    · have hlt := ht.pv_qk ⟨_, _, _, _, hmi⟩ ⟨_, _, _, _, hoi⟩ hthr hmo hO hm hS' (by omega)
      have hgl := (ht.mma_cells hmi).1
      exact .inr (.inr (.inr (.inr (.inl ⟨⟨⟨hgl, hthr ▸ hgl, by rw [hthr]⟩, by rw [hthr]⟩,
        .inl (IsMma.baseCausality ⟨_, _, _, _, hmi⟩ hthr hlt (IsMma.lt ⟨_, _, _, _, hoi⟩)),
        ⟨d, s, acc, mask, hmi, haT⟩, d', s', acc', mask', hoi⟩))))
  · obtain ⟨a', vals', j', hst', hj', hceq⟩ := ht.storeCell hstc
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hst')
    by_cases hc8 : 8 ≤ warpOf L other.1
    · obtain ⟨st', hst'2, hOc, -⟩ := ho.corr_st hgl hc8 hgw hst'
      have := hOc j' hj'
      rw [← hceq] at this
      unfold InO at this
      unfold InP at hPj
      omega
    have hw' : warpOf L other.1 < 8 := by omega
    have hP' := (ht.soft_st hgl hw' hst').1 j' hj'
    rw [← hceq] at hP'
    have hsteq : warpOf L h / 4 = warpOf L other.1 / 4 := by
      unfold InP at hP' hPj
      omega
    have hthr : h = other.1 := soft_cell_thread hpre hsteq hceq
    obtain ⟨g, k⟩ := other
    simp only at hthr
    subst hthr
    rcases Nat.lt_trichotomy (sPolls L X h (warpOf L h / 4) k)
      (sPolls L X h (warpOf L h / 4) i) with hlt | heq | hgt
    · have hki : k < i := lt_of_count_lt hlt
      obtain ⟨pck, hkget⟩ := hst'
      exact .inr (.inr (.inl (.inr (.inl ⟨⟨a', vals', _, pck, hkget⟩, .inr (.inr
        ⟨⟨⟨hh, hh, rfl⟩, rfl⟩, .inl (baseCausality_tc hkget rfl hki (TSt.lt hs)),
          ⟨a', vals', _, pck, hkget⟩, a, vals, _, hs⟩)⟩))))
    · exact .inl (by rw [ht.soft_st_one hh hw hst' hs hj' hj hceq.symm heq])
    · have hlk := TSt.lt hst'
      exact .inr (.inr (.inr (.inl (s_doneBefore ht hS hh hw ⟨_, _, _, _, hmi⟩
        (by rw [hlm, hcm]) (by omega) hlk))))

/-- **PPublished.** The softmax store of tile `u` is the read source of the A-operand byte of the
PV MMA of tile `u` at its cell (`ReadSource .a`), given that the store is live at the MMA. -/
theorem p_aReadSource (hlive : SourceLive L X (h, i) mma (tcDataCell32 L h a j)) :
    ReadSource L X .a (h, i) mma (tcDataCell32 L h a j) := by
  obtain ⟨hwb, hother⟩ := p_aRead hpre ht ho hP h2 hS hmi hmo hO ha hh hw hs hj htile
  have hne : (h, i) ≠ mma := by
    intro heq
    have h12 := (ht.mma_cells hmi).2.1
    rw [← heq] at h12
    simp only at h12
    omega
  refine readSource_a.mpr ⟨hne, .inr (.inl ⟨a, vals, .s32x32b, j, hs, hj, ?_⟩), hwb,
    fun other hwo => ?_, hlive⟩
  · exact (tcDataCell_s32x32b _ _ _ _).symm
  rcases hother other hwo with h1 | h1 | h1 | h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inr (.inl h1))
  · exact .inr (.inl h1)
  · exact .inr (.inr (.inr (.inl h1)))
  · exact .inr (.inr (.inr (.inr (.inl h1))))
  · exact .inr (.inr (.inr (.inr (.inr h1))))

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof

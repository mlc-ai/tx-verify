-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceDef
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.ScoreDone

@[expose] public section

/-! # The sources of the PV MMAs' A operands

A PV MMA of a stage and a tile `u` reads an A byte from a cell that the softmax lane of the cell's
row stores in tile `u` (`pvAStore`): below column `112` before its P-full arrival of the tile, which
the MMA lane's poll observes, and from column `112` before its warp barrier of the tile, which the
elected lane's arrival on the second P-full barrier follows. The store is the byte's read source
(`p_aReadSource`). -/
namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

section
variable (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X) (hP : PReadyHandoff L X)
    (h2 : P2Gate L X) (hS : SFullHandoff L X) {mma : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {cellO : Cell} {st : Nat} (hmi : X.MmaIssue mma d s acc mask)
    (hmo : X.MmaCell mma cellO) (hO : InO st cellO) {index pos h i a j : Nat} {vals : List Value}
    (ha : aCell s index = some (tcDataCell32 L h a j, pos)) (hh : h < L.threads)
    (hw : Prologue.warpIndex L h < 8) (hs : X.TSt (h, i) a vals .s32x32b) (hj : j < vals.length)
    (htile : sPolls L X h (Prologue.warpIndex L h / 4) i = pPolls L X mma.1 (Prologue.warpIndex L h
        / 4) mma.2)
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
  have hsteq : st = Prologue.warpIndex L h / 4 := by
    unfold InP at hPc hPj
    omega
  subst hsteq
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  have hS' : InS (Prologue.warpIndex L h / 4) (tcDataCell32 L h a j) := by
    unfold InP at hPc
    exact ⟨by omega, hPc.2⟩
  have hcm : mma.1 / L.block = h / L.block := hcta.symm
  refine ⟨.inr (.inl (store_done ht hP h2 hh hw hs ⟨_, _, _, _, hmi⟩ hcm (by omega)
    fun hall => by rw [htile, hhi (hall j hj)])), fun other hwo => ?_⟩
  rcases tmemWrite_of_no_copy ht.no_cp ht.no_shift hwo with hm | hstc
  · obtain ⟨d', s', acc', mask', -, -, hoi, -⟩ := id hm
    have hco : other.1 / L.block = h / L.block := by
      rw [← (mma_s ht hoi hm hS' hst _ hm).2]
      rfl
    have hthr : mma.1 = other.1 := ht.tc_one ⟨_, _, _, _, hmi⟩ (.inl ⟨_, _, _, _, hoi⟩)
      (by rw [hco, hcm])
    by_cases hle : sCommits L X other.1 (Prologue.warpIndex L h / 4) other.2 + 1 ≤
        sPolls L X h (Prologue.warpIndex L h / 4) i
    · exact .inr (.inr (.inl (.inl (.inl (s_doneBefore ht hS hh hw ⟨_, _, _, _, hoi⟩
        (by rw [hco]) hle (tSt_lt hs))))))
    · have hlt := ht.pv_qk hst ⟨_, _, _, _, hmi⟩ ⟨_, _, _, _, hoi⟩ hthr hmo hO hm hS' (by omega)
      have hgl := (ht.mma_cells hmi).1
      exact .inr (.inr (.inr (.inr (.inl ⟨⟨⟨hgl, hthr ▸ hgl, by rw [hthr]⟩, by rw [hthr]⟩,
        .inl (isMma_baseCausality ⟨_, _, _, _, hmi⟩ hthr hlt (isMma_lt ⟨_, _, _, _, hoi⟩)),
        ⟨d, s, acc, mask, hmi, haT⟩, d', s', acc', mask', hoi⟩))))
  · obtain ⟨a', vals', j', hst', hj', hceq⟩ := ht.storeCell hstc
    obtain ⟨hgl, hgw⟩ := ht.tc_role (.inr hst')
    by_cases hc8 : 8 ≤ Prologue.warpIndex L other.1
    · obtain ⟨st', hst'2, hOc, -⟩ := ho.corr_st hgl hc8 hgw hst'
      have := hOc j' hj'
      rw [← hceq] at this
      unfold InO at this
      unfold InP at hPj
      omega
    have hw' : Prologue.warpIndex L other.1 < 8 := by omega
    have hP' := (ht.soft_st hgl hw' hst').1 j' hj'
    rw [← hceq] at hP'
    have hsteq : Prologue.warpIndex L h / 4 = Prologue.warpIndex L other.1 / 4 := by
      unfold InP at hP' hPj
      omega
    have hthr : h = other.1 := soft_cell_thread hpre hsteq hceq
    obtain ⟨g, k⟩ := other
    simp only at hthr
    subst hthr
    rcases Nat.lt_trichotomy (sPolls L X h (Prologue.warpIndex L h / 4) k)
      (sPolls L X h (Prologue.warpIndex L h / 4) i) with hlt | heq | hgt
    · have hki : k < i := lt_of_count_lt hlt
      obtain ⟨pck, hkget⟩ := hst'
      exact .inr (.inr (.inl (.inr (.inl ⟨⟨a', vals', _, pck, hkget⟩, .inr (.inr
        ⟨⟨⟨hh, hh, rfl⟩, rfl⟩, .inl (baseCausality_tc hkget rfl hki (tSt_lt hs)),
          ⟨a', vals', _, pck, hkget⟩, a, vals, _, hs⟩)⟩))))
    · exact .inl (by rw [ht.soft_st_one hh hw hst' hs hj' hj hceq.symm heq])
    · have hlk := tSt_lt hst'
      exact .inr (.inr (.inr (.inl (s_doneBefore ht hS hh hw ⟨_, _, _, _, hmi⟩
        hcm (by omega) hlk))))

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

end

/-- The softmax thread of stage `st` whose row holds cell `c`. -/
def cellThread (L : Launch) (st : Nat) (c : Cell) : Nat := c.cta * L.block + 128 * st + c.lane

/-- The softmax thread of a cell of the first 128 lanes of a lane's CTA. -/
theorem cellThread_spec (hpre : Pre P L mem0) {g st : Nat} {c : Cell} (hst : st < 2)
    (hl : c.lane < 128) (hg : g < L.threads) (hc : c.cta = g / L.block) :
    cellThread L st c < L.threads ∧ Prologue.warpIndex L (cellThread L st c) =
        4 * st + c.lane / 32 ∧
      cellThread L st c / L.block = c.cta ∧ tcDataCell32 L (cellThread L st c) 0 c.column = c := by
  have hb := hpre.block
  obtain ⟨cta, lane, col⟩ := c
  dsimp only at hl hc ⊢
  unfold cellThread Prologue.warpIndex
  unfold Launch.threads at hg ⊢
  simp only [tcDataCell32, laneBase, laneOf, Cell.mk.injEq]
  rw [hb] at hc hg ⊢
  have hlt : g / 512 < L.grid := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact hg
  have : (cta + 1) * 512 ≤ L.grid * 512 := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at this
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The store a PV MMA reads an A byte from**: the softmax lane of the cell's row stored the
cell in the MMA's tile. -/
theorem pvAStore (hpre : Pre P L mem0) (ht : ScoreFacts L X)
    (hT : SourceFacts L X) (hP : PReadyHandoff L X) {i : EvId} {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {index pos : Nat} {cell : Cell}
    (hi : X.MmaIssue i d s acc mask) (ha : aCell s index = some (cell, pos)) :
    ∃ cellO st, st < 2 ∧ X.MmaCell i cellO ∧ InO st cellO ∧
    ∃ h k a j, ∃ vals : List Value, h < L.threads ∧ Prologue.warpIndex L h < 8 ∧
      X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧ cell = tcDataCell32 L h a j ∧
      sPolls L X h (Prologue.warpIndex L h / 4) k =
        pPolls L X i.1 (Prologue.warpIndex L h / 4) i.2 := by
  obtain ⟨c0, hc0⟩ := ht.mma_cell hi
  obtain ⟨hgx, -, st, hst, hcs | hcs⟩ := ht.mma_cells hi
  · have hnone := ht.qk_smem hst hi hc0 (hcs c0 hc0).1
    simp [aCell, hnone] at ha
  obtain ⟨hO, -⟩ := hcs c0 hc0
  refine ⟨c0, st, hst, hc0, hO, ?_⟩
  obtain ⟨hP1, -, haT, hA⟩ := ht.pv_polls hi hc0 hO
  obtain ⟨hPc, hcta, hhigh⟩ := hA index cell pos ha
  have hlane := hT.a_lane hi ha
  obtain ⟨hhl, hhw, hhc, hcell⟩ := cellThread_spec hpre hst hlane hgx hcta
  set h := cellThread L st cell
  have hhw8 : Prologue.warpIndex L h < 8 := by omega
  have hhst : Prologue.warpIndex L h / 4 = st := by omega
  have hlh : h / L.block = i.1 / L.block := by rw [hhc, hcta]
  have hxm : IsMma X i := ⟨_, _, _, _, hi⟩
  have hin := mma_in ht hxm
  have hP' : InP (Prologue.warpIndex L h / 4) (tcDataCell32 L h 0 cell.column) := by
    rw [hcell, hhst]; exact hPc
  refine ⟨h, ?_⟩
  rw [hhst]
  obtain ⟨u, hu⟩ : ∃ u, pPolls L X i.1 st i.2 = u + 1 := ⟨pPolls L X i.1 st i.2 - 1, by omega⟩
  rw [hu]
  by_cases hH : InPHigh st cell
  · have hp2 := hhigh hH
    obtain ⟨b, m, inst, hbw, hbu⟩ := hT.elected hhl hhw8 hxm hlh.symm (u := u)
      (by rw [hhst]; omega)
    have hH' : InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h 0 cell.column) := by
      rw [hcell, hhst]; exact hH
    obtain ⟨k', a', j', vals', -, hst', hj', hceq, hsp⟩ := hT.soft_high hhw8 hbw hP' hH'
    rw [hhst, hbu] at hsp
    exact ⟨k', a', j', vals', hhl, hhw8, hst', hj', by rw [hceq, hcell], hsp⟩
  · obtain ⟨j, pc, p, acq, sc, -, hwj, hcnt⟩ := MbarRing.UnitHandoff.exists_poll
      (X := X) (m := pFull L (i.1 / L.block) st) (h := i.1) (f := i.2)
      (c := u) (by rw [← hu]; exact le_refl _)
    obtain ⟨e, he, hsy⟩ := hP (i.1 / L.block) st hst i.1 j pc p acq sc _ hin hwj hcnt h
      ⟨hhl, hlh, .inl ⟨hhw8, hhst⟩⟩
    obtain ⟨rs, ⟨tx, cnt, pce, hev⟩, -⟩ := id hsy
    have hev' : X.get (h, e) = some ⟨pce,
        .arrive (pFull L (h / L.block) (Prologue.warpIndex L h / 4)) tx cnt true rs⟩ := by
      rw [hlh, hhst]
      exact hev
    have hH' : ¬ InPHigh (Prologue.warpIndex L h / 4) (tcDataCell32 L h 0 cell.column) := by
      rw [hcell, hhst]; exact hH
    obtain ⟨k', a', j', vals', -, hst', hj', hceq, hsp⟩ := hT.soft_low hhw8 hev' hP' hH'
    refine ⟨k', a', j', vals', hhl, hhw8, hst', hj', by rw [hceq, hcell], ?_⟩
    rw [hhst] at hsp
    rw [hsp]
    unfold pArr
    rw [hlh, he]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm

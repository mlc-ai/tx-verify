-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdCommit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvCell
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkPrev
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StBlockLt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Block
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RldRst

@[expose] public section

/-! # An output load reads PV MMA `6 + p` of the last block

An output load of the epilogue (columns below `256`) is after the lane's poll of `svDone` at pc
1184, which observes the MMA lane's last commit, the one of block `R - 1` (`svDone_last`), after
`24 R` MMA issues (`mma_svCommit`): the lane's PV MMA `6 + p` of that block (`p = column / 128`)
is done before the load (`done_after_svPoll`) and every MMA of the lane is before the commit
(`mma_asyncSv`), so none is later. A store of the arm is of a block below `R`, so done before
that MMA (`pvStore_blk`). The source of a load register is the latest write ordered before the
load: that MMA (`ld_pin_epi`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem pvPc_inj {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

private theorem ru_eq1 {x y : Nat} (h : ∀ b : Fin 2, ringUses 2 b.val x = ringUses 2 b.val y) :
    x = y := by
  have h0 := h 0
  have h1 := h 1
  unfold ringUses at h0 h1
  simp only [Fin.val_zero, Fin.val_one] at h0 h1
  omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **The pin of an output load**: the source of a register of an epilogue load of a column
below `256` is the lane's PV MMA `6 + p` of the last block `R - 1`, done. -/
theorem ld_pin_epi (hG : SyncGuarded L kernel X)
    {h k a j jw p0 pc : Nat} {vals : List Value} {sh : TcShape} {src : EvId}
    {cell : TcMma.Cell}
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (ha : a ≤ 192)
    (hj : j < vals.length) (hcell : cell = tcDataCell L h sh a j) (hjw : jw < k)
    (hpoll : X.get (h, jw) = some ⟨1184, .wait (mbarLoc L (h / L.block)
      (.svDone (slot2 (blocksOf P L (h / L.block) - 1)))) p0 true true .cta⟩)
    (hs : TcMma.ReadSource L X .ld src (h, k) cell) :
    ∃ i sx mask, src = (mmaLane L X (h / L.block), i) ∧
      X.get src = some ⟨TmemRow.pvPc (6 + cell.column / 128), .tc (.mma (128 * (cell.column / 128))
        sx true mask)⟩ ∧
      mmaIssues ((X.tr (mmaLane L X (h / L.block))).take i) =
        24 * (blocksOf P L (h / L.block) - 1) + 16 + (6 + cell.column / 128) ∧
      X.async.mmaDone src = true ∧ X.MmaCell src cell := by
  obtain ⟨hat', hsh, ha', -⟩ := ld_class hp hX hFw he
  subst hsh
  have hT := tmem_rows hp hX hFw
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat'.1 ha' (j := j)
  rw [← hcell] at hcta hlane hcol
  have hlen := ldLen hp hX he rfl
  have hcol256 : cell.column < 256 := by omega
  have hl128 : cell.lane < 128 := by
    have hw4 := hat'.1
    unfold MbarRow.warp at hw4
    rw [tidOf_x_eq hp h] at hw4
    omega
  have hkl : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hsl, ic, pci, spi, rank, hgc, hmi, -, hcnt, -, -⟩ :=
    svDone_last hp hX hFw hR hI hB hN hat'.1 hpoll
  obtain ⟨hcy, r, hrR, hsr, hall, hiss⟩ := mma_svCommit hp hX hFw hgc hmi
  have hrl : r = blocksOf P L (h / L.block) - 1 := by
    have h1 := hall (slot2 (blocksOf P L (h / L.block) - 1))
    rw [hcnt] at h1
    have h2 := congrArg Fin.val hsr
    simp only [slot2, ringUses] at h1 h2
    omega
  obtain ⟨p, hpe, hp2⟩ : ∃ p, p = cell.column / 128 ∧ p < 2 := ⟨_, rfl, by omega⟩
  -- PV MMA `6 + p` of the last block
  obtain ⟨xM, hxi, pcx, dcx, sx, accx, maskx, hM0, hpx1, hpx2, hxc⟩ :=
    mma_with_count (X := X) (g := mmaLane L X (h / L.block)) (i := ic)
      (c := 24 * r + 22 + p) (by omega)
  obtain ⟨r', k', hk', hiss', hcases⟩ := mma_slot_pc hp hX hFw hM0 ⟨by omega, by omega⟩
  obtain ⟨hkk, hpcM, hdM⟩ : k' = 22 + p ∧ TmemRow.pvPc (6 + p) = pcx ∧ dcx = 128 * p := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, h2, h3, h4⟩
    · omega
    · refine ⟨by omega, ?_, ?_⟩
      · rw [← h3]; congr 1; omega
      · rw [h4]; omega
  subst hpcM hdM
  have hM : X.get (mmaLane L X (h / L.block), xM) =
      some ⟨TmemRow.pvPc (6 + p), .tc (.mma (128 * p) sx accx maskx)⟩ := hM0
  obtain ⟨kM0, hkM0, hpcM0, hdM0, -, honM, hopsM⟩ := pv_pc hT hX hM (by omega)
  obtain ⟨dM, kM, -, hpcMA, -, hissM, haccM, -, -, -, hplM, -⟩ :=
    mma_pvAt hp hX hFw hM honM.1 (by omega)
  have hkM : 6 + p = kM := pvPc_inj hpcMA
  subst hkM
  have haccx : accx = true := haccM.mpr (.inl (by omega))
  subst haccx
  have hdM1 : dM = r := by omega
  have hdoneM : TcMma.DoneBefore L X (mmaLane L X (h / L.block), xM) (h, k) :=
    done_after_svPoll hp hX hFw hR hI hB hN hM (.inl ⟨128 * p, sx, true, maskx, rfl⟩) hcy
      hat'.1 hpoll hjw hkl
  have hMw : TcMma.TmemWrite L X (mmaLane L X (h / L.block), xM) cell :=
    pv_write_of hp hX hFw hp2 hM (hcta.trans hcy) hl128 (by omega) (by omega)
  have hsk := ld_src_kind hp hX hFw ⟨_, he⟩ hj hcell hs
  obtain ⟨-, hsw, hWB, hlat, -⟩ := TcMma.readSource_ld.mp hs
  obtain ⟨gs, is⟩ := src
  obtain ⟨hcw, hcls⟩ := writer_cases hp hX hT hsw
  have hxc2 : gs / L.block = h / L.block := hcw.symm.trans hcta
  have hpR : 1853 ≤ TmemRow.pvPc (6 + p) ∧ TmemRow.pvPc (6 + p) ≤ 2160 := by
    simp only [TmemRow.pvPc]
    split <;> omega
  rcases hcls with ⟨k1, -, h1, -⟩ | ⟨b2, ⟨pc2, s2, a2, he2, hon2, hops2⟩, hb2, hb2m, h2l, h2h⟩ |
    ⟨k1, -, h1, -⟩ | ⟨⟨pcy, ay, vy, hy, hwy⟩, hy1, hy2⟩
  · omega
  · -- the source is a PV MMA of the lane
    have hb2eq : b2 = 128 * p := by omega
    subst hb2eq
    obtain ⟨hg, hm, hdone⟩ := ld_pv_src hp hX hFw hsk he2 hon2 hxc2
    subst hg
    obtain ⟨d2, kk2, hkk8, hpc2, hbb2, hiss2, -, -, -, -, -, -⟩ :=
      mma_pvAt hp hX hFw he2 hon2.1 (by omega)
    have hr2 : 1853 ≤ pc2 ∧ pc2 ≤ 2160 := by
      rw [hpc2]
      simp only [TmemRow.pvPc]
      split <;> omega
    have hr3 : 1853 < pc2 := by
      rw [hpc2]
      simp only [TmemRow.pvPc]
      split <;> omega
    have hlt_ic : is < ic := by
      by_contra hge
      have hge' : ic ≤ is := Nat.le_of_not_lt hge
      have hcs := mma_asyncSv hp hX hFw he2 hon2.1 hr3 (Or.inl ⟨_, _, _, _, rfl⟩)
      rw [← hcy] at hcs
      rcases Nat.eq_or_lt_of_le hge' with heq | hlt'
      · subst heq
        rw [he2] at hgc
        cases hgc
      · have h1 := countP_take_succ (p := PTX.Flow.commitsTo (mbarLoc L (h / L.block)
          (.svDone (slot2 (blocksOf P L (h / L.block) - 1))))) hgc
          (by simp [PTX.Flow.commitsTo, hmi])
        have h2 := countP_take_mono (PTX.Flow.commitsTo (mbarLoc L (h / L.block)
          (.svDone (slot2 (blocksOf P L (h / L.block) - 1)))))
          (X.tr (mmaLane L X (h / L.block))) (show ic + 1 ≤ is by omega)
        omega
    have hij : is = xM := by
      rcases Nat.lt_trichotomy is xM with hlt | heq | hgt
      · exfalso
        have hB1 := pv_writeBefore hp hX hT he2 hM hp2 hlt
        rcases hlat _ hMw with h1 | h1 | h1 | ⟨-, -, -, a2', v2', s2', pc2', hst⟩
        · exact absurd (congrArg Prod.snd h1) (by simp only; omega)
        · exact TcMma.tcStep_asymm hX hG hB1.tcStep h1.tcStep
        · exact TcMma.tcStep_asymm hX hG hdoneM.tcStep h1.tcStep
        · cases get_tc_inj hM hst
      · exact heq
      · exfalso
        have hlt4 := mmaIssues_lt hM hpR hgt
        have hlt5 := mmaIssues_lt he2 hr2 hlt_ic
        omega
    subst hij
    exact ⟨is, sx, maskx, rfl, by rw [← hpe]; exact hM, by rw [hxc, hrl, hpe]; omega, hdone, hm⟩
  · omega
  · -- the source is a rescale store: of a block below `R`, so before PV MMA `6 + p`
    exfalso
    obtain ⟨c', hpc', hay, -, hvl⟩ := wg0_rst_addr hp hX hFw hwy hy
    have hcxy : (mmaLane L X (h / L.block), xM).1 / L.block = (gs, is).1 / L.block :=
      hcy.symm.trans hxc2.symm
    obtain ⟨dA, rA, hpA, hqA, hA⟩ := pvStore_blk hp hX hFw hR hI hB hT hM (by omega) hy hcxy
    have hat3 : MbarRow.Wg0At L gs pcy := by
      have hr4 : 103 ≤ pcy ∧ pcy < 1842 := by
        rw [hpc']; fin_cases c' <;> decide
      exact ⟨hwy, hr4.1, hr4.2⟩
    obtain ⟨r2, hr2lt, hr2⟩ := wg0_stBlock_lt hp hX hFw hy hat3
    rw [hxc2] at hr2lt
    have hdA : dA + 1 = dM + 1 := ru_eq1 fun b => by
      have := (hpA b).symm.trans (hplM b)
      simpa using this
    have hrA : rA + 1 = r2 + 1 := ru_eq1 fun b => by
      have := (hqA b).symm.trans (hr2 b).1
      simpa using this
    rcases hA with hA | hA
    · rcases hlat (mmaLane L X (h / L.block), xM) hMw with h1 | h1 | h1 |
        ⟨-, -, -, a2', v2', s2', pc2', hst⟩
      · obtain ⟨h21, h22⟩ := Prod.mk.inj h1
        rw [h21, h22] at hM
        rw [hM] at hy
        simp at hy
      · exact TcMma.tcStep_asymm hX hG h1.tcStep hA.2.tcStep
      · exact TcMma.tcStep_asymm hX hG hdoneM.tcStep h1.tcStep
      · cases get_tc_inj hM hst
    · omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

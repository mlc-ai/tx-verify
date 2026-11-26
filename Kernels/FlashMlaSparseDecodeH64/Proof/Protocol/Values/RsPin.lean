-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdCommit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvCell
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Block
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkPrev
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RldRst

@[expose] public section

/-! # A rescale load reads PV MMA `6 + p` of the previous block

A rescale load of warpgroup 0 at block `r ≥ 1` (columns below `256`, chunk `c`) has polled
`qkDone` for the commit of block `r` (`qk_commit_poll`), before which the MMA lane issued the PV
MMAs of block `r - 1`: its PV MMA `6 + p` (`p = column / 128`, the D column) is done before the
load (`ld_second`). The source of a load register is the latest write ordered before the load
(`ReadSource`): not an earlier PV MMA of that D column (`pv_writeBefore`), not a later one (its
polls of `soReady` make the load's wait precede it, `ld_first`), not a store of an earlier block
(done before the PV MMA by `pvStore_blk`) and not a store of block `r` or later (after the load of
its chunk, `wg0_rld_before_rst`, or of another chunk's cells). So it is that PV MMA
(`ld_pin_rs`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem ru_after {r t : Nat} (h : r < t) : r / 2 + 1 ≤ ringUses 2 (r % 2) t := by
  unfold ringUses; omega

private theorem ru_eq {x y : Nat} (h : ∀ b : Fin 2, ringUses 2 b.val x = ringUses 2 b.val y) :
    x = y := by
  have h0 := h 0
  have h1 := h 1
  unfold ringUses at h0 h1
  simp only [Fin.val_zero, Fin.val_one] at h0 h1
  omega

private theorem pvPc_inj {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **The pin of a rescale load**: the source of a register of a rescale load of block `r ≥ 1`
(chunk `c`) is the lane's PV MMA `6 + p` of block `r - 1`, `p` the D column of the cell, done. -/
theorem ld_pin_rs (hG : SyncGuarded L kernel X)
    {h k a j r : Nat} {c : Fin 4} {vals : List Value} {sh : TcShape} {src : EvId}
    {cell : TcMma.Cell}
    (he : X.get (h, k) = some ⟨[716, 817, 918, 1019].getD c.val 0, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length) (hcell : cell = tcDataCell L h sh a j) (h1r : 1 ≤ r)
    (hr : ∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take k) =
        ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady b))
        ((X.tr h).take k) = ringUses 2 b.val r)
    (hs : TcMma.ReadSource L X .ld src (h, k) cell) :
    ∃ i sx mask, src = (mmaLane L X (h / L.block), i) ∧
      X.get src = some ⟨TmemRow.pvPc (6 + cell.column / 128), .tc (.mma (128 * (cell.column / 128))
        sx true mask)⟩ ∧
      mmaIssues ((X.tr (mmaLane L X (h / L.block))).take i) =
        24 * (r - 1) + 16 + (6 + cell.column / 128) ∧
      X.async.mmaDone src = true ∧ X.MmaCell src cell := by
  obtain ⟨hat', hsh, ha', -⟩ := ld_class hp hX hFw he
  subst hsh
  obtain ⟨hca, -⟩ := wg0_rld_addr hp hX hFw hat'.1 he
  have hT := tmem_rows hp hX hFw
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat'.1 ha' (j := j)
  rw [← hcell] at hcta hlane hcol
  have hlen := ldLen hp hX he rfl
  have hc4 := c.isLt
  have hcol256 : cell.column < 256 := by omega
  have hl128 : cell.lane < 128 := by
    have hw4 := hat'.1
    unfold MbarRow.warp at hw4
    rw [tidOf_x_eq hp h] at hw4
    omega
  have hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r)))
      ((X.tr h).take k) := by
    rw [(hr (slot2 r)).1]
    simp only [slot2]
    unfold ringUses
    omega
  obtain ⟨ic, pcc, sp, hcom, hmb, hcnt, hrb, hn, -⟩ :=
    qk_commit_poll hp hX hFw hR hI hB hat'.1 hpol
  obtain ⟨hcy, -⟩ := mma_qkBlock hp hX hFw hcom hmb
  obtain ⟨p, hpe, hp2⟩ : ∃ p, p = cell.column / 128 ∧ p < 2 := ⟨_, rfl, by omega⟩
  -- PV MMA `6 + p` of block `r - 1`
  obtain ⟨xM, hxi, pcx, dcx, sx, accx, maskx, hM0, hpc1, hpc2, hxc⟩ :=
    mma_with_count (X := X) (g := mmaLane L X (h / L.block)) (i := ic)
      (c := 24 * (r - 1) + 22 + p) (by omega)
  obtain ⟨r', k', hk', hiss, hcases⟩ := mma_slot_pc hp hX hFw hM0 ⟨by omega, by omega⟩
  obtain ⟨hkk, hpcM, hdM⟩ : k' = 22 + p ∧ TmemRow.pvPc (6 + p) = pcx ∧ dcx = 128 * p := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, h2, h3, h4⟩
    · omega
    · refine ⟨by omega, ?_, ?_⟩
      · rw [← h3]; congr 1; omega
      · rw [h4]; omega
  subst hpcM hdM
  have hM : X.get (mmaLane L X (h / L.block), xM) =
      some ⟨TmemRow.pvPc (6 + p), .tc (.mma (128 * p) sx accx maskx)⟩ := hM0
  have hmono : ((X.tr (mmaLane L X (h / L.block))).take xM).countP
      (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) ≤ r / 2 :=
    hcnt ▸ countP_take_mono _ _ hxi.le
  have hdoneM : TcMma.DoneBefore L X (mmaLane L X (h / L.block), xM) (h, k) :=
    ld_second hp hX hFw hR hI hB hM he hat' rfl hcy.symm hmono hpol
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
    ⟨k1, -, h1, -⟩ | ⟨⟨pcy, ay, vy, hy, -⟩, hy1, hy2⟩
  · omega
  · -- the source is a PV MMA of the lane
    have hb2eq : b2 = 128 * p := by omega
    subst hb2eq
    obtain ⟨hg, hm, hdone⟩ := ld_pv_src hp hX hFw hsk he2 hon2 hxc2
    subst hg
    obtain ⟨d, k2, hk2, hpcS, hbbS, hissS, hacc, -, -, -, hplS, -⟩ :=
      mma_pvAt hp hX hFw he2 hon2.1 (by omega)
    have hiseq : is = xM := by
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
        have hlt := mmaIssues_lt hM hpR hgt
        have hrd : r ≤ d := by omega
        rw [hxc2] at hplS
        have hwait := ld_first hp hX hFw hR hI hB he hat' rfl hxc2
          (List.getElem?_eq_some_iff.mp he2).1
          (by rw [(hplS (slot2 r))]; exact ru_after (by omega))
          (by rw [(hr (slot2 r)).2]; simp only [slot2]; unfold ringUses; omega)
        exact TcMma.tcStep_asymm hX hG hWB.tcStep hwait.tcStep
    subst hiseq
    have hk26 : k2 = 6 + p := by omega
    subst hk26
    have ha2 : a2 = true := hacc.mpr (.inl (by omega))
    subst ha2 hpcS
    exact ⟨is, s2, _, rfl, by rw [← hpe]; exact he2, by rw [hxc, hpe]; omega, hdone, hm⟩
  · omega
  · -- the source is a rescale store
    exfalso
    have hgs : h = gs := by
      simp only at hy2
      rw [hp.block] at hxc2
      omega
    subst hgs
    obtain ⟨c', hpc', hay, hsh', hvl⟩ := wg0_rst_addr hp hX hFw hat'.1 hy
    have hcxy : (mmaLane L X (h / L.block), xM).1 / L.block = (h, is).1 / L.block := hcy.symm
    obtain ⟨d1, r1, hp1, hq1, h1 | h1⟩ := pvStore_blk hp hX hFw hR hI hB hT hM (by omega) hy hcxy
    · rcases hlat _ hMw with h2 | h2 | h2 | ⟨-, -, -, a3, v3, s3, pc3, hst⟩
      · simp only [Prod.mk.injEq] at h2
        obtain ⟨h21, h22⟩ := h2
        rw [h21, h22] at hM
        rw [hM] at hy
        simp at hy
      · exact TcMma.tcStep_asymm hX hG h2.tcStep h1.2.tcStep
      · exact TcMma.tcStep_asymm hX hG hdoneM.tcStep h2.tcStep
      · cases get_tc_inj hM hst
    · obtain ⟨kM, hkM, hpcM, -, -, honM, -⟩ := pv_pc hT hX hM (by omega)
      obtain ⟨d2, k2, hk2, -, -, hissM, -, -, -, -, hplM, -⟩ :=
        mma_pvAt hp hX hFw hM honM.1 (by omega)
      have hd12 : d1 + 1 = d2 + 1 := ru_eq fun b => by
        have := (hp1 b).symm.trans (hplM b)
        simpa using this
      have hd2 : d2 = r - 1 := by omega
      obtain ⟨hat'', hstB⟩ : MbarRow.Wg0At L h pcy ∧ ∃ r2, ∀ b : Fin 2,
          okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take is) =
            ringUses 2 b.val (r2 + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady b))
            ((X.tr h).take is) = ringUses 2 b.val r2 := by
        have hr4 : 103 ≤ pcy ∧ pcy < 1842 := by
          rw [hpc']; fin_cases c' <;> decide
        have hat3 : MbarRow.Wg0At L h pcy := ⟨hat'.1, hr4.1, hr4.2⟩
        exact ⟨hat3, wg0_stBlock hp hX hFw hy hat3⟩
      obtain ⟨r2, hr2⟩ := hstB
      have hr21' : r2 + 1 = r1 + 1 := ru_eq fun b => by
        have := (hr2 b).1.symm.trans (hq1 b)
        simpa using this
      have hr21 : r2 = r1 := by omega
      have hr1 : r ≤ r1 := by omega
      rcases Nat.lt_trichotomy is k with hlt | heq | hgt
      · -- the store is before the load
        have hmon : ∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take is) ≤
            okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take k) := fun b =>
          countP_take_mono _ _ hlt.le
        have hrr : r1 = r := by
          have h3 := hmon (slot2 r1)
          rw [(hr2 _).1, (hr _).1, hr21] at h3
          simp only [slot2] at h3
          unfold ringUses at h3
          omega
        have hjj : j < 64 := by omega
        rcases hsk with hm' | ⟨a', vals', sh', jj, ⟨pcs, hst⟩, hjj', hcell'⟩
        · obtain ⟨⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, -⟩, -⟩ := hm'
          rw [hy] at h0
          simp at h0
        · have hinj := get_tc_inj hst hy
          simp only [TcKind.st.injEq] at hinj
          obtain ⟨rfl, rfl, rfl⟩ := hinj
          rw [hay] at hcell'
          obtain ⟨-, -, hc2⟩ := stCell hp hat'.1 c'.isLt (j := jj)
          rw [← hcell'] at hc2
          have hcc : c' = c := Fin.ext (by omega)
          subst hcc
          have hord := wg0_rld_before_rst hp hX hFw hat'.1 he (by rw [← hpc']; exact hy)
            (fun b => by rw [(hr b).2, (hr2 b).2, hr21, hrr])
          omega
      · exact hs.1 (by subst heq; rfl)
      · have hbc := TcMma.baseCausality_of_tc_po (L := L) (f := (h, is)) he rfl hgt
          (len_of_get (X := X) hy)
        exact TcMma.tcStep_acyclic hX hG _ (hWB.tcStep.tail (Or.inl hbc))

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

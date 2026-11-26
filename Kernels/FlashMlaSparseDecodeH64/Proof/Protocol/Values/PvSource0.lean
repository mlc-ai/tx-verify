-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvCell
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RsPin
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkPrev
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RldRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Block
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.RStores
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode

@[expose] public section

/-! # The accumulator source of PV MMA `0` and `1` of a block `d ≥ 1`

PV MMA `k < 2` of block `d ≥ 1` accumulates the cell that PV MMA `6 + k` of block `d - 1` wrote
(`d` is the block's number of issues), unless the warpgroup's rescale arm wrote it in between:
the latest write ordered before the read is that MMA, or the rescale store of block `d` of the
lane of the cell (`acc_source_pv0`). A store of an earlier block is done before PV MMA `6 + k`
of block `d - 1` (`pvStore_blk`), a store of a later block is after the read. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem pvPc_inj0 {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

private theorem ru_eq0 {x y : Nat} (h : ∀ b : Fin 2, ringUses 2 b.val x = ringUses 2 b.val y) :
    x = y := by
  have h0 := h 0
  have h1 := h 1
  unfold ringUses at h0 h1
  simp only [Fin.val_zero, Fin.val_one] at h0 h1
  omega

theorem cell_eq {z cell : TcMma.Cell} (h1 : z.cta = cell.cta) (h2 : z.lane = cell.lane)
    (h3 : z.column = cell.column) : cell = z := by
  obtain ⟨z1, z2, z3⟩ := z
  obtain ⟨y1, y2, y3⟩ := cell
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- **A cell written by a PV MMA with D column `128 k` is in its half of the columns.** -/
theorem pv_cell_col (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) {g i k : Nat} {s : TcMma.OperandSpec} {a : Bool} {mask : List Nat}
    {cell : TcMma.Cell}
    (he : X.get (g, i) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * k) s a mask)⟩)
    (hw : TcMma.TmemWrite L X (g, i) cell) :
    cell.cta = g / L.block ∧ 128 * k ≤ cell.column ∧ cell.column < 128 * k + 128 := by
  obtain ⟨hcta, hcl⟩ := writer_cases hp hX hT hw
  refine ⟨hcta, ?_⟩
  rcases hcl with h | ⟨b0, hpv, hb0, hb1, h1, h2⟩ | h | h
  · obtain ⟨k1, ⟨pc1, s1, hk1, he1, -⟩, -, -⟩ := h
    rw [he] at he1
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he1
    omega
  · obtain ⟨pc1, s1, a1, he1, -⟩ := hpv
    rw [he] at he1
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he1
    have h3 : b0 = 128 * k := he1.2.1.symm
    rw [h3] at h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨k1, ⟨pc1, c1, hk1, he1, -⟩, -, -⟩ := h
    rw [he] at he1
    cases he1
  · obtain ⟨⟨pc1, a1, v1, he1, -⟩, -, -⟩ := h
    rw [he] at he1
    cases he1

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
  (hG : SyncGuarded L kernel X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
include hp hX hFw hR hI hB hT hO hPS hG ht hmd

omit hPS ht hmd in
/-- **The accumulator source of PV MMA `k < 2` of a block `d ≥ 1`** (any source of the read). -/
theorem acc_source_pv0 {g i k : Nat} {s : TcMma.OperandSpec}
    {mask : List Nat} {cell : TcMma.Cell} {src : EvId}
    (he : X.get (g, i) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * k) s true mask)⟩) (hk : k < 2)
    (hr : X.MmaReadCell (g, i) cell) (hsrc : TcMma.ReadSource L X .acc src (g, i) cell) :
    ∃ d, 1 ≤ d ∧ mmaIssues ((X.tr g).take i) = 24 * d + 16 + k ∧
        ((∃ j s' m', src = (g, j) ∧ X.get src = some ⟨TmemRow.pvPc (6 + k),
            .tc (.mma (128 * k) s' true m')⟩ ∧
          mmaIssues ((X.tr g).take j) = 24 * (d - 1) + 16 + (6 + k) ∧ X.MmaCell src cell) ∨
        (∃ (h is a c : Nat) (vals : List Value), src = (h, is) ∧ h / L.block = cell.cta ∧
          h % 384 = cell.lane ∧ warp L h < 4 ∧ c < 4 ∧
          X.get src = some ⟨[814, 915, 1016, 1117].getD c 0, .tc (.st a vals .s32x32b)⟩ ∧
          a = 64 * c ∧ vals.length = 64 ∧ cell.column / 64 = c ∧
          (∀ b : Fin 2, arrivals (mbarLoc L (h / L.block) (.soReady b)) ((X.tr h).take is) =
            ringUses 2 b.val d) ∧
          ∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take is) =
            ringUses 2 b.val (d + 1))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨kr, hkr, hpcr, hdr, -, honr, hopsr⟩ := pv_pc hT hX he (by omega)
  obtain ⟨d, kk, -, hpcA, hbbA, hiss, hacc, -, -, -, hplE, -⟩ :=
    mma_pvAt hp hX hFw he honr.1 (by omega)
  have hkk : k = kk := pvPc_inj0 hpcA
  subst hkk
  have hd1 : 1 ≤ d := by
    rcases hacc.mp rfl with h2 | h2
    · omega
    · exact h2
  refine ⟨d, hd1, hiss, ?_⟩
  have hwr := acc_write hX hT hr
  -- PV MMA `6 + k` of block `d - 1`
  obtain ⟨xM, hxi, pcx, dcx, sx, accx, maskx, hM0, hpx1, hpx2, hxc⟩ :=
    mma_with_count (X := X) (g := g) (i := i) (c := 24 * (d - 1) + 22 + k) (by omega)
  obtain ⟨r', k', hk', hiss', hcases⟩ := mma_slot_pc hp hX hFw hM0 ⟨by omega, by omega⟩
  obtain ⟨hkk, hpcM, hdM⟩ : k' = 22 + k ∧ TmemRow.pvPc (6 + k) = pcx ∧ dcx = 128 * k := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, h2, h3, h4⟩
    · omega
    · refine ⟨by omega, ?_, ?_⟩
      · rw [← h3]; congr 1; omega
      · rw [h4]; omega
  subst hpcM hdM
  have hM : X.get (g, xM) = some ⟨TmemRow.pvPc (6 + k), .tc (.mma (128 * k) sx accx maskx)⟩ := hM0
  obtain ⟨kM0, hkM0, hpcM0, hdM0, -, honM, hopsM⟩ := pv_pc hT hX hM (by omega)
  obtain ⟨dM, kM, -, hpcMA, hbbMA, hissM, haccM, -, -, -, hplM, -⟩ :=
    mma_pvAt hp hX hFw hM honM.1 (by omega)
  have hkM : 6 + k = kM := pvPc_inj0 hpcMA
  subst hkM
  have haccx : accx = true := haccM.mpr (.inl (by omega))
  subst haccx
  have hdM1 : dM = d - 1 := by omega
  have hmr : X.MmaCell (g, i) cell := by
    rcases hwr with h | ⟨a, vals, sh, j, ⟨pc, hst⟩, -⟩ | ⟨c, cta, index, lane, ⟨pc, hcg⟩, -⟩ |
      ⟨sp, ⟨pc, hsh⟩, -⟩
    · exact h
    · cases get_tc_inj he hst
    · cases get_tc_inj he hcg
    · exact absurd rfl (no_shift_of_code hX code_noShift hsh sp)
  have hmM : X.MmaCell (g, xM) cell := pv_cell_shared hp hX hT he hM hk hmr
  have hMw : TcMma.TmemWrite L X (g, xM) cell := .inl hmM
  have hBM : TcMma.WriteBefore L X (g, xM) (g, i) := pv_writeBefore hp hX hT hM he hk hxi
  obtain ⟨-, hsw, hWB, hlat, -⟩ := TcMma.readSource_acc.mp hsrc
  obtain ⟨hctaI, hcol1, hcol2⟩ := pv_cell_col hp hX hT he hwr
  have hcol : 128 * k ≤ cell.column ∧ cell.column < 128 * k + 128 := ⟨hcol1, hcol2⟩
  have hpR : 1853 ≤ TmemRow.pvPc (6 + k) ∧ TmemRow.pvPc (6 + k) ≤ 2160 := by
    simp only [TmemRow.pvPc]
    split <;> omega
  obtain ⟨g2, i2⟩ := src
  obtain ⟨hctaS, hclS⟩ := writer_cases hp hX hT hsw
  rcases hclS with ⟨k1, -, h1, -⟩ | ⟨b2, ⟨pc2, s2, a2, he2, hon2, hops2⟩, hb2, hb2m, h2l, h2h⟩ |
    ⟨k1, -, h1, -⟩ | ⟨⟨pcy, ay, vy, hy, hwy⟩, hy1, hy2⟩
  · omega
  · -- the source is a PV MMA of the lane
    have hb2eq : b2 = 128 * k := by omega
    subst hb2eq
    have hm : X.MmaCell (g2, i2) cell := by
      rcases hsw with hm | ⟨a3, vals, sh3, jj, ⟨pcs, hst⟩, -, -⟩ | hcp | ⟨sp, ⟨pc', hsh⟩, -⟩
      · exact hm
      · cases get_tc_inj he2 hst
      · obtain ⟨c, cta, index, lane, ⟨pcc, hcg⟩, -⟩ := id hcp
        cases get_tc_inj he2 hcg
      · exact absurd rfl (no_shift_of_code hX code_noShift hsh sp)
    obtain ⟨hsg, hlt⟩ := acc_mma_prev hp hX hT hO hG hr hsrc hm
    simp only at hsg hlt
    subst hsg
    obtain ⟨d2, kk2, hkk8, hpc2, hbb2, hiss2, -, -, -, -, -, -⟩ :=
      mma_pvAt hp hX hFw he2 hon2.1 (by omega)
    have hk2r : TmemRow.pvPc kk2 = pc2 := hpc2.symm
    have hlt2 := mmaIssues_lt he2 (by rw [← hk2r]; simp only [TmemRow.pvPc]; split <;> omega) hlt
    have hij : i2 = xM := by
      rcases Nat.lt_trichotomy i2 xM with hlt3 | heq | hgt
      · exfalso
        have hB1 := pv_writeBefore hp hX hT he2 hM hk hlt3
        rcases hlat (g2, xM) hMw with h1 | h1 | h1 | h1
        · exact absurd (congrArg Prod.snd h1) (by simp only; omega)
        · exact absurd (congrArg Prod.snd h1) (by simp only; omega)
        · exact TcMma.tcStep_acyclic hX hG _ (h1.tcStep.trans hB1.tcStep)
        · exact TcMma.tcStep_acyclic hX hG _ (h1.tcStep.trans hBM.tcStep)
      · exact heq
      · exfalso
        have hlt4 := mmaIssues_lt hM hpR hgt
        omega
    subst hij
    left
    exact ⟨i2, sx, maskx, rfl, hM, by omega, hm⟩
  · omega
  · -- the source is a rescale store
    right
    have hgh : g2 / L.block = g / L.block := hctaS.symm.trans hctaI
    simp only at hy2
    obtain ⟨c, hpc', hay, -, hvl⟩ := wg0_rst_addr hp hX hFw hwy hy
    have hcolc : cell.column / 64 = c := by
      rcases hsw with ⟨⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, -⟩⟩ |
        ⟨a3, vals3, sh3, jj, ⟨pcs, hst⟩, hjj, hcell3⟩ | hcp | ⟨sp, ⟨pc', hsh⟩, -⟩
      · rw [hy] at h0
        simp at h0
      · have hinj := get_tc_inj hst hy
        simp only [TcKind.st.injEq] at hinj
        obtain ⟨rfl, rfl, rfl⟩ := hinj
        rw [hay] at hcell3
        obtain ⟨-, -, hc2⟩ := stCell hp hwy c.isLt (j := jj)
        rw [← hcell3] at hc2
        omega
      · obtain ⟨c', cta, index, lane, ⟨pcc, hcg⟩, -⟩ := id hcp
        cases get_tc_inj hy hcg
      · exact absurd rfl (no_shift_of_code hX code_noShift hsh sp)
    have hcxy : (g, xM).1 / L.block = (g2, i2).1 / L.block := hgh.symm
    have hcey : (g, i).1 / L.block = (g2, i2).1 / L.block := hgh.symm
    obtain ⟨dA, rA, hpA, hqA, hA⟩ := pvStore_blk hp hX hFw hR hI hB hT hM (by omega) hy hcxy
    obtain ⟨dB, rB, hpB, hqB, hB'⟩ := pvStore_blk hp hX hFw hR hI hB hT he (by omega) hy hcey
    have hdA : dA + 1 = dM + 1 := ru_eq0 fun b => by
      have := (hpA b).symm.trans (hplM b)
      simpa using this
    have hdB : dB + 1 = d + 1 := ru_eq0 fun b => by
      have := (hpB b).symm.trans (hplE b)
      simpa using this
    have hrAB : rA + 1 = rB + 1 := ru_eq0 fun b => by
      have := (hqA b).symm.trans (hqB b)
      simpa using this
    have hrd : rA = d := by
      rcases hA with hA | hA
      · exfalso
        rcases hlat (g, xM) hMw with h2 | h2 | h2 | h2
        · obtain ⟨h21, h22⟩ := Prod.mk.inj h2
          rw [h21, h22] at hM
          rw [hM] at hy
          simp at hy
        · exact absurd (congrArg Prod.snd h2) (by simp only; omega)
        · exact TcMma.tcStep_asymm hX hG h2.tcStep hA.2.tcStep
        · exact TcMma.tcStep_acyclic hX hG _ (h2.tcStep.trans hBM.tcStep)
      · rcases hB' with hB' | hB'
        · omega
        · exact absurd (hB'.2.tcStep) (fun h3 => TcMma.tcStep_asymm hX hG h3 hWB.tcStep)
    have hr4 : 103 ≤ pcy ∧ pcy < 1842 := by
      rw [hpc']; fin_cases c <;> decide
    have hat3 : MbarRow.Wg0At L g2 pcy := ⟨hwy, hr4.1, hr4.2⟩
    obtain ⟨r2, hr2⟩ := wg0_stBlock hp hX hFw hy hat3
    have hr2A : r2 + 1 = rA + 1 := ru_eq0 fun b => by
      have := (hr2 b).1.symm.trans (hqA b)
      simpa using this
    refine ⟨g2, i2, ay, c, vy, rfl, hctaS.symm, hy2.symm, hwy, c.isLt, hpc' ▸ hy, hay, hvl, hcolc,
      fun b => ?_, fun b => ?_⟩
    · rw [(hr2 b).2]
      congr 1
      omega
    · have := hqA b
      rw [hrd] at this
      exact this

omit hO hPS ht hmd in
/-- **When the source is the MMA, the arm of the block was skipped**: the lane `h` of the cell has
its arrival at the end of block `d` (`ia`), and its vote 18 events before it is false. -/
theorem pv0_mma_noarm (hnu : ¬ HasUb X) {g i j k d h ia tx cnt : Nat} {l : Loc} {rel : Bool}
    {sc : MbarScope} {s s' : TcMma.OperandSpec} {mask m' : List Nat} {cell : TcMma.Cell}
    (he : X.get (g, i) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * k) s true mask)⟩) (hk : k < 2)
    (hr : X.MmaReadCell (g, i) cell) (hd1 : 1 ≤ d)
    (hiss : mmaIssues ((X.tr g).take i) = 24 * d + 16 + k)
    (hs : TcMma.ReadSource L X .acc (g, j) (g, i) cell)
    (hM : X.get (g, j) = some ⟨TmemRow.pvPc (6 + k), .tc (.mma (128 * k) s' true m')⟩)
    (hissM : mmaIssues ((X.tr g).take j) = 24 * (d - 1) + 16 + (6 + k))
    (hh : h / L.block = cell.cta) (hl : h % 384 = cell.lane)
    (hw : warp L h < 4)
    (hia : X.get (h, ia) = some ⟨1122, .arrive l tx cnt rel sc⟩)
    (harr : ∀ b : Fin 2, arrivals (mbarLoc L (h / L.block) (.soReady b)) ((X.tr h).take ia) =
      ringUses 2 b.val d) :
    ∃ q mm a, 18 ≤ ia ∧ X.get (h, ia - 18) = some ⟨578, .voteMode q mm a false⟩ ∧
      ∀ l', arrivals l' ((X.tr h).take (ia - 18)) = arrivals l' ((X.tr h).take ia) := by
  obtain ⟨r, harr', hcase⟩ := wg0_arm hp hX hFw hnu hw hia
  have hrd : d = r := (ru_eq0 fun b => (harr' b).symm.trans (harr b)).symm
  subst hrd
  rcases hcase with ⟨h18, q, mm, a, res, hv, hres, hAr⟩ | ⟨h36, h1r, -, hst⟩
  · refine ⟨q, mm, a, h18, ?_, hAr⟩
    rcases hres with h0 | h0
    · omega
    · rw [← h0]; exact hv
  · exfalso
    have hwr := acc_write hX hT hr
    obtain ⟨hctaI, hcol1, hcol2⟩ := pv_cell_col hp hX hT he hwr
    have hcol : 128 * k ≤ cell.column ∧ cell.column < 128 * k + 128 := ⟨hcol1, hcol2⟩
    have hc4 : cell.column / 64 < 4 := by omega
    obtain ⟨a, vals, sh, hyc, harry⟩ := hst ⟨cell.column / 64, hc4⟩
    obtain ⟨c2, hpc2, ha2, hsh2, hvl2⟩ := wg0_rst_addr hp hX hFw hw hyc
    subst hsh2
    have hcinj : ∀ c c' : Fin 4, [814, 915, 1016, 1117].getD c.val 0 =
        [814, 915, 1016, 1117].getD c'.val 0 → c = c' := by decide
    have hcc : c2 = ⟨cell.column / 64, hc4⟩ := (hcinj _ _ hpc2.symm)
    obtain ⟨jj, hjj⟩ : ∃ jj, jj = cell.column % 64 := ⟨_, rfl⟩
    have hc2v : c2.val = cell.column / 64 := by rw [hcc]
    obtain ⟨hcta2, hlane2, hcol2⟩ := stCell hp hw c2.isLt (j := jj)
    have hcell : cell = tcDataCell L h .s32x32b (64 * c2.val) jj := cell_eq (hcta2.trans hh)
      (hlane2.trans hl) (by omega)
    have hjl : jj < vals.length := by omega
    have hWy : TcMma.TmemWrite L X (h, ia - 16 + 4 * (cell.column / 64)) cell :=
      .inr (.inl ⟨a, vals, .s32x32b, jj, ⟨_, hyc⟩, hjl, by rw [ha2]; exact hcell⟩)
    have hr4 : 103 ≤ [814, 915, 1016, 1117].getD c2.val 0 ∧
        [814, 915, 1016, 1117].getD c2.val 0 < 1842 := by
      fin_cases c2 <;> decide
    have hat3 : MbarRow.Wg0At L h
        ([814, 915, 1016, 1117].getD (↑(⟨cell.column / 64, hc4⟩ : Fin 4)) 0) :=
      ⟨hw, by rw [hpc2]; exact hr4⟩
    obtain ⟨r2, hr2⟩ := wg0_stBlock hp hX hFw hyc hat3
    have hr2d : r2 = d := ru_eq0 fun b => (hr2 b).2.symm.trans ((harry _).trans (harr b))
    have hgh : g / L.block = h / L.block := hctaI.symm.trans hh.symm
    have hcxy : (g, j).1 / L.block = (h, ia - 16 + 4 * (cell.column / 64)).1 / L.block := hgh
    have hcey : (g, i).1 / L.block = (h, ia - 16 + 4 * (cell.column / 64)).1 / L.block := hgh
    obtain ⟨kr, -, -, -, -, honr, -⟩ := pv_pc hT hX he (by omega)
    obtain ⟨dE, kE, -, hpcE, -, hissE, -, -, -, -, hplE, -⟩ :=
      mma_pvAt hp hX hFw he honr.1 (by omega)
    have hkE : k = kE := pvPc_inj0 hpcE
    subst hkE
    obtain ⟨kM0, -, -, -, -, honM, -⟩ := pv_pc hT hX hM (by omega)
    obtain ⟨dM, kM, -, hpcMA, -, hissMA, -, -, -, -, hplM, -⟩ :=
      mma_pvAt hp hX hFw hM honM.1 (by omega)
    have hkM : 6 + k = kM := pvPc_inj0 hpcMA
    subst hkM
    obtain ⟨dB, rB, hpB, hqB, hB'⟩ := pvStore_blk hp hX hFw hR hI hB hT he (by omega) hyc hcey
    obtain ⟨dA, rA, hpA, hqA, hA⟩ := pvStore_blk hp hX hFw hR hI hB hT hM (by omega) hyc hcxy
    have hdB : dB + 1 = dE + 1 := ru_eq0 fun b => by
      have := (hpB b).symm.trans (hplE b)
      simpa using this
    have hdA : dA + 1 = dM + 1 := ru_eq0 fun b => by
      have := (hpA b).symm.trans (hplM b)
      simpa using this
    have hrB : rB + 1 = r2 + 1 := ru_eq0 fun b => by
      have := (hqB b).symm.trans (hr2 b).1
      simpa using this
    have hrA : rA + 1 = r2 + 1 := ru_eq0 fun b => by
      have := (hqA b).symm.trans (hr2 b).1
      simpa using this
    obtain ⟨-, -, hWB, hlat, -⟩ := TcMma.readSource_acc.mp hs
    have hSD : TcMma.StoreDoneBefore L X (h, ia - 16 + 4 * (cell.column / 64)) (g, i) := by
      rcases hB' with hB' | hB'
      · exact hB'.2
      · omega
    have hDM : TcMma.DoneBefore L X (g, j) (h, ia - 16 + 4 * (cell.column / 64)) := by
      rcases hA with hA | hA
      · omega
      · exact hA.2
    rcases hlat _ hWy with h2 | h2 | h2 | h2
    · obtain ⟨h21, h22⟩ := Prod.mk.inj h2
      rw [h21, h22] at hyc
      rw [hM] at hyc
      simp at hyc
    · obtain ⟨h21, h22⟩ := Prod.mk.inj h2
      rw [h21, h22] at hyc
      rw [he] at hyc
      simp at hyc
    · exact TcMma.tcStep_asymm hX hG h2.tcStep hDM.tcStep
    · exact TcMma.tcStep_asymm hX hG hSD.tcStep h2.tcStep

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.QkSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvPrev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvAt

@[expose] public section

/-! # The accumulator source of PV MMA `k ≥ 2` is PV MMA `k - 2` of its block

PV MMA `k` (D at `128 (k % 2)`) of block `d` accumulates the cell its PV MMA `k - 2` wrote
(`mma_pvPrev`: the previous MMA with its D column). The latest write ordered before the read is
that MMA: a write of the cell is a PV MMA of the lane (the only MMA with that D column between is
none) or a rescale store, and a store is ordered, by its block, before the whole block's PV MMAs
or after all of them (`pvStore_blk`), so it is not between them (`acc_source_pv`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A PV MMA is at `pvPc k`**, with D at `128 (k % 2)`. -/
theorem pv_pc (hR : TmemRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {g i pc d : Nat} {s : TcMma.OperandSpec} {a : Bool} {mask : List Nat}
    (he : X.get (g, i) = some ⟨pc, .tc (.mma d s a mask)⟩) (hd : d < 256) :
    ∃ k, k < 8 ∧ pc = TmemRow.pvPc k ∧ d = 128 * (k % 2) ∧ mask = [0, 0, 0, 0] ∧ MmaOn L g pc ∧
      TmemRow.MmaOps L g s none TmemRow.pvIdesc := by
  have hg := Frame.lt_of_get hX he
  rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
      ⟨_, _, k, hk, hpc, h, -, hops⟩ <;> simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
    · cases h
    · cases h
    · cases h
    · obtain ⟨h1, -⟩ := h
      omega
    · obtain ⟨h1, rfl, rfl, rfl⟩ := h
      refine ⟨k, hk, hpc, h1, rfl, ⟨hat, ?_⟩, hops⟩
      simp only [TmemRow.pvPc] at hpc
      split at hpc <;> omega
  · cases hc'

private theorem ru_two {a b : Nat} (h0 : ringUses 2 0 (a + 1) = ringUses 2 0 (b + 1))
    (h1 : ringUses 2 1 (a + 1) = ringUses 2 1 (b + 1)) : a = b := by
  unfold ringUses at h0 h1
  omega

private theorem pvPc_inj2 {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

private theorem pvPc_rng2 {k : Nat} (hk : k < 8) :
    1853 ≤ TmemRow.pvPc k ∧ TmemRow.pvPc k ≤ 2160 := by
  simp only [TmemRow.pvPc]
  split <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
  (hG : SyncGuarded L kernel X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
include hp hX hFw hR hI hB hT hO hPS hG ht hmd

/-- **The accumulator source of PV MMA `k ≥ 2`**: PV MMA `k - 2` of the lane. -/
theorem acc_source_pv {g i k : Nat} {s : TcMma.OperandSpec} {mask : List Nat} {cell : TcMma.Cell}
    (he : X.get (g, i) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * (k % 2)) s true mask)⟩)
    (hk2 : 2 ≤ k) (hk : k < 8) (hr : X.MmaReadCell (g, i) cell) :
    ∃ j < i, (∃ s' acc' mask', X.get (g, j) =
        some ⟨TmemRow.pvPc (k - 2), .tc (.mma (128 * (k % 2)) s' acc' mask')⟩) ∧
      (∃ r, mmaIssues ((X.tr g).take i) = 24 * r + 16 + k ∧
        mmaIssues ((X.tr g).take j) = 24 * r + 16 + (k - 2)) ∧
      X.MmaCell (g, j) cell ∧ TcMma.ReadSource L X .acc (g, j) (g, i) cell := by
  obtain ⟨j, hji, s', a', m', hj, hrr, hbt⟩ := mma_pvPrev hp hX hFw he hk2 hk
  obtain ⟨src, hsrc⟩ := acc_source hp hX hFw hT hO hPS hG ht hmd hr
  have hwr := acc_write hX hT hr
  have hg := Frame.lt_of_get hX he
  have hr0 := hr
  obtain ⟨d0, s0, mask0, row, col, ⟨pc0, he0⟩, hc⟩ := hr
  rw [he] at he0
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he0
  obtain ⟨-, rfl, rfl, -, rfl⟩ := he0
  obtain ⟨ki, hki, hpci, hdi, -, honi, hopsi⟩ := pv_pc hT hX he (by omega)
  obtain ⟨kj, hkj, hpcj, hdj, hmj, honj, hopsj⟩ := pv_pc hT hX hj (by omega)
  subst hmj
  have hdd : s.descriptor = s'.descriptor := by
    obtain ⟨-, hd1, -⟩ := hopsi
    obtain ⟨-, hd2, -⟩ := hopsj
    exact Option.some.inj (hd1.symm.trans hd2)
  obtain ⟨hl, hh⟩ := ops_cta hp hg (.inr rfl) hopsi
  obtain ⟨hl', hh'⟩ := ops_cta hp hg (.inr rfl) hopsj
  have hcell : TcMma.resultCell s' (128 * (k % 2)) row col = some cell := by
    have hlo : s.lowCta = s'.lowCta := hl.trans hl'.symm
    have hhi : s.highCta = s'.highCta := hh.trans hh'.symm
    rw [← hc]
    unfold TcMma.resultCell
    rw [hdd, hlo, hhi]
  have hW : TcMma.TmemWrite L X (g, j) cell :=
    .inl ⟨128 * (k % 2), s', a', [0, 0, 0, 0], row, col, ⟨_, hj⟩,
      writeCell_zeroMask (ops_group (.inr rfl) hopsj) (ops_m64 (.inr rfl) hopsj) hcell⟩
  have hBf : TcMma.WriteBefore L X (g, j) (g, i) :=
    .inl (TcMma.Before.of_mma_po ⟨_, hj⟩ ⟨_, he⟩ hg rfl hji
      ⟨rfl, by rw [hdd], by rw [hdd], by rw [hl, hl'], by rw [hh, hh']⟩)
  obtain ⟨-, -, -, hlatest, -⟩ := TcMma.readSource_acc.mp hsrc
  obtain ⟨hctaI, hclI⟩ := writer_cases hp hX hT hwr
  have hcol : 128 * (k % 2) ≤ cell.column ∧ cell.column < 128 * (k % 2) + 128 := by
    rcases hclI with ⟨k1, ⟨pc1, s1, hk1, he1, -⟩, -, -⟩ |
      ⟨b0, ⟨pc1, s1, a1, he1, -⟩, hb0, hb1, h1, h2⟩ |
      ⟨k1, ⟨pc1, c1, hk1, he1, -⟩, -, -⟩ | ⟨⟨pc1, a1, v1, he1, -⟩, -, -⟩
    · rw [he] at he1
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he1
      omega
    · rw [he] at he1
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he1
      obtain ⟨-, h3, -⟩ := he1
      subst h3
      exact ⟨h1, h2⟩
    · rw [he] at he1
      cases he1
    · rw [he] at he1
      cases he1
  obtain ⟨g2, i2⟩ := src
  obtain ⟨hctaS, hclS⟩ := writer_cases hp hX hT hsrc.2.1
  rcases hclS with ⟨k1, -, h1, -⟩ | ⟨b2, ⟨pc2, s2, a2, he2, hon2, hops2⟩, hb2, hb2m, h2l, h2h⟩ |
    ⟨k1, -, h1, -⟩ | ⟨⟨pcy, ay, vy, hy, -⟩, hy1, hy2⟩
  · omega
  · -- the source is a PV MMA of the lane
    have hb2eq : b2 = 128 * (k % 2) := by omega
    have hm : X.MmaCell (g2, i2) cell := by
      rcases hsrc.2.1 with hm | ⟨a3, vals, sh, jj, ⟨pcs, hst⟩, -, -⟩ | hcp | ⟨sp, ⟨pc', hsh⟩, -⟩
      · exact hm
      · cases get_tc_inj he2 hst
      · obtain ⟨c, cta, index, lane, ⟨pcc, hcg⟩, -⟩ := id hcp
        cases get_tc_inj he2 hcg
      · exact absurd rfl (no_shift_of_code hX code_noShift hsh sp)
    obtain ⟨hsg, hlt⟩ := acc_mma_prev hp hX hT hO hG hr0 hsrc hm
    simp only at hsg hlt
    subst hsg
    obtain ⟨k2, hk2', hpc2, -⟩ := pv_pc hT hX he2 (by omega)
    have hr2 := pvPc_rng2 hk2'
    have hij : i2 = j := by
      rcases Nat.lt_trichotomy i2 j with h | h | h
      · exfalso
        have hpo : po X (g2, i2) (g2, j) :=
          po_of_not_access rfl h (len_of_get hj) (by rw [hj]; rfl)
        rcases hlatest (g2, j) hW with h1 | h1 | h1 | h1
        · exact absurd (congrArg Prod.snd h1) (by simp only; omega)
        · exact absurd (congrArg Prod.snd h1) (by simp only; omega)
        · exact TcMma.tcStep_acyclic hX hG _ (h1.tcStep.tail (.inl (.single (.inl hpo))))
        · have hB' : TcMma.WriteBefore L X (g2, i) (g2, j) := .inl h1
          exact TcMma.tcStep_acyclic hX hG _ (hBf.tcStep.trans hB'.tcStep)
      · exact h
      · exfalso
        rw [← hpc2] at hr2
        exact hbt i2 h hlt _ b2 s2 a2 _ he2 (by omega) (by omega) hb2eq
    subst hij
    exact ⟨i2, hlt, ⟨s', a', [0, 0, 0, 0], hj⟩, hrr, hm, hsrc⟩
  · omega
  · -- the source is a rescale store: it is not between the two MMAs
    exfalso
    have hcI : (g, i).1 / L.block = (g2, i2).1 / L.block := hctaI.symm.trans hctaS
    have hcJ : (g, j).1 / L.block = (g2, i2).1 / L.block := hcI
    obtain ⟨d1, r1, hp1, hq1, h1 | h1⟩ := pvStore_blk hp hX hFw hR hI hB hT he (by omega) hy hcI
    swap
    · exact TcMma.tcStep_acyclic hX hG _ (h1.2.tcStep.trans hsrc.2.2.1.tcStep)
    obtain ⟨d2, r2, hp2, hq2, h2 | h2⟩ := pvStore_blk hp hX hFw hR hI hB hT hj (by omega) hy hcJ
    swap
    · -- the store is of a later block than the MMA `k - 2` but not than the MMA `k`
      have hrr' : r1 = r2 := ru_two (by simpa using (hq1 0).symm.trans (hq2 0))
        (by simpa using (hq1 1).symm.trans (hq2 1))
      obtain ⟨rr, hri, hrj⟩ := hrr
      obtain ⟨dB1, kB1, -, hpcB1, -, hiss1, -, -, -, -, hpl1, -⟩ := mma_pvAt hp hX hFw he
        honi.1 (by omega)
      obtain ⟨dB2, kB2, -, hpcB2, -, hiss2, -, -, -, -, hpl2, -⟩ := mma_pvAt hp hX hFw hj
        honj.1 (by omega)
      have e1 := pvPc_inj2 hpcB1
      have e2 := pvPc_inj2 hpcB2
      have hd1 : d1 = dB1 := ru_two (by simpa using (hp1 0).symm.trans (hpl1 0))
        (by simpa using (hp1 1).symm.trans (hpl1 1))
      have hd2 : d2 = dB2 := ru_two (by simpa using (hp2 0).symm.trans (hpl2 0))
        (by simpa using (hp2 1).symm.trans (hpl2 1))
      omega
    · have hrr' : r1 = r2 := ru_two (by simpa using (hq1 0).symm.trans (hq2 0))
        (by simpa using (hq1 1).symm.trans (hq2 1))
      rcases hlatest (g, j) hW with h3 | h3 | h3 | h3
      · have e := Prod.mk.inj h3
        rw [e.1, e.2] at hj
        rw [hj] at hy
        simp at hy
      · have e := Prod.mk.inj h3
        omega
      · exact TcMma.tcStep_acyclic hX hG _ (h3.tcStep.trans h2.2.tcStep)
      · exact TcMma.tcStep_acyclic hX hG _ (h3.tcStep.trans hBf.tcStep)

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

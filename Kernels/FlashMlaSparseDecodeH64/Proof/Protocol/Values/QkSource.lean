-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaResults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.SourceDone
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkPrev

@[expose] public section

/-! # The accumulator source of QK MMA `k` is QK MMA `k - 1` of its block

A QK MMA (D at column 400) is at `qkPc k` for a `k < 16` (`qk_pc`); the writers of the cells of
columns `[400, 464)` are QK MMAs only (`qk_writer`). QK MMA `k ≥ 1` accumulates; the MMA lane's
previous MMA is QK MMA `k - 1`, with no MMA between (`mma_qkPrev`). It writes the cell the read
reads and is ordered before the read by the lane's program order, so it is the latest write ordered
before the read: the read source is it (`acc_source_qk`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A QK MMA is at `qkPc k`**, accumulating iff `k ≠ 0`. -/
theorem qk_pc (hR : TmemRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {g i pc : Nat} {s : TcMma.OperandSpec} {a : Bool} {mask : List Nat}
    (he : X.get (g, i) = some ⟨pc, .tc (.mma 400 s a mask)⟩) :
    ∃ k, k < 16 ∧ pc = TmemRow.qkPc k ∧ a = (k != 0) ∧ mask = [0, 0, 0, 0] ∧ MmaOn L g pc ∧
      TmemRow.MmaOps L g s (some (256 + 8 * k)) TmemRow.qkIdesc := by
  have hg := Frame.lt_of_get hX he
  rcases tc_role hR hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
      ⟨_, _, k, hk, hpc, h, -, hops⟩ <;> simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
    · cases h
    · cases h
    · cases h
    · obtain ⟨-, rfl, rfl, rfl⟩ := h
      refine ⟨k, hk, hpc, rfl, rfl, ⟨hat, ?_⟩, hops⟩
      simp only [TmemRow.qkPc] at hpc
      split at hpc <;> omega
    · obtain ⟨h1, -⟩ := h
      omega
  · cases hc'

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hR : TmemRows P L X)
include hp hX hR

/-- **A write of a score-column cell is a QK MMA**: its column is in `[400, 464)` and the
writer is an MMA at `qkPc k` with D at 400. -/
theorem qk_writer {x : EvId} {cell : TcMma.Cell} (hw : TcMma.TmemWrite L X x cell)
    (hc : 400 ≤ cell.column) : ∃ g i k pc s a mask, x = (g, i) ∧ k < 16 ∧ pc = TmemRow.qkPc k ∧
      X.get x = some ⟨pc, .tc (.mma 400 s a mask)⟩ ∧ cell.column < 464 := by
  obtain ⟨-, hcl⟩ := writer_cases hp hX hR hw
  rcases hcl with ⟨k, ⟨pc, s, hk, he, hon, hops⟩, h1, h2⟩ | ⟨b, ⟨pc, s, acc, he, -⟩, hb, -, -, h2⟩ |
    ⟨k, ⟨-, -, hk, -⟩, h1, h2⟩ | ⟨-, h1, -⟩
  · obtain ⟨g, i⟩ := x
    obtain ⟨k', hk', hpc, -⟩ := qk_pc hR hX he
    exact ⟨g, i, k', pc, s, _, _, rfl, hk', hpc, he, h2⟩
  · omega
  · omega
  · omega

/-- **A write of an MMA with D at 400 is in the score columns.** -/
theorem qk_col {x : EvId} {cell : TcMma.Cell} {pc : Nat} {s : TcMma.OperandSpec} {a : Bool}
    {mask : List Nat} (he : X.get x = some ⟨pc, .tc (.mma 400 s a mask)⟩)
    (hw : TcMma.TmemWrite L X x cell) : 400 ≤ cell.column := by
  obtain ⟨-, hcl⟩ := writer_cases hp hX hR hw
  rcases hcl with ⟨k, -, h1, h2⟩ | ⟨b, ⟨pc', s', acc, he', -⟩, hb, -, -, h2⟩ |
    ⟨k, ⟨pc', c, hk, he', -⟩, -, -⟩ | ⟨⟨pc', a', vals, he', -⟩, -, -⟩
  · exact h1
  · rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    omega
  · cases get_tc_inj he he'
  · cases get_tc_inj he he'

end

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
  (hG : SyncGuarded L kernel X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
include hp hX hFw hT hO hPS hG ht hmd

/-- **The accumulator source of QK MMA `k ≥ 1`**: QK MMA `k - 1` of the lane. -/
theorem acc_source_qk {g i k : Nat} {s : TcMma.OperandSpec} {mask : List Nat} {cell : TcMma.Cell}
    (he : X.get (g, i) = some ⟨TmemRow.qkPc k, .tc (.mma 400 s true mask)⟩)
    (hk1 : 1 ≤ k) (hk : k < 16) (hr : X.MmaReadCell (g, i) cell) :
    ∃ j < i, (∃ s' acc' mask', X.get (g, j) =
        some ⟨TmemRow.qkPc (k - 1), .tc (.mma 400 s' acc' mask')⟩) ∧
      (∃ r, mmaIssues ((X.tr g).take i) = 24 * r + k ∧
        mmaIssues ((X.tr g).take j) = 24 * r + (k - 1)) ∧
      X.MmaCell (g, j) cell ∧ TcMma.ReadSource L X .acc (g, j) (g, i) cell := by
  obtain ⟨j, hji, ⟨s', a', m', hj⟩, hrr, hbt⟩ := mma_qkPrev hp hX hFw he hk1 hk
  obtain ⟨src, hsrc⟩ := acc_source hp hX hFw hT hO hPS hG ht hmd hr
  have hwr := acc_write hX hT hr
  have hc400 := qk_col hp hX hT he hwr
  obtain ⟨g2, i2, k2, pc2, s2, a2, m2, hgi, hk2, hpc2, he2, -⟩ :=
    qk_writer hp hX hT hsrc.2.1 hc400
  subst hgi
  have hm : X.MmaCell (g2, i2) cell := by
    rcases hsrc.2.1 with hm | ⟨a, vals, sh, jj, ⟨pcs, hst⟩, hjj, hceq⟩ | hcp |
      ⟨sp, ⟨pc', hsh⟩, -⟩
    · exact hm
    · cases get_tc_inj he2 hst
    · obtain ⟨c, cta, index, lane, ⟨pcc, hcg⟩, -⟩ := id hcp
      cases get_tc_inj he2 hcg
    · exact absurd rfl (no_shift_of_code hX code_noShift hsh sp)
  obtain ⟨hsg, hlt⟩ := acc_mma_prev hp hX hT hO hG hr hsrc hm
  simp only at hsg hlt
  subst hsg
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, s0, mask0, row, col, ⟨pc0, he0⟩, hc⟩ := hr
  rw [he] at he0
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he0
  obtain ⟨-, rfl, rfl, -, rfl⟩ := he0
  obtain ⟨kj, hkj, hpcj, -, hmj, -, hopsj⟩ := qk_pc hT hX hj
  subst hmj
  obtain ⟨ki, hki, hpci, -, -, -, hopsi⟩ := qk_pc hT hX he
  have hdd : s.descriptor = s'.descriptor := by
    obtain ⟨-, hd1, -⟩ := hopsi
    obtain ⟨-, hd2, -⟩ := hopsj
    exact Option.some.inj (hd1.symm.trans hd2)
  obtain ⟨hl, hh⟩ := ops_cta hp hg (.inl rfl) hopsi
  obtain ⟨hl', hh'⟩ := ops_cta hp hg (.inl rfl) hopsj
  have hcell : TcMma.resultCell s' 400 row col = some cell := by
    have hlo : s.lowCta = s'.lowCta := hl.trans hl'.symm
    have hhi : s.highCta = s'.highCta := hh.trans hh'.symm
    rw [← hc]
    unfold TcMma.resultCell
    rw [hdd, hlo, hhi]
  have hW : TcMma.TmemWrite L X (g2, j) cell :=
    .inl ⟨400, s', a', [0, 0, 0, 0], row, col, ⟨_, hj⟩,
      writeCell_zeroMask (ops_group (.inl rfl) hopsj) (ops_m64 (.inl rfl) hopsj) hcell⟩
  have hB : TcMma.WriteBefore L X (g2, j) (g2, i) :=
    .inl (TcMma.Before.of_mma_po ⟨_, hj⟩ ⟨_, he⟩ hg rfl hji
      ⟨rfl, by rw [hdd], by rw [hdd], by rw [hl, hl'], by rw [hh, hh']⟩)
  obtain ⟨-, -, -, hlatest, -⟩ := TcMma.readSource_acc.mp hsrc
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
        exact TcMma.tcStep_acyclic hX hG _ (hB.tcStep.trans hB'.tcStep)
    · exact h
    · exfalso
      have hr2 : 1853 ≤ pc2 ∧ pc2 ≤ 2160 := by
        subst hpc2
        simp only [TmemRow.qkPc]
        split <;> omega
      exact hbt i2 h hlt _ he2 ⟨hr2.1, hr2.2, _, _, _, _, rfl⟩
  subst hij
  exact ⟨i2, hlt, ⟨s', a', [0, 0, 0, 0], hj⟩, hrr, hm, hsrc⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

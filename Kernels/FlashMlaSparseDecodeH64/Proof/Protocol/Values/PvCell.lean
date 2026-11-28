-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect

@[expose] public section

/-! # The PV MMAs of a lane with one D column write the same cells

Every PV MMA of the MMA lane has the same descriptor and CTA group (`MmaOps`), so a cell written
by one is written by every PV MMA of the lane with the same D column, and the earlier one is a
write ordered before the later one. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A cell of one PV MMA is a cell of every PV MMA of the lane with the same D column.** -/
theorem pv_cell_shared (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) {g i j pc pc' kk : Nat} {s s' : TcMma.OperandSpec} {a a' : Bool}
    {mask mask' : List Nat} {cell : TcMma.Cell}
    (hi : X.get (g, i) = some ⟨pc, .tc (.mma (128 * kk) s a mask)⟩)
    (hj : X.get (g, j) = some ⟨pc', .tc (.mma (128 * kk) s' a' mask')⟩) (hkk : kk < 2)
    (hm : X.MmaCell (g, i) cell) : X.MmaCell (g, j) cell := by
  obtain ⟨d, s0, a0, mask0, row, col, ⟨pcx, hx⟩, hc⟩ := hm
  rw [hi] at hx
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hx
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hx
  have hg := Frame.lt_of_get hX hi
  obtain ⟨ki, -, -, -, -, -, hopsi⟩ := pv_pc hT hX hi (by omega)
  obtain ⟨kj, -, -, -, hmj, -, hopsj⟩ := pv_pc hT hX hj (by omega)
  have hdd : s.descriptor = s'.descriptor := by
    obtain ⟨-, hd1, -⟩ := hopsi
    obtain ⟨-, hd2, -⟩ := hopsj
    exact Option.some.inj (hd1.symm.trans hd2)
  obtain ⟨hl, hh⟩ := ops_cta hp hg (.inr rfl) hopsi
  obtain ⟨hl', hh'⟩ := ops_cta hp hg (.inr rfl) hopsj
  have hcell : TcMma.resultCell s' (128 * kk) row col = some cell := by
    have hr := TcMma.writeCell_resultCell hc
    rw [← hr]
    unfold TcMma.resultCell
    rw [hdd, hl.trans hl'.symm, hh.trans hh'.symm]
  exact ⟨128 * kk, s', a', mask', row, col, ⟨_, hj⟩, hmj ▸
    writeCell_zeroMask (ops_group (.inr rfl) hopsj) (ops_m64 (.inr rfl) hopsj) hcell⟩

/-- **An earlier PV MMA of the lane is a write ordered before a later one with its D column.** -/
theorem pv_writeBefore (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) {g i j pc pc' kk : Nat} {s s' : TcMma.OperandSpec} {a a' : Bool}
    {mask mask' : List Nat}
    (hi : X.get (g, i) = some ⟨pc, .tc (.mma (128 * kk) s a mask)⟩)
    (hj : X.get (g, j) = some ⟨pc', .tc (.mma (128 * kk) s' a' mask')⟩) (hkk : kk < 2)
    (hij : i < j) : TcMma.WriteBefore L X (g, i) (g, j) := by
  have hg := Frame.lt_of_get hX hi
  obtain ⟨ki, -, -, -, -, -, hopsi⟩ := pv_pc hT hX hi (by omega)
  obtain ⟨kj, -, -, -, -, -, hopsj⟩ := pv_pc hT hX hj (by omega)
  have hdd : s.descriptor = s'.descriptor := by
    obtain ⟨-, hd1, -⟩ := hopsi
    obtain ⟨-, hd2, -⟩ := hopsj
    exact Option.some.inj (hd1.symm.trans hd2)
  obtain ⟨hl, hh⟩ := ops_cta hp hg (.inr rfl) hopsi
  obtain ⟨hl', hh'⟩ := ops_cta hp hg (.inr rfl) hopsj
  exact .inl (TcMma.Before.of_mma_po ⟨_, hi⟩ ⟨_, hj⟩ hg rfl hij
    ⟨rfl, by rw [hdd], by rw [hdd], by rw [hl, hl'], by rw [hh, hh']⟩)

/-- **The source of a load that is a PV MMA of the CTA is the CTA's MMA lane's, done.** -/
theorem ld_pv_src (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {gs is h pc2 b : Nat} {s : TcMma.OperandSpec} {a : Bool}
    {mask : List Nat} {cell : TcMma.Cell}
    (hsk : (X.MmaCell (gs, is) cell ∧ X.async.mmaDone (gs, is) = true) ∨
      TcMma.StoreCell L X (gs, is) cell)
    (he2 : X.get (gs, is) = some ⟨pc2, .tc (.mma b s a mask)⟩) (hon2 : MmaOn L gs pc2)
    (hxc2 : gs / L.block = h / L.block) :
    gs = mmaLane L X (h / L.block) ∧ X.MmaCell (gs, is) cell ∧
      X.async.mmaDone (gs, is) = true := by
  have hg : gs = mmaLane L X (h / L.block) := by
    rw [← hxc2]
    exact laneOn_eq (mmaOne hp hX hFw) he2 (fun _ h => by cases h) hon2
  rcases hsk with ⟨hm, hdone⟩ | ⟨a', vals, sh', jj, ⟨pcs, hst⟩, -⟩
  · exact ⟨hg, hm, hdone⟩
  · cases get_tc_inj he2 hst

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

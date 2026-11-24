-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseTailTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The actual first LSE instruction sequence forms the bound-checked packed address
from the retained ABI pointer, head stride and request offset. -/
theorem correctionLseBaseRun {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch head : Nat} (hBatch : batch < p.batch) (hHead : head < p.heads)
    (hRows : 0 < p.qLength batch) {t : TState} {F : List (Nat × Value)} (ht : At t 9057 F)
    (hOffset : (1634, b32 (p.qOffset batch)) ∈ F) (hHeadWord : (9605, b64 head) ∈ F)
    (hStride : (7501, b64 p.lseStride) ∈ F) (hBase : (7500, b64 p.lseBase) ∈ F)
    (hWrites : ((kernel.code.drop 9057).take 4).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true) :
    ∃ u, At u 9061 ((9525, b64 (p.lseLoc (p.qOffset batch) head).addr) :: F) ∧
      run kernel Assumptions.all l g 4 t = some u := by
  have hOffsetBound : p.qOffset batch < 2 ^ 31 := by
    have hT := hp.shape.2.2.2.2
    have hO := hp.qOffset_le_total hBatch.le
    omega
  have hHeadBound : head < 2 ^ 64 := by
    have hH := (hp.values (17, p.heads) (by simp [Params.scalarWords])).1
    omega
  have hStrideBound : p.lseStride < 2 ^ 64 := by
    have hs := hp.objectBytes 4 16 8 p.lseStride (by simp [Params.objectWords])
    exact hs.1
  have hAddrBound : (p.lseLoc (p.qOffset batch) head).addr < 2 ^ 64 := by
    have hEnd := hp.qOffset_le_total (b := batch + 1) (by omega)
    have hQ : p.qOffset batch < p.totalQ := by unfold Params.qLength at hRows; omega
    have hR := hp.ranges p.lseRegion (by simp)
    have hH := Nat.mul_le_mul_right p.lseStride (show head ≤ p.heads - 1 by omega)
    simp only [Params.lseLoc, globalLoc, Params.lseRegion] at hR ⊢
    omega
  obtain ⟨u, hu, hU⟩ := lsePackedBase (l := l) (g := g) hOffsetBound hHeadBound hStrideBound
    hAddrBound t (ht.mono ⟨holds_mem ht.2.2.2.2 hOffset, holds_mem ht.2.2.2.2 hHeadWord,
      holds_mem ht.2.2.2.2 hStride, holds_mem ht.2.2.2.2 hBase, trivial⟩)
  obtain ⟨hRun, hFrame⟩ := lseTailLinear (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) hWrites
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hCarry := holdsSchedulerFrame ht.2.2.2.2 hFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, hU.mono ⟨hU.2.2.2.2.1, hCarry⟩, hRun⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction

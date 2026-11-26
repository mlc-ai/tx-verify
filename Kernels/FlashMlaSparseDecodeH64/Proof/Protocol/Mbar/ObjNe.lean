-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
public import Lemmas.Protocol.UnitReachBlocker
import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

/-! # An mbarrier of a lane past barrier 0 has records

A lane past barrier 0 has a lane of its CTA that won the startup's election and reached
barrier 0 (`InitRows.winner`); that lane initialized every mbarrier of the CTA (`won_inits`), so
each object has its initialization record (`objects_ne`). A blocked poll's object then has a
final state (`Unit.final_of_init`, `Notify.Obj.final`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The CTA's mbarriers have records** once a lane of the CTA is past barrier 0. -/
theorem objects_ne (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hI : InitRows L X) {g k : Nat} (hg : g < L.threads)
    (hpass : k < (X.tr g).length ∨ (k = (X.tr g).length ∧ Step.Released L X g))
    (hb0 : 0 < ((X.tr g).take k).countP isBar0) (f : MbarFam) :
    X.objects (mbarLoc L (g / L.block) f) ≠ [] := by
  obtain ⟨g0, j0, kb, mk, inst, pcb, cnt, mode, hcg, hj, hb, h0j, h0b⟩ := hI.winner hg hpass hb0
  obtain ⟨i, -, pci, hgi⟩ := won_inits hp hX hFw hj rfl hb h0j h0b f
  rw [hcg] at hgi
  obtain ⟨_, r, hr0, -⟩ := init_record_of_actual_get hX hgi
  intro hnil
  rw [hnil] at hr0
  simp at hr0

/-- **An mbarrier of the CTA of a lane past barrier 0 has a final state**: its history starts
with its one initialization and holds no invalidation. -/
theorem objects_final (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    {g k : Nat} (hg : g < L.threads)
    (hpass : k < (X.tr g).length ∨ (k = (X.tr g).length ∧ Step.Released L X g))
    (hb0 : 0 < ((X.tr g).take k).countP isBar0) (f : MbarFam) :
    ∃ st, MBarrier.stateBefore (X.objects (mbarLoc L (g / L.block) f))
      (X.objects (mbarLoc L (g / L.block) f)).length = some st := by
  obtain ⟨-, -, ho, -⟩ := hX.tma
  exact MbarRing.Unit.final_of_init hX (initFirst hp hX hFw hR hI hB _ f)
    (AsyncCopy.objects_noInval ho (no_inval hX hR) _) (objects_ne hp hX hFw hI hg hpass hb0 f)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

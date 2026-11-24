-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Score

@[expose] public section

/-! # The load part of `SourceSafe`, per load

Every Tensor Memory load is a softmax or a correction thread's (`ScoreFacts.tc_role`). Each
register of a softmax load reads a source of its cell: the last QK MMA of the tile that wrote it
(`SoftLoadSources`, from `Score.s_readSource`); each register of a correction load the last
writer of its accumulator cell, a PV MMA of the previous tile or the correction's own rescale
store (`CorrLoadSources`, from `OAcc.o_readSource`). So every loaded register has a supported
source with a written value (`tc_supported`, the load clause of `TcMma.sourceSafe_iff`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX TcMma

noncomputable section

variable {L : Launch} {X : Execution}

/-- Each register of a softmax load has a source of its cell, with a written value. -/
def SoftLoadSources (L : Launch) (X : Execution) : Prop :=
  ∀ h i a vals j, h < L.threads → warpOf L h < 8 → X.TLd (h, i) a vals .s32x32b → j < vals.length →
    ∃ src value, ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L asms X src (tcDataCell32 L h a j) value

/-- Each register of a correction load has a source of its cell, with a written value. -/
def CorrLoadSources (L : Launch) (X : Execution) : Prop :=
  ∀ h i a vals j, h < L.threads → 8 ≤ warpOf L h → warpOf L h < 12 → X.TLd (h, i) a vals .s32x32b →
    j < vals.length → ∃ src value, ReadSource L X .ld src (h, i) (tcDataCell32 L h a j) ∧
      Wrote L asms X src (tcDataCell32 L h a j) value

/-- **Every loaded register has a source with a written value.** -/
theorem tc_supported (ht : ScoreFacts L X) (hs : SoftLoadSources L X)
    (hc : CorrLoadSources L X) :
    ∀ e j cell, LoadCell L X e j cell →
      ∃ source value, ReadSource L X .ld source e cell ∧ Wrote L asms X source cell value := by
  rintro ⟨h, i⟩ j cell hcell
  obtain ⟨a, vals, hld, hj, rfl⟩ := ht.loadCell hcell
  obtain ⟨hh, h12⟩ := ht.tc_role (.inl hld)
  by_cases h8 : warpOf L h < 8
  · exact hs h i a vals j hh h8 hld hj
  · exact hc h i a vals j hh (by omega) h12 hld hj

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety

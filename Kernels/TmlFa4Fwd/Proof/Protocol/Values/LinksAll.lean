-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.CorrLink
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LseStore
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Open
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.OutSource
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatVals
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.SoftStats
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatReadsAll
import Lemmas.Kernel.FrameEnd
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The links and the stored values of a complete execution, for the traced row data

With the row data of the softmax lanes' traces (`softRow`), the correction lanes' links, the final
stores and the log-sum-exp stores of a complete execution are proved from two facts of the softmax
lanes: `SoftLink`, and that the maximum of a valid row is finite (`RowFinite`). `outputLinks` and
`lseLinks` are the open parts of the two result items. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The row maximum of a valid row is finite.** -/
def RowFinite (p : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {h : Nat} {t : Tile}, h < L.threads → Prologue.warpIndex L h < 8 →
    tileOf p L (h / L.block) = some t → t.Valid p (Prologue.warpIndex L h / 4) (rowIx L h) →
    softMaxFinite p L X h = true

/-- **A factor's word reads as the factor** on the correction data machine. -/
theorem scaleReads_of_words {D : Nat → RowData} (h : ScaleWords L X D) : ScaleReads L X D := by
  intro g i u st a bs hg h8 h12 he hu
  obtain ⟨w, hw, hr⟩ := h hg h8 h12 he hu
  rcases hw with rfl | ⟨rfl, hx⟩
  · exact ⟨.num _, hr, rfl⟩
  · exact ⟨.one, hr, hx.symm⟩

/-- A complete execution has no undefined behaviour event: its lanes end with exits. -/
theorem noUb_of_complete (hX : Consistent L kernel Assumptions.all m X) (hD : Complete L X) :
    ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  obtain ⟨j, pc', hj, hx⟩ := Frame.Complete.exit_last hD (Frame.lt_of_get hX he) (by
    rintro ⟨-, request, h⟩
    obtain ⟨i, s, ts, -, hi, -⟩ := hX.clc.canceled_has_issue h
    exact noClcIssue hX hi)
  have h1 := ub_last hX he hx
  have h2 : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1
  obtain rfl : j = k := by omega
  rw [he] at hx
  cases hx

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hD : Complete L X) (hS : SoftLink p L X (tileOf p L) (softRow p L X))
include hp hX hFw

/-- Every Tensor Memory load returned numbers. -/
private theorem loads {e : EvId} {a : Nat} {vals : List Value} (hl : X.TLd e a vals .s32x32b) :
    F32s vals :=
  loads_f32 hp hX hFw (softFacts hp hX hFw) hl

include hD hS in
/-- **The lanes' links** of a complete execution, from the softmax lanes'. -/
theorem laneLinks (hF : RowFinite p L X) : LaneLinks p L X (softRow p L X) where
  soft := hS
  corr := corrLink hp hX hFw (loads hp hX hFw)
    (scaleReads_of_words (scaleWords hp hX hFw (softStats hp hX hFw (loads hp hX hFw) hF)))
    (noUb_of_complete hX hD) hD

include hD hS in
private theorem rows (hF : RowFinite p L X) : RowSums p (tileOf p L) L (softRow p L X) :=
  rowSums hp hX hFw ((laneLinks hp hX hFw hD hS hF).links hp hX hFw
    (inputsUnwritten hp (Top.noInputWrite hp hX hFw)))

include hD hS in
/-- **The open part of the output tile values.** -/
theorem outputLinks (hF : RowFinite p L X) : ∃ D, LaneLinks p L X D ∧
    FinalVals p L X (tileOf p L) D :=
  ⟨_, laneLinks hp hX hFw hD hS hF, final_vals hp hX hFw (statReads hp hX hFw) (loads hp hX hFw)
    (statVals hp hX hFw (softStats hp hX hFw (loads hp hX hFw) hF)) (rows hp hX hFw hD hS hF)⟩

include hD hS in
/-- **The open part of the log-sum-exp values.** -/
theorem lseLinks (hF : RowFinite p L X) : ∃ D, LaneLinks p L X D ∧
    LseVals p L X (tileOf p L) D :=
  ⟨_, laneLinks hp hX hFw hD hS hF, lse_vals hp hX hFw (statReads hp hX hFw) (loads hp hX hFw)
    (statVals hp hX hFw (softStats hp hX hFw (loads hp hX hFw) hF)) (rows hp hX hFw hD hS hF)⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values

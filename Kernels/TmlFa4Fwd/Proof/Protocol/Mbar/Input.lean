-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Input
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mbar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The kernel's tensor copies

Every tensor copy of an execution is a loader lane's decoded copy (`input_box`), of 16384 bytes
(`input_bytes`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A tensor copy is a loader lane's decoded copy.** -/
theorem input_box (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩) :
    (Prologue.warpIndex L i.1 = 14 ∨ Prologue.warpIndex L i.1 = 15) ∧
      ∃ j org mb, a = Loader.inputMapAddress p (Loader.inputSite j) ∧
        s = inputSpec p L (i.1 / L.block) j org mb := by
  obtain ⟨h, k⟩ := i
  have hm : MbarOf ⟨pc, .tensorIssue a s⟩ s.mbar := rfl
  have hni : ∀ c, (⟨pc, .tensorIssue a s⟩ : Event).kind ≠ .mbInit s.mbar c :=
    fun _ h => by cases h
  have h16 := Prologue.warpIndex_lt hp h
  rcases show Prologue.warpIndex L h < 8 ∨
      (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) ∨ Prologue.warpIndex L h = 12 ∨
      Prologue.warpIndex L h = 13 ∨
      (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) by omega with
    hw | hw | hw | hw | hw
  · rcases soft_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk
  · rcases corr_mbar_use hp hX hFw hw.1 hw.2 he hm hni with ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;>
      cases hk
  · rcases mma_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk, _⟩ <;>
      cases hk
  · rcases epi_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, hk, _⟩ | ⟨_, _, hk, _⟩ <;> cases hk
  · exact ⟨hw, ld_input hp hX hFw hw he⟩

/-- The box of an input map: 64 columns of 128 rows of two-byte elements, swizzled by 128 bytes. -/
theorem input_map (p : Params) (j : Fin 14) :
    TensorTile.count (Loader.inputMap p (Loader.inputSite j)).box 0 = 64 ∧
      TensorTile.rows (Loader.inputMap p (Loader.inputSite j)).box = 128 ∧
      (Loader.inputMap p (Loader.inputSite j)).format = .bf16 ∧
      (Loader.inputMap p (Loader.inputSite j)).swizzle = .b128 ∧
      (Loader.inputMap p (Loader.inputSite j)).fill = .zero := by
  simp only [Loader.inputMap]
  split <;> refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;>
    simp [Params.biasMap, Params.qMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step]

/-- **A tensor copy transfers 16384 bytes.** -/
theorem input_bytes (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩) :
    TensorTransfer.bytes s.descriptor = 16384 := by
  obtain ⟨-, j, org, mb, -, rfl⟩ := input_box hp hX hFw he
  obtain ⟨h1, h2, h3, -, -⟩ := input_map p j
  have e : TensorTransfer.bytes (Loader.inputMap p (Loader.inputSite j)) = 16384 := by
    unfold TensorTransfer.bytes
    rw [h1, h2, h3]
    rfl
  exact e

end
end PTX.Kernels.TmlFa4Fwd.Proof

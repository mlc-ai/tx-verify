-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
public import Kernels.TmlFa4Fwd.Proof.LoaderSourceLayout
public import Kernels.TmlFa4Fwd.Proof.OutputFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Once the recurring pointer words are supplied, the issued copy uses a cache address
whose entire live byte span is initialized by the launch. The decoded zero page is also backed. -/
theorem recurringFirstCopyBackedByPointer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hFrame : OutputFootprint p X)
    {g batch head row tid : Nat} (hb : batch < p.batch)
    (hh : head < p.kvHeads) (hTid : tid < 512) (site : Fin 4) (upper : Bool)
    {s : TState} {es : List Event} {vs : List Visit} {sp : AsyncCopy.Spec}
    (hs : At s (recurringSourceStart site) (recurringSourceInputs site
      ((recurringCache p site).loc (primingScratchPage p batch row) head (row % 16) 0).addr tid))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : ⟨packetPlanePc (recurringPacketSite site) 0 upper, .copy sp⟩ ∈
      loaderSliceEvents (recurringSourceStart site) (copyCommitPc (recurringPacketSite site)) vs)
    (hSize : sp.src.size ≤ 16) :
    let layout := recurringCache p site
    sp.src.loc = layout.loc (primingScratchPage p batch row) head (row % 16)
        (kvCopyColumn tid upper) ∧
      ∀ k < sp.src.size,
        (layout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
        (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  let layout := recurringCache p site
  let page := primingScratchPage p batch row
  let r := row % 16
  let col := kvCopyColumn tid upper
  have hPage : page < p.pages := primingScratchPageBound hp hb
  have hr : r < 16 := Nat.mod_lt _ (by decide)
  have hLayout : layout.region p.pages p.kvHeads ∈ p.inputRegions := by
    dsimp [layout, recurringCache]
    split <;> simp [Params.inputRegions]
  have hSource := recurringFirstCopySourceLayoutFromSavedRow hp hb hh hTid site upper hs hw hSeen
  refine ⟨hSource, ?_⟩
  intro k hk
  have hByte := kvCopyColumn_byte_lt (lane := tid) upper (show k < 16 by omega)
  rw [hSource]
  have hRegion := CacheLayout.loc_copy_in_region (c := layout) hPage hh hr hByte
  have hBytes := hp.kvBytes page hPage head hh r hr (col + k / 2) hByte
  have hInit : ∃ value, m ((layout.loc page head r col).at k) = some (some value) := by
    rw [layout.loc_copy_byte]
    have hByte16 : k % 2 < 2 := Nat.mod_lt _ (by decide)
    dsimp [layout, recurringCache]
    split
    · exact ⟨_, hBytes.1 _ (by simp [Value.bytes, FloatFmt.bytes]; omega)⟩
    · exact ⟨_, hBytes.2 _ (by simp [Value.bytes, FloatFmt.bytes]; omega)⟩
  exact ⟨hRegion, hInit, fun w a data hw => hFrame.input_unwritten hp hLayout hRegion hw⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

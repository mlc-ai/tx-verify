-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.TcMmaThread

@[expose] public section

/-! # The MMA instruction branch of `Unsafe` and the MMA read sources

Every MMA has the issue shape its site's template checks (`TcFacts.mma_shape`: the `kind::f16`
instruction descriptors of the QK and PV MMAs, M = 256 over the pair, the 128-byte swizzled
shared descriptors, the A address of a PV MMA in its column field, zero lane masks), the kernel
has no copy (`ScoreFacts.no_cp`), and no MMA reuses a collector buffer (`hcol`). The completed
MMAs' values are the value protocols' (`MmaValues`).

The accumulator and A sources of the completed MMAs (`AccSources`, `ASources`) are the
accumulator and A clauses of the read-source check `TcMma.SourceSafe` (`sources_acc_a`, by
`TcMma.sourceSafe_iff`). `ASources` follows from `PvAStores`, the existence of the A operand's
stores: the A operand of a completed PV MMA of tile `u` is read from the softmax stores of tile
`u` (a store of the tile to the cell, with the value it wrote and live until the read), and every
other write of the cell is ordered with the read (`Score.p_aReadSource`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof TcMma

noncomputable section

variable {L : Launch} {X : Execution}

/-- **MmaValues**: every completed MMA's unmasked results have values. -/
def MmaValues (L : Launch) (X : Execution) : Prop :=
  ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → CompletedValues L asms X i

/-- **AccSources**: every accumulator read of a completed MMA has a read source with a value. -/
def AccSources (L : Launch) (X : Execution) : Prop :=
  ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → X.async.mmaDone i = true → ∀ cell, X.MmaReadCell i cell →
      ∃ source value, ReadSource L X .acc source i cell ∧ Wrote L asms X source cell value

/-- **ASources**: every A byte a completed MMA read from Tensor Memory has a read source with a
value. -/
def ASources (L : Launch) (X : Execution) : Prop :=
  ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → X.async.mmaDone i = true → ∀ cell, X.MmaACell i cell →
      ∃ source value, ReadSource L X .a source i cell ∧ Wrote L asms X source cell value

/-- **PvAStores**: each A cell of a completed PV MMA of tile `u` is written by a softmax store of
tile `u` of the cell's stage, with a value, live until the read. -/
def PvAStores (L : Launch) (X : Execution) : Prop :=
  ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {index pos : Nat}
    {cell : Cell}, X.MmaIssue i d s acc mask → X.async.mmaDone i = true →
    aCell s index = some (cell, pos) →
      ∃ h k a j vals value, h < L.threads ∧ warpOf L h < 8 ∧ X.TSt (h, k) a vals .s32x32b ∧
        j < vals.length ∧ cell = tcDataCell32 L h a j ∧
        sPolls L X h (warpOf L h / 4) k = pPolls L X i.1 (warpOf L h / 4) i.2 ∧
        Wrote L asms X (h, k) cell value ∧ SourceLive L X (h, k) i cell

/-- **No MMA instruction is unsafe.** -/
theorem no_instruction_unsafe (ht : ScoreFacts L X) (htc : TcFacts L X)
    (htt : TcMmaThreadFacts L X) (hmv : MmaValues L X) : ¬ InstructionUnsafe L asms X := fun hn =>
  hn ⟨fun _ _ _ _ _ hi => ⟨htc.mma_shape hi, hmv hi⟩,
    fun _ _ hcp => absurd hcp (ht.no_cp _ _),
    TcMma.collectorSafe_of_noReuse fun _ _ _ _ _ hu => htt.mma_collector hu⟩

/-- **The accumulator and A clauses of the read-source check** (`TcMma.sourceSafe_iff`). -/
theorem sources_acc_a (has : AccSources L X) (haa : ASources L X) :
    (∀ i cell, X.async.mmaDone i = true → X.MmaReadCell i cell →
      ∃ source value, ReadSource L X .acc source i cell ∧ Wrote L asms X source cell value) ∧
    (∀ i cell, X.async.mmaDone i = true → X.MmaACell i cell →
      ∃ source value, ReadSource L X .a source i cell ∧ Wrote L asms X source cell value) :=
  ⟨fun _ cell hd hc => by
      obtain ⟨d, s, mask, row, col, hi, -⟩ := id hc
      exact has hi hd cell hc,
    fun _ cell hd hc => by
      obtain ⟨d, s, acc, mask, index, b, hi, -⟩ := id hc
      exact haa hi hd cell hc⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety

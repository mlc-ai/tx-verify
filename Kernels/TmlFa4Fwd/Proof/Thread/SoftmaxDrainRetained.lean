-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainSelectedRetire
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalPublicationCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainRecordedKeep
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxLaneRegister

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Correction

private theorem terminalSiteFloor {floor : Nat} (hf : 7617 ≤ floor) :
    ∀ pc ∈ Assumptions.swExp2Sites, pc < floor := by
  intro pc hm
  exact (of_decide_eq_true (List.all_eq_true.mp noSegmentsInDrain pc hm)).trans_le hf

/-- The actual post-publication parity and launch operands survive the entire
scheduler search, including every taken group backedge. -/
theorem terminalRetainedAtComparison {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g parity : Nat} {warp : Fin 8} {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g 7617 (terminalRetained l warp parity))
    (u : OpeningTripCursor l X g 7720 F) :
    Holds u.ready.regs (terminalRetained l warp parity) := by
  let span : RowDrainSpan := ⟨7617,7721,7721⟩
  apply span.recordedKeep hp (by decide) (by decide) (by decide) rfl
    (terminalSiteFloor (by decide)) (terminalSiteFloor (by decide)) _ _ _ _ c u
  · set_option maxRecDepth 100000 in kernel_rfl
  · apply span.segmentKeeps_of_audit
    rfl
  · set_option maxRecDepth 100000 in decide +kernel
  · set_option maxRecDepth 100000 in decide +kernel

/-- The count produced by the first group's down shuffle is still present after its
five prefix shuffles and total broadcast. -/
theorem terminalFirstCountAtTotal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g : Nat} {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g 7642 [(7262,b32 (groupLaneTiles p 0 (laneOf l g)))])
    (u : OpeningTripCursor l X g 7658 F) :
    Holds u.ready.regs [(7262,b32 (groupLaneTiles p 0 (laneOf l g)))] := by
  let span : RowDrainSpan := ⟨7642,7659,7659⟩
  apply span.recordedKeep hp (by decide) (by decide) (by decide) rfl
    (terminalSiteFloor (by decide)) (terminalSiteFloor (by decide)) _ _ _ _ c u
  · set_option maxRecDepth 100000 in kernel_rfl
  · apply span.segmentKeeps_of_audit
    rfl
  · set_option maxRecDepth 100000 in decide +kernel
  · set_option maxRecDepth 100000 in decide +kernel

end PTX.Kernels.TmlFa4Fwd.Softmax

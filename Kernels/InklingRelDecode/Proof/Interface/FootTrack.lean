-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixTrack

@[expose] public section

/-!
# `Good` at a whole prefix of a thread

A value fact about a shared word (`NumWordRead`, `BaseWordRead`, `RoleReads`) is a fact about the
source of a read, whose own value depends on its thread's earlier loads. `GoodP e` says `Good` at
every event of `e`'s thread up to `e` (`goodP_of_tracked` proves it at every event).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Good` at every event of the thread up to `e`.** -/
def GoodP (Q : Params) (L : Launch) (mem0 : Mem0) (X : Execution) (e : EvId) : Prop :=
  ∀ j ≤ e.2, Good Q L mem0 X (e.1, j)

theorem GoodP.good {e : EvId} (h : GoodP Q L mem0 X e) : Good Q L mem0 X e := h e.2 le_rfl

theorem GoodP.before {e : EvId} (h : GoodP Q L mem0 X e) {j : Nat} (hj : j ≤ e.2) :
    Good Q L mem0 X (e.1, j) := h j hj

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Objects

@[expose] public section

/-! # The startup's mbarrier initializations: vocabulary

The startup's elected lane of warp 0 initializes the 23 mbarriers in program order
(`MbarFam.ofInit j` is the `j`-th), and the thread's events on CTA barrier 0 and its mbarrier
initializations are counted by `isBar0` and `isMbInit` (prefix counts of `(X.tr g).take k`). The
rows that use them are `Startup/Export/Mbar.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- The family the `j`-th initialization of the startup initializes. -/
def MbarFam.ofInit (j : Fin 23) : MbarFam :=
  [.lastStoreDone, .qTma, .qUtccp, .dequantReady 0, .rawReady 0, .rawFree 0, .qkDone 0,
    .soReady 0, .svDone 0, .dequantReady 1, .rawReady 1, .rawFree 1, .qkDone 1, .soReady 1,
    .svDone 1, .coordReady 0, .coordFree 0, .coordReady 1, .coordFree 1, .coordReady 2,
    .coordFree 2, .coordReady 3, .coordFree 3].getD j.val .lastStoreDone

/-- Every family is initialized by exactly one initialization of the order. -/
theorem MbarFam.ofInit_bij (f : MbarFam) : ∃ j, MbarFam.ofInit j = f ∧
    ∀ j', MbarFam.ofInit j' = f → j' = j := by
  have h : ∀ f ∈ MbarFam.all, ∃ j, MbarFam.ofInit j = f ∧
      ∀ j', MbarFam.ofInit j' = f → j' = j := by decide
  exact h f (MbarFam.mem_all f)

/-- An event on CTA barrier 0. -/
def isBar0 (e : Event) : Bool := match e.kind with | .bar 0 _ _ => true | _ => false

/-- An mbarrier initialization. -/
def isMbInit (e : Event) : Bool := match e.kind with | .mbInit _ _ => true | _ => false

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Proof.CuQReadBytes
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

/-- Agreement for reads of one endpoint made by one particular thread. -/
def CuQWordReadsFromLaunchOnThread (p : Params) (X : Execution) (g index : Nat) : Prop :=
  ∀ position bytes,
    X.Reads (g, position) {loc := globalLoc (p.cuQBase + 4 * index), size := 4} bytes →
    bytes = (b32 (p.qOffset index)).toBytes.map some

/-- Agreement for all in-range endpoint reads made by one particular thread. -/
def CuQReadsFromLaunchOnThread (p : Params) (X : Execution) (g : Nat) : Prop :=
  ∀ index ≤ p.batch, CuQWordReadsFromLaunchOnThread p X g index

/-- Agreement for the endpoint reads of the lanes in the warp containing `g`. -/
def CuQReadsFromLaunchInWarp (p : Params) (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ lane < 32, CuQReadsFromLaunchOnThread p X (warpLane l g lane)

theorem CuQWordReadsFromLaunch.onThread {p : Params} {X : Execution} {index : Nat}
    (hReads : CuQWordReadsFromLaunch p X index) (g : Nat) :
    CuQWordReadsFromLaunchOnThread p X g index :=
  fun pos => hReads (g, pos)

theorem CuQReadsFromLaunch.onThread {p : Params} {X : Execution}
    (hReads : CuQReadsFromLaunch p X) (g : Nat) : CuQReadsFromLaunchOnThread p X g :=
  fun index hi => (hReads index hi).onThread g

theorem CuQReadsFromLaunch.inWarp {p : Params} {l : Launch} {X : Execution}
    (hReads : CuQReadsFromLaunch p X) (g : Nat) : CuQReadsFromLaunchInWarp p l X g :=
  fun lane _ => hReads.onThread (warpLane l g lane)

end PTX.Kernels.TmlFa4Fwd.Epilogue

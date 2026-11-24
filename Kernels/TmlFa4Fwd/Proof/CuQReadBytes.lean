-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.ReadValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof

/-- Each actual scalar read of this cumulative query offset returns its launch bytes. -/
def CuQWordReadsFromLaunch (p : Params) (X : Execution) (index : Nat) : Prop :=
  ∀ i bs, X.Reads i {loc := globalLoc (p.cuQBase + 4 * index), size := 4} bs →
    bs = (b32 (p.qOffset index)).toBytes.map some

/-- Byte agreement at ordinary reads of in-range cumulative query offsets. -/
def CuQReadsFromLaunch (p : Params) (X : Execution) : Prop :=
  ∀ index ≤ p.batch, CuQWordReadsFromLaunch p X index

theorem cuQWordReadsFromLaunchOfProtected {A : List Assumption}
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel A m X) {index : Nat} (hi : index ≤ p.batch)
    (hProtect : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * index)).at k)) :
    CuQWordReadsFromLaunch p X index := by
  intro i bs hRead
  have hMem : X.MemReads (.thread i)
      {loc := globalLoc (p.cuQBase + 4 * index), size := 4} bs := .inl hRead
  exact hX.launch_value hMem rfl hProtect (hp.cuQ index hi)

end PTX.Kernels.TmlFa4Fwd.Epilogue

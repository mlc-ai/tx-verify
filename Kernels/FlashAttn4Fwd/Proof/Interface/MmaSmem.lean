-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings

@[expose] public section

/-! # What the thread layer exports for the MMAs' shared-memory descriptors

The MMA warp builds every shared-memory descriptor from a low word and the fixed high word
`0x40004040` (`Mma.desc`, `Mma.descHi`): version 1, stride 1024 bytes (eight 128-byte rows),
base offset 0, 128-byte swizzle. The low words are those of the value table (`Mma.qVals`,
`Mma.asmVals`):

* **QK MMA `j` of a block** (`j < 8`, A in shared memory, K-major A and B, `Mma.qkIdesc`): A is
  `fa_fwd_q_smem_desc_j`, Q stage `st` at `Mma.qLo` plus `2 j` (`j < 4`) or `1024 + 2 (j - 4)`:
  box `j / 4` of the stage, head-dimension columns `16 (j % 4)` on (`qStepStart`); B is
  `smem_desc_b_j`, an even KV slot `sl` at `Mma.kLo` plus `2 j` or `512 + 2 (j - 4)`
  (`kStepStart`). Both low words carry the leading-offset field 1 (16 bytes, which the swizzled
  K-major layout ignores): `kMajorDesc`.
* **PV MMA `j` of a block** (A in Tensor Memory, MN-major B, `Mma.pvIdesc`): B is an odd KV slot
  `sl` at `Mma.vLo` plus `128 j`: key rows `16 j` on of the slot's V box (`vStepStart`), leading
  offset 0: `mnMajorDesc`.

These are facts of single threads (the MMA sites' registers, from the MMA warp's run invariant
and value table, `Mma.qk_isMma`, `Mma.pv_isMma`); which stage and slot an MMA names, and which
use of it, is the rings' business (`Rings.read_source`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The MMA warp's K-major shared descriptor (Q, K) starting at `start`. -/
def kMajorDesc (start : Nat) : TcShared.Descriptor := ⟨start, 16, 1024, 0, false, false, .b128⟩

/-- The MMA warp's MN-major shared descriptor (V) starting at `start`. -/
def mnMajorDesc (start : Nat) : TcShared.Descriptor := ⟨start, 0, 1024, 0, false, false, .b128⟩

/-- The start of K step `j` of Q stage `st`: box `j / 4`, head-dimension columns `16 (j % 4)`
on. -/
def qStepStart (L : Launch) (st : Fin 2) (j : Nat) : Nat :=
  L.sharedBase + (FBar.qFull st).regionOff + 16384 * (j / 4) + 32 * (j % 4)

/-- The start of K step `j` of the K block in KV slot `sl`: box `j / 4`, head-dimension columns
`16 (j % 4)` on. -/
def kStepStart (L : Launch) (sl : Fin 6) (j : Nat) : Nat :=
  L.sharedBase + (FBar.kvFull sl).regionOff + 8192 * (j / 4) + 32 * (j % 4)

/-- The start of K step `j` of the V block in KV slot `sl`: key rows `16 j` on. -/
def vStepStart (L : Launch) (sl : Fin 6) (j : Nat) : Nat :=
  L.sharedBase + (FBar.kvFull sl).regionOff + 2048 * j

/-- The thread layer's facts of the MMAs' shared-memory descriptors. -/
structure MmaSmemFacts (L : Launch) (X : Execution) : Prop where
  /-- A QK MMA (A in shared memory) is K step `j` of a Q stage and of the K block of an even KV
  slot. -/
  qk : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → s.aTmem = none →
      ∃ (st : Fin 2) (sl : Fin 6) (j : Fin 8), sl.val % 2 = 0 ∧
        s.a = kMajorDesc (qStepStart L st j) ∧ s.b = kMajorDesc (kStepStart L sl j)
  /-- A PV MMA (A in Tensor Memory) is K step `j` of the V block of an odd KV slot. -/
  pv : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → s.aTmem.isSome = true →
      ∃ (sl : Fin 6) (j : Fin 8), sl.val % 2 = 1 ∧ s.b = mnMajorDesc (vStepStart L sl j)

end
end PTX.Kernels.FlashAttn4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

namespace PTX.Tmem.Pair

/-! ## MEM-TMEM-RESULT-HANDOFF — actual participants and bytes of the allocation result
Statement: The local handoff relates the allocation instruction's representative result store
  to an ordinary load of the same byte by one of the instruction's participants.

Defs:
  Tmem.Pair.AllocResult, Tmem.Pair.AllocResultBefore

Source:
- EXT-TMEM-ALLOC-RESULT-ORDER

Direction: reading

Applies: Ordinary shared-memory loads by a lane of an allocating warp.

Premises: Matching warp lane events name the same allocation instance. The representative
  four-byte store and the later load cover the byte.

Effect: Supplies the local result-write node of DEP-ORDER and the byte edge of
  MEM-MODEL-CAUSALITY.
-/

/-!
### EXT-TMEM-ALLOC-RESULT-ORDER — visibility of a warp's local allocation result
Statement: The weak allocation result write precedes a subsequent ordinary read of the same byte
  by a lane participating in that allocation.

Source:
- §9.7.18.6.1: "maintain same-address ordering"
- §9.7.18.7.1: "tcgen05.alloc is a blocking instruction"
- §9.7.18.7.1: "writes the address of the allocated Tensor Memory into shared memory"
- §9.7.18.7.1 (Example 1): "tcgen05.alloc.cta_group::1.sync.aligned.shared::cta.b32 [sMemAddr1], 32;
    ld.shared.b32 taddr, [sMemAddr1];"

Direction: reading

Applies: The allocating warp's local shared write and its participating lanes' later ordinary
  reads, for both CTA group sizes.

Premises: The leader and reading lane issue the same allocation instance, identified by matching
  collective ordinals and operands in one warp. The leader's next event writes the four-byte
  result. The reading lane has a later ordinary read covering a byte of that result.

Effect: The result write precedes the read at the overlapping byte in `modelCausality`. A
  nonleader's return depends on the actual local result write. The leader can emit the write
  once the resource operation is ready.

Why it is not spec text: The manual gives a blocking warp instruction, its same-address
  behavior, and an immediate readback example. It does not express cross-lane ordering for a
  trace representation that splits the warp instruction from a single representative weak
  store. The readback example motivates a local byte edge rather than a warp-wide memory fence.
  Disclosed by every kernel whose statement names `Op.tcAlloc`: FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, TcGemm.
-/

/-- The local result store immediately after the leader's half of the same
allocation as the participating event `i`. The collective ordinal distinguishes
repeated executions of the same instruction. -/
def AllocResult (L : Launch) (X : Execution) (store i : EvId) (dst : Loc) : Prop :=
  SameWarp L store.1 i.1 ∧ laneOf L store.1 = 0 ∧
    dst.space = .shared ∧ dst.cta = i.1 / L.block ∧
    ∃ j site group n k bytes,
      store.2 = j + 1 ∧
      X.get (store.1, j) = some ⟨site, .tc (.resource group (some dst) (.alloc n))⟩ ∧
      X.get i = some ⟨site, .tc (.resource group (some dst) (.alloc n))⟩ ∧
      X.TcK (store.1, j) k ∧ X.TcK i k ∧
      X.get store = some ⟨site, .wr { loc := dst, size := 4 } bytes⟩

/-- Byte-local handoff from the allocation result to an ordinary load by a
participating lane after that allocation. The handoff is restricted to the
intersection of the load footprint and the four-byte result. -/
def AllocResultBefore (L : Launch) (X : Execution) (l : Loc) (store load : EvId) : Prop :=
  ∃ j dst a bytes, AllocResult L X store (load.1, j) dst ∧ j < load.2 ∧
    dst.InRange 4 l ∧ X.Reads load a bytes ∧ a.Covers l

end PTX.Tmem.Pair

-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma

@[expose] public section

/-! # The coordinate words the TMA lane reads: vocabulary

`CoordWordsBits L X`: every read of the TMA warp's code (the coordinate loads) returns four bytes
that rebuild a 32-bit word (the bytes are those of 32-bit words the index warp stored). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **The TMA warp's reads rebuild 32-bit words.** -/
def CoordWordsBits (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)},
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → MbarRow.TmaAt L g pc →
      ∃ z, rebuild 3 bs = .ok (.bits 32 z)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot

@[expose] public section

/-! # Every source byte of a query copy has a location

A copy `keyDesc B k` of shape `128x256b` has `4096` source bytes, and each has a shared location
(`copy_byteLoc`): the descriptor is a valid K-major 128-byte-swizzled one. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
open PTX

/-- **Source byte `idx < 4096` of copy `k` has a location in CTA `cta`.** -/
theorem copy_byteLoc {B k cta idx : Nat} (hidx : idx < 4096) :
    ∃ l, TcCopy.byteLoc .s128x256b (keyDesc B k) cta idx = some l := by
  have hlt : idx < TcCpShape.s128x256b.sourceBytes := by
    simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]; omega
  unfold TcCopy.byteLoc TcShared.byteAddress
  simp [keyDesc, hlt]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot

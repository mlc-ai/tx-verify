-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexVal

@[expose] public section

/-! # The TMA lane's main-cache test is the block count's

The TMA lane's map choice `isMain d = (block < nmain l0)` (`Tma/Machine.lean`) and the index
warp's block count `ixNmain l0` are the same word: for the lane's length word `lenWA` the main
cache's blocks are `numOrigBlocks (topkLen)`, so a TMA block `r` is a main one iff `r` is below
them (`tma_isMain`). For the TMA role's gather exports. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The unsigned comparison of two small words. -/
theorem scmp_lt_u_W {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    scmp .lt .u (W a) (W b) = decide (a < b) := by
  simp only [scmp, PTX.compare, r32_W ha, r32_W hb, toNat_W (show a < 2 ^ 64 by omega),
    toNat_W (show b < 2 ^ 64 by omega)]
  simp

/-- **A TMA block is a main one iff it is below the main cache's blocks.** -/
theorem tma_isMain (hp : Pre P L m) {d : Tma.D} (h0 : d.l0 = lenWA P L (g / L.block))
    (hL : Tma.LoopOk d) :
    Tma.isMain d = decide (d.cnt.toNat <
      FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) := by
  obtain ⟨-, -, hR, hr, hc, -⟩ := hL
  have hM := nMain_lane hp (c := { l0 := d.l0 }) h0
  have hb := (Index.nMain_bnd d.l0).2.1
  have hn : Tma.nmain d.l0 = W (Index.nMain d.l0) := (eq_W _ : ixNmain d.l0 = _)
  have hr32 : d.cnt.toNat < 2 ^ 32 := by omega
  unfold Tma.isMain
  rw [hn, eq_W d.cnt, scmp_lt_u_W hr32 (by omega)]
  simp only [toNat_W (show d.cnt.toNat < 2 ^ 64 by omega)]
  have : Index.nMain d.l0 = FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g)) := hM
  rw [this]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

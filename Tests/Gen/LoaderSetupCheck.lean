-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Gen.LoaderSetup
public import Kernels.TmlFa4Fwd.Proof2.Loader.Machine

@[expose] public section

/-! # The generated 64-bit and wide entries agree with the loader's hand-written setup

`Tools/machine_gen.py` generates, from the PTX alone, the entries of the registers the loader
warps' setup assigns once (`Tests/Gen/loader_setup.json`: the head division by `mul.hi.s32`, the
page-table and K/V base addresses by `mul.lo.s64`, `shl.b64`, `add.s64` and `cvt.s64.s32`, the
block counts by signed shifts, `min.s32`, `max.s32`, `or.b32`). At every register of the
loader's setup (`Loader.setup`) the generated entry is the hand-written one by `rfl`: the
generator writes `Lemmas/Flow/Arith32Wide.lean`'s vocabulary in the forms the loader closes its
segments with. -/

namespace PTX.Tests.Gen.LoaderSetup
set_option maxRecDepth 100000
open PTX PTX.Kernels.TmlFa4Fwd

/-- The head division (`%r748`). -/
theorem headDiv_setup (p : Params) (L : Launch) (g : Nat) (v : Proof2.Loader.V) (rd : BitVec 64) :
    (headDiv v.co.head rd).lookup 1808 =
      some (.bits 32 (Proof2.Loader.setup p L g v).r748) := rfl

/-- The registers of the setup's rest. -/
theorem setupRest_setup (p : Params) (L : Launch) (g : Nat) (v : Proof2.Loader.V)
    (r21 r22 w259 : BitVec 64) (p106 : Bool) :
    let su := Proof2.Loader.setup p L g v
    let T := setupRest v.co.head su.r748 v.ukw su.r741 (Flow.Arith32.sub32 v.sc.c0 v.sc.c1) r21
      r22 su.rd9 (BitVec.ofNat 64 p.pageTableBase) (BitVec.ofNat 64 p.pageTableStride)
      (BitVec.ofNat 64 p.kLayout.base) (BitVec.ofNat 64 p.kLayout.headStride)
      (BitVec.ofNat 64 p.vLayout.base) (BitVec.ofNat 64 p.vLayout.headStride) w259 p106
    T.lookup 7299 = some (.bits 64 su.rd11) ∧ T.lookup 7300 = some (.bits 64 su.rd12) ∧
      T.lookup 7301 = some (.bits 64 su.rd13) ∧ T.lookup 111 = some (.pred su.p109) ∧
      T.lookup 1811 = some (.bits 32 su.r751) ∧ T.lookup 1815 = some (.bits 32 su.r755) ∧
      T.lookup 114 = some (.pred su.p112) ∧ T.lookup 1818 = some (.bits 32 su.r758) ∧
      T.lookup 1820 = some (.bits 32 su.r760) ∧ T.lookup 1825 = some (.bits 32 su.r765) ∧
      T.lookup 117 = some (.pred su.p115) ∧ T.lookup 1088 = some (.bits 32 su.r28) ∧
      T.lookup 1833 = some (.bits 32 su.r773) ∧ T.lookup 120 = some (.pred su.p118) ∧
      T.lookup 1089 = some (.bits 32 su.r29) ∧
      T.lookup 1090 = some (.bits 32 (Flow.Arith32.max32 su.r29 (Flow.Arith32.i32 0))) ∧
      T.lookup 121 = some (.pred su.p119) ∧ T.lookup 1091 = some (.bits 32 su.r31) ∧
      T.lookup 1092 = some (.bits 32 su.r32) ∧ T.lookup 1838 = some (.bits 32 su.r778) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

end PTX.Tests.Gen.LoaderSetup

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Data.Sites

@[expose] public section

/-! Static audit of the FlashMLA assumptions' scopes: the instruction forms the numeric
assumptions name and the site lists of the pointer and store assumptions, checked against the
decoded program. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit

open PTX
open PTX.Kernels.FlashMlaSparseDecodeH64

/-- The pcs whose floating operation satisfies `f`. -/
def floatSites (f : FloatInstr → Bool) : List Nat :=
  sites fun op => match op with
    | .float i => f i
    | _ => false

/-- The pcs whose conversion satisfies `f`. -/
def cvtSites (f : CvtInstr → Bool) : List Nat :=
  sites fun op => match op with
    | .cvt c => f c
    | _ => false

def isEx2 (i : FloatInstr) : Bool :=
  i.op == .ex2 && i.mode == .approx && i.ty == ⟨.f32, 1⟩

def isDiv (i : FloatInstr) : Bool :=
  i.op == .div && i.mode == .approx && i.ty == ⟨.f32, 1⟩

def isLg2 (i : FloatInstr) : Bool :=
  i.op == .lg2 && i.mode == .approx && i.ty == ⟨.f32, 1⟩

def isMulBf16x2 (i : FloatInstr) : Bool :=
  i.op == .mul && i.ty == ⟨.bf16, 2⟩

def isCvtBf16x2 (c : CvtInstr) : Bool :=
  c.dst == .packed (.float .bf16) 2 && c.src == .float .f32 && c.rnd == some .rn

def isCvtE4m3x2 (c : CvtInstr) : Bool :=
  c.dst == .packed (.float .bf16) 2 && c.src == .packed (.float .e4m3) 2

def isCvtUe8m0x2 (c : CvtInstr) : Bool :=
  c.dst == .packed (.float .bf16) 2 && c.src == .packed (.float .ue8m0) 2

/-- The 34 `ex2.approx.ftz.f32` and the single `div.approx.ftz.f32`. -/
theorem approx_counts :
    (floatSites isEx2).length = 34 ∧ (floatSites isDiv).length = 1 := by
  decide +kernel

/-- The single `lg2.approx.ftz.f32`. -/
theorem lg2_count : (floatSites isLg2).length = 1 := by
  decide +kernel

/-- The 128 `mul.bf16x2`, 144 `cvt.rn.bf16x2.f32`, 128 `cvt.rn.bf16x2.e4m3x2` and 32
`cvt.rn.bf16x2.ue8m0x2`. -/
theorem bf16_counts :
    (floatSites isMulBf16x2).length = 128 ∧
      (cvtSites isCvtBf16x2).length = 144 ∧
      (cvtSites isCvtE4m3x2).length = 128 ∧
      (cvtSites isCvtUe8m0x2).length = 32 := by
  decide +kernel

/-- The 24 `tcgen05.mma` sites are the kernel's `.ws` MMAs. -/
theorem mma_count : (sites fun op => match op with | .tcMma _ => true | _ => false).length = 24 :=
  by decide +kernel

/-- The pointer assumption's sites are exactly the six descriptor additions and the three
tensormap prefetches. -/
theorem pointer_sites : paramPointerSites.length = 9 := by decide

/-- The store-drain assumption covers exactly the four tensor stores. -/
theorem store_sites : tensorStores.length = 4 := by decide

/-- The notification order selects just the final static MMA commit instruction. -/
theorem pv_commit_order_sites :
    Assumptions.pvCommitOrderSites = (sites isTcCommit).drop 2 :=
  Assumptions.pvCommitOrderSites_eq.trans (congrArg (·.drop 2) tcCommit_eq)

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit

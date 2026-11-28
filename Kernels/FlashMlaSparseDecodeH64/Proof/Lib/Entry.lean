-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamObj
public import Lemmas.Flow.Arith32
public import Lemmas.Flow.Arith32Wide
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Arith
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Regs
public import Lemmas.Flow.Code

@[expose] public section

/-! # The registers a role finds at its entry

The startup's ABI prefix (pcs 0–8) leaves the thread's place in the launch in registers that no
instruction writes again: the two parameter objects' generic addresses (`%rd1`, `%rd2`),
`%ctaid.x`, `%ctaid.y`, `%tid.x` and the words the code derives from `%tid.x` (`>> 7`, `& 127`,
`>> 5`, `& 31`). Warpgroup 1's dispatch sets the election masks of the MMA and TMA warps
(pcs 1850–1852, 2162–2164). `entryVal L g r` is the value of register `r` in this table (the word
`0` elsewhere). A fragment whose first state names only these registers takes its facts as
`factsFrom (Flow.live pc) (entryVal L g)`; the fragment before it hands off by the same terms. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- A 32-bit word in a register. -/
abbrev w32 (x : BitVec 64) : Value := .bits 32 x

/-- The thread index as a word. -/
abbrev tw (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (tidOf L g)

/-- The dynamic shared base as a word, as `mov.b32` of the workspace symbol reads it. -/
abbrev sbw (L : Launch) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0))

/-- A 32-bit and a 64-bit field of `param_0`, as the explicit launch's `ld.param` reads them
(`Lib/ParamObj.lean`). -/
abbrev pw (x : Nat) : BitVec 64 := BitVec.ofNat 64 (leNat x 0 4)
abbrev pw8 (x : Nat) : BitVec 64 := BitVec.ofNat 64 (leNat x 0 8)

/-- `%ctaid.y` as a word: the batch row. -/
abbrev r2W (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (ctaidY L g)

/-- **The entry registers**: the launch reads of the ABI prefix and the election masks of
warpgroup 1's dispatch. -/
def entryVals (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(2990, .ptr 64 false (.param (param "1")) 0), (2991, .ptr 64 false (.param (param "0")) 0),
   (459, w32 (BitVec.ofNat 64 (ctaidX L g))), (460, w32 (r2W L g)),
   (461, w32 (tw L g)), (519, w32 (BitVec.ofNat 64 (tidOf L g / 128))),
   (463, w32 (andi (tw L g) 127)), (464, w32 (shru (tw L g) 5)), (466, w32 (andi (tw L g) 31)),
   (792, w32 (i32 0)), (793, w32 (i32 0)), (794, w32 (i32 (-1))),
   (661, w32 (i32 0)), (662, w32 (i32 0)), (663, w32 (i32 (-1)))]

/-- The value of an entry register. -/
def entryVal (L : Launch) (g : Nat) (r : Nat) : Value :=
  ((entryVals L g).lookup r).getD (b32 0)

/-- The register facts of a concrete state of a code machine's state. -/
theorem atD_holds {K : Kernel} {A : List Assumption} {C : Code K A L g} {d : C.D} {t : TState}
    (h : C.AtD d t) : Holds t.regs (C.facts d) := by
  obtain ⟨-, -, -, -, hF⟩ := h
  exact hF

/-- A concrete state at a code machine's state, at a stub's first state of the same pc. -/
theorem atD_stop {K : Kernel} {A : List Assumption} {C : Code K A L g} {d : C.D} {t : TState}
    {pc : Nat} (h : C.AtD d t) (hpc : C.pc d = pc) (hs : C.sub d = 0) (ha : C.acc d = []) :
    t.pc = pc ∧ t.sub = 0 ∧ t.acc = [] ∧ t.fault = none := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨h1.trans hpc, h2.trans hs, h3.trans ha, h4⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

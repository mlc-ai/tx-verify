-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Lemmas.Flow.Arith32Norm

@[expose] public section

/-! # A thread's place in the launch, and the local steps no assumption names

Read from the PTX and the launch only (moved from the old tree's `Proof/Thread/Prologue.lean` and
`Proof/Thread/Wg1Idle.lean`, so that `Proof/` imports nothing of `Proof/`): the thread's CTA,
`%tid.x`, warp and lane, the grid indices, the dynamic shared range, and the steps the
assumption list leaves to Core (integer and address instructions outside the audited
parameter-pointer, shared-pointer and peer-score sites) or takes by the kernel's parameter-pointer
reading (the elected lane's descriptor additions and prefetches, `Assumptions.paramPointers`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000


/-- The thread's CTA. -/
def ctaOf (L : Launch) (g : Nat) : Nat := g / L.block

/-- The thread's linear thread index in its CTA (`%tid.x`). -/
def tidOf (L : Launch) (g : Nat) : Nat := (L.tidOf g).x

/-- The thread's warpgroup (`%tid.x / 128`): the value of the first shuffle. -/
def wgOf (L : Launch) (g : Nat) : Nat := tidOf L g / 128

/-- The thread's warp (`%tid.x / 32`): the value of the second shuffle. -/
def warpOf (L : Launch) (g : Nat) : Nat := tidOf L g / 32

/-- The thread's lane in its warp (`%tid.x % 32`). -/
def laneOf (L : Launch) (g : Nat) : Nat := tidOf L g % 32

/-- `%ctaid.x` of the thread's CTA: the query index of the kernel's `(s_q, b, 1)` grid. -/
def ctaidX (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).x % 2 ^ 32

/-- `%ctaid.y` of the thread's CTA: the batch of the kernel's `(s_q, b, 1)` grid. -/
def ctaidY (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).y % 2 ^ 32

/-- A shared address `off` bytes above the dynamic shared base, as the kernel's 32-bit
registers hold it. -/
def sb (L : Launch) (off : Nat) : Value := b32 (L.sharedBase + off)

/-- The registers read but never written in the program: `%r492` and `%r1257` are packed with
a written word into a `b64` register and discarded when it is unpacked, so their value is
immaterial and the startup does not track it. -/
def skipRegs : List Nat := [950, 1715]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem tidOf_eq (hpre : Pre P L mem0) (g : Nat) : tidOf L g = g % 384 := by
  simp only [tidOf, Launch.tidOf, Dim3.coord, hpre.ntid, hpre.block, Nat.mod_mod,
    Nat.mod_one, Nat.mul_one]

theorem tidOf_lt (hpre : Pre P L mem0) (g : Nat) : tidOf L g < 2 ^ 32 := by
  rw [tidOf_eq hpre]; omega

/-- `%tid.x` of the thread in a `(384, 1, 1)` CTA. -/
theorem tidOf_x_eq (hpre : Pre P L mem0) (g : Nat) : (L.tidOf g).x = g % 384 := by
  simp only [Launch.tidOf, Dim3.coord, hpre.ntid, hpre.block, Nat.mod_mod, Nat.mod_one,
    Nat.mul_one]

/-- The dynamic shared base plus the last byte the kernel addresses is below `2 ^ 32`. -/
theorem sharedBase_lt (hpre : Pre P L mem0) : L.sharedBase + 222952 < 2 ^ 32 := by
  have h := hpre.sharedRange
  rw [← hpre.sharedBase] at h
  unfold sharedBytes at h
  omega


/-- A word of a number, truncated to 32 bits, is the word of the number's low 32 bits (a
`%ctaid` read). -/
theorem truncBits_ofNat_mod (n : Nat) :
    truncBits 32 (BitVec.ofNat 64 n) = BitVec.ofNat 64 (n % 2 ^ 32) := by
  simp only [truncBits, BitVec.toNat_ofNat]
  congr 1
  exact Nat.mod_mod_of_dvd n (by norm_num)

/-- `shr.u32` by `7` of a 32-bit word, as Core's rule computes it: the word of the number divided
by `128` (the warpgroup index of `%tid.x`). -/
theorem shr7_word (a : Nat) (h : a < 2 ^ 32) :
    (if (truncBits 32 (BitVec.ofInt 64 7)).toNat ≥ 32 then 0
      else truncBits 32 (BitVec.ofNat 64 a) >>> (truncBits 32 (BitVec.ofInt 64 7)).toNat) =
    BitVec.ofNat 64 (a / 128) := by
  have h7 : (truncBits 32 (BitVec.ofInt 64 7)).toNat = 7 := by rfl
  rw [h7]
  split
  · omega
  rw [truncBits_ofNat h (by omega)]
  apply BitVec.eq_of_toNat_eq
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Rewrite the launch data a segment's arithmetic reads: the thread's `%tid.x` of a
`(384, 1, 1)` CTA, and the two `%ctaid` components. -/
syntax "launch_norm" term:max : tactic
macro_rules
  | `(tactic| launch_norm $hpre) => `(tactic|
      simp only [ctaidX, ctaidY, ctaOf, tidOf, wgOf, warpOf, laneOf, tidOf_x_eq $hpre,
        Dim3.get, ($hpre).block, Nat.mod_one, Nat.mul_one])

/-- A thread of the `(384, 1, 1)` CTA is in warp 0 to 11. -/
theorem warpOf_lt (hpre : Pre P L mem0) : warpOf L g < 12 := by
  simp only [warpOf, tidOf_eq hpre]; omega

/-- `and.b32 d, a, 127` keeps the low seven bits of `a`. -/
theorem land127 (a : Nat) : a &&& 127 = a % 128 := Nat.and_two_pow_sub_one_eq_mod a 7

/-- **The launch's warpgroup word**: the word the startup's first shuffle returns (lane 0's
`%tid.x / 128`), which the startup's dispatch gates on (`Common/Roles.lean`). -/
abbrev wgW (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (wgOf L g)

/-- **The launch's warp word**: the word the startup's second shuffle and warpgroup 1's head
shuffle return (lane 0's `%tid.x / 32`); warpgroup 0 is entered with it. -/
abbrev warpW (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (warpOf L g)

/-- Lane 0 of a thread's warp has the thread's `%tid.x` less its lane. -/
theorem lane0_tid (hpre : Pre P L mem0) (g : Nat) :
    tidOf L (g - PTX.laneOf L g + 0) = tidOf L g - tidOf L g % 32 := by
  simp only [tidOf_eq hpre, PTX.laneOf, hpre.block]
  omega

/-- Lane 0 of a thread's warp is in the thread's warpgroup. -/
theorem lane0_wg (hpre : Pre P L mem0) (g : Nat) : wgOf L (g - PTX.laneOf L g + 0) = wgOf L g := by
  simp only [wgOf, lane0_tid hpre]
  omega

/-- Lane 0 of a thread's warp is in the thread's warp. -/
theorem lane0_warp (hpre : Pre P L mem0) (g : Nat) :
    warpOf L (g - PTX.laneOf L g + 0) = warpOf L g := by
  simp only [warpOf, lane0_tid hpre]
  omega

/-- The warp word as the code computes it, `shr.u32 %tid.x, 5`. -/
theorem shru_tw (hpre : Pre P L mem0) (g : Nat) :
    Arith32.shru (BitVec.ofNat 64 (tidOf L g)) 5 = warpW L g := by
  rw [Arith32.shru_int (tidOf_lt hpre g) (by decide) (by decide)]
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

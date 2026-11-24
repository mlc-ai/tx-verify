-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadySpillStart
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
public import Kernels.TmlFa4Fwd.Proof.LoaderSourceLayout
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerBroadcastPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- A pair draws from the first or second of the lane's saved pointers. -/
def steadyPairSlot (pair : Fin 16) : Fin 2 := if pair.val < 8 then 0 else 1

def steadyPairShufflePc (value : Bool) (pair : Fin 16) : Nat :=
  if value then
    (![1633, 1642, 1649, 1655, 1661, 1667, 1673, 1679,
       1686, 1692, 1698, 1704, 1710, 1716, 1722, 1728] : Fin 16 → Nat) pair
  else
    (![1470, 1480, 1489, 1497, 1505, 1513, 1521, 1529,
       1538, 1546, 1554, 1562, 1570, 1578, 1586, 1594] : Fin 16 → Nat) pair

def steadyPairShuffleOut (value : Bool) (pair : Fin 16) : Nat :=
  if value then
    (![2200, 2204, 2207, 2209, 2211, 2213, 2215, 2217,
       2221, 2223, 2225, 2227, 2229, 2231, 2233, 2235] : Fin 16 → Nat) pair
  else
    (![2158, 2162, 2165, 2167, 2169, 2171, 2173, 2175,
       2179, 2181, 2183, 2185, 2187, 2189, 2191, 2193] : Fin 16 → Nat) pair

def steadyPairShuffleIn (value : Bool) (pair : Fin 16) : Nat :=
  (pointerSlotReloadRegs (steadySpillSite value) (steadyPairSlot pair)).1

def steadyPairSender (src : Nat) (pair : Fin 16) : Nat :=
  pointerBroadcastLane src + pair.val % 8

def steadyPairSourceCut (value : Bool) (pair : Fin 16) : Nat :=
  steadyPairShufflePc value pair + if value && pair.val == 0 then 5 else 4

/-- Each real steady pair uses two adjacent shuffle words and its subgroup selector. -/
theorem steadyPairShuffleCode (value : Bool) (pair : Fin 16) (word : Fin 2) :
    kernel.code[steadyPairShufflePc value pair + word.val]? = some
      (pointerBroadcastInstr (steadyPairShuffleIn value pair + word.val)
        (steadyPairShuffleOut value pair + word.val) (pair.val % 8)) := by
  cases value <;> fin_cases pair <;> fin_cases word <;>
    (set_option maxRecDepth 100000 in kernel_rfl)

/-- K uses the prelude column. V computes an equivalent wide column on its first vector. -/
def steadyPairColumn (value : Bool) (pair : Fin 16) (tid : Nat) : Nat × Value :=
  if value then
    if pair.val = 0 then (1147, b32 (8 * (tid % 8))) else (7825, b64 (16 * (tid % 8)))
  else (7781, b64 (16 * (tid % 8)))

def steadyPairInputs (value : Bool) (pair : Fin 16) (base tid : Nat) : List (Nat × Value) :=
  [(steadyPairShuffleOut value pair, b32 (base % 2 ^ 32)),
    (steadyPairShuffleOut value pair + 1, b32 (base / 2 ^ 32)), steadyPairColumn value pair tid]

private theorem steadyPointerJoin {base : Nat} (hBase : base < 2 ^ 64) :
    (base % 4294967296 ||| base / 4294967296 * 4294967296 % 18446744073709551616) = base := by
  have hLo : base % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hShift : base / 4294967296 * 4294967296 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hShift, Nat.or_comm, Nat.mul_comm]
  change 2 ^ 32 * (base / 2 ^ 32) ||| base % 2 ^ 32 = base
  rw [← Nat.two_pow_add_eq_or_of_lt hLo]
  omega

set_option maxRecDepth 100000 in
/-- The pack and column add compute the true pre-issue source pointer for any steady vector. -/
theorem steadyPairSourceCore {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (value : Bool) (pair : Fin 16) :
    Seg kernel [] l g (steadyPairSourceCut value pair - (steadyPairShufflePc value pair + 2))
      (steadyPairShufflePc value pair + 2) (steadyPairInputs value pair base tid)
      (steadyPairSourceCut value pair)
      [(packetSrcReg (recurringPacketSite (steadySpillSite value)) pair,
        b64 (recurringSourceAddress base tid))] := by
  have hLo : base % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hHi : base / 4294967296 < 4294967296 := by omega
  have hCol32 : 8 * (tid % 8) < 4294967296 := by omega
  have hCol64 : 16 * (tid % 8) < 18446744073709551616 := by omega
  have hTwice : 8 * (tid % 8) * 2 = 16 * (tid % 8) := by omega
  cases value <;> fin_cases pair <;> intro s hs <;>
    simp only [steadyPairSourceCut, steadyPairShufflePc, steadyPairInputs, steadyPairShuffleOut,
      steadyPairColumn, recurringPacketSite, steadySpillSite, packetSrcReg, recurringSourceAddress,
      Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and,
      Nat.reduceEqDiff] at hs ⊢ <;>
    seg_fp hs using
      norm_bits [steadyPointerJoin hBase, Nat.mod_eq_of_lt hCol32, Nat.mod_eq_of_lt hCol64, hTwice]

end
end PTX.Kernels.TmlFa4Fwd.Loader

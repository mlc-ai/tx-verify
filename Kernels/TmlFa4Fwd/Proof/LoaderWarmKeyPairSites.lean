-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmShuffleFloor
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
public import Kernels.TmlFa4Fwd.Proof.LoaderSourceLayout
public import Kernels.TmlFa4Fwd.Proof.OutputFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def warmKShufflePc (pair : Fin 16) : Nat :=
  (![1004, 1015, 1024, 1032, 1040, 1048, 1056, 1064,
     1073, 1081, 1089, 1097, 1105, 1113, 1121, 1129] : Fin 16 → Nat) pair

def warmKShuffleInput (pair : Fin 16) : Nat := if pair.val < 8 then 1998 else 2019

def warmKShuffleOutput (pair : Fin 16) : Nat :=
  (![2000, 2004, 2007, 2009, 2011, 2013, 2015, 2017,
     2021, 2023, 2025, 2027, 2029, 2031, 2033, 2035] : Fin 16 → Nat) pair

def warmKShuffleSender (src : Nat) (pair : Fin 16) : Nat :=
  pointerBroadcastLane src + pair.val % 8

def warmKSourceCut (pair : Fin 16) : Nat := warmKShufflePc pair + if pair.val = 0 then 5 else 4

def warmKNextShuffleCut (pair : Fin 16) : Nat :=
  (![1016, 1025, 1033, 1041, 1049, 1057, 1065, 1074,
     1082, 1090, 1098, 1106, 1114, 1122, 1130, 1240] : Fin 16 → Nat) pair

/-- All warm K pairs use an adjacent pair of shuffles with one common subgroup selector. -/
theorem warmKShuffleCode (pair : Fin 16) (word : Fin 2) :
    kernel.code[warmKShufflePc pair + word.val]? = some
      (pointerBroadcastInstr (warmKShuffleInput pair + word.val)
        (warmKShuffleOutput pair + word.val) (pair.val % 8)) := by
  fin_cases pair <;> fin_cases word <;> (set_option maxRecDepth 100000 in kernel_rfl)

/-- The offset added to the reconstructed pointer is independent of the selected row. -/
def warmKPairInputs (pair : Fin 16) (base tid : Nat) : List (Nat × Value) :=
  [(warmKShuffleOutput pair, b32 (base % 2 ^ 32)),
   (warmKShuffleOutput pair + 1, b32 (base / 2 ^ 32))] ++
  if pair.val = 0 then [(1119, b32 (8 * (tid % 8)))] else [(7666, b64 (16 * (tid % 8)))]

private theorem joinPointerWords {base : Nat} (hBase : base < 2 ^ 64) :
    (base % 4294967296 ||| base / 4294967296 * 4294967296 % 18446744073709551616) = base := by
  have hLo : base % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hShift : base / 4294967296 * 4294967296 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hShift, Nat.or_comm, Nat.mul_comm]
  change 2 ^ 32 * (base / 2 ^ 32) ||| base % 2 ^ 32 = base
  rw [← Nat.two_pow_add_eq_or_of_lt hLo]
  omega

/-- The decoded pack and add produce the same byte-address formula for all 16 pairs. -/
theorem warmKPairSourceCore {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (pair : Fin 16) :
    Seg kernel [] l g (warmKSourceCut pair - (warmKShufflePc pair + 2))
      (warmKShufflePc pair + 2) (warmKPairInputs pair base tid) (warmKSourceCut pair)
      [(packetSrcReg (recurringPacketSite 0) pair, b64 (recurringSourceAddress base tid))] := by
  have hLo : base % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hHi : base / 4294967296 < 4294967296 := by omega
  have hOffset1 : 8 * (tid % 8) < 4294967296 := by omega
  have hOffset2 : 16 * (tid % 8) < 4294967296 := by omega
  have hOffset4 : (8 * (tid % 8)) * 2 = 16 * (tid % 8) := by omega
  have hOff64 : 16 * (tid % 8) < 18446744073709551616 := by omega
  fin_cases pair <;> intro s hs <;>
    simp only [warmKShufflePc, warmKSourceCut, warmKPairInputs, warmKShuffleOutput,
      recurringPacketSite, packetSrcReg, recurringSourceAddress,
      List.cons_append, List.nil_append, Nat.reduceEqDiff, ↓reduceIte] at hs ⊢ <;>
    seg_fp hs using
      norm_bits [joinPointerWords hBase, Nat.mod_eq_of_lt hOffset1, Nat.mod_eq_of_lt hOffset2,
        Nat.mod_eq_of_lt hOff64, hOffset4]

end
end PTX.Kernels.TmlFa4Fwd.Loader

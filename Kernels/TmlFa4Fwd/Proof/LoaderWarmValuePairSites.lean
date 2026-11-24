-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundValueReload
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyReload
public import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
public import Kernels.TmlFa4Fwd.Proof.LoaderSourceLayout
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmShuffleFloor
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFirstPrefix
public import Kernels.TmlFa4Fwd.Proof.TerminalSite
public import Kernels.TmlFa4Fwd.Flow.Code.Part019

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def warmVShufflePc (pair : Fin 16) : Nat :=
  (![1239, 1249, 1256, 1262, 1268, 1274, 1280, 1286,
     1293, 1299, 1305, 1311, 1317, 1323, 1329, 1335] : Fin 16 → Nat) pair

def warmVShuffleInput (pair : Fin 16) : Nat := if pair.val < 8 then 2077 else 2098

def warmVShuffleOutput (pair : Fin 16) : Nat :=
  (![2079, 2083, 2086, 2088, 2090, 2092, 2094, 2096,
     2100, 2102, 2104, 2106, 2108, 2110, 2112, 2114] : Fin 16 → Nat) pair

def warmVShuffleSender (src : Nat) (pair : Fin 16) : Nat :=
  pointerBroadcastLane src + pair.val % 8

def warmVSourceCut (pair : Fin 16) : Nat := warmVShufflePc pair + if pair.val = 0 then 6 else 4

/-- All warm V pairs use an adjacent pair of shuffles with one common subgroup selector. -/
theorem warmVShuffleCode (pair : Fin 16) (word : Fin 2) :
    kernel.code[warmVShufflePc pair + word.val]? = some
      (pointerBroadcastInstr (warmVShuffleInput pair + word.val)
        (warmVShuffleOutput pair + word.val) (pair.val % 8)) := by
  fin_cases pair <;> fin_cases word <;> (set_option maxRecDepth 100000 in kernel_rfl)

/-- The offset added to the reconstructed pointer is independent of the selected row. -/
def warmVPairInputs (pair : Fin 16) (base tid : Nat) : List (Nat × Value) :=
  [(warmVShuffleOutput pair, b32 (base % 2 ^ 32)),
   (warmVShuffleOutput pair + 1, b32 (base / 2 ^ 32))] ++
  if pair.val = 0 then [(2066, b32 (16 * tid))] else [(7721, b64 (16 * (tid % 8)))]

private theorem pagePointerJoin {base : Nat} (hBase : base < 2 ^ 64) :
    (base % 4294967296 ||| base / 4294967296 * 4294967296 % 18446744073709551616) = base := by
  have hLo : base % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hShift : base / 4294967296 * 4294967296 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hShift, Nat.or_comm, Nat.mul_comm]
  change 2 ^ 32 * (base / 2 ^ 32) ||| base % 2 ^ 32 = base
  rw [← Nat.two_pow_add_eq_or_of_lt hLo]
  omega

private theorem columnMask16 (tid : Nat) : (16 * tid &&& 112) = 16 * (tid % 8) := by
  have h := congrArg (fun n => n <<< 4) (Nat.and_two_pow_sub_one_eq_mod tid 3)
  change (tid &&& 7) <<< 4 = (tid % 8) <<< 4 at h
  rw [Nat.shiftLeft_and_distrib] at h
  simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, Nat.mul_comm _ 16] using h

/-- The decoded pack and add produce the same byte-address formula for all 16 pairs. -/
theorem warmVPairSourceCore {l : Launch} {g base tid : Nat}
    (hBase : base < 2 ^ 64) (hTid : tid < 512) (pair : Fin 16) :
    Seg kernel [] l g (warmVSourceCut pair - (warmVShufflePc pair + 2))
      (warmVShufflePc pair + 2) (warmVPairInputs pair base tid) (warmVSourceCut pair)
      [(packetSrcReg (recurringPacketSite 1) pair, b64 (recurringSourceAddress base tid))] := by
  have hLo : base % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hHi : base / 4294967296 < 4294967296 := by omega
  have hOffset1 : 8 * (tid % 8) < 4294967296 := by omega
  have hOffset2 : 16 * (tid % 8) < 4294967296 := by omega
  have hOffset4 : (8 * (tid % 8)) * 2 = 16 * (tid % 8) := by omega
  have hOff64 : 16 * (tid % 8) < 18446744073709551616 := by omega
  have hOffset3 : 16 * tid < 4294967296 := by omega
  have hTid64 : 16 * tid < 18446744073709551616 := by omega
  fin_cases pair <;> intro s hs <;>
    simp only [warmVShufflePc, warmVSourceCut, warmVPairInputs, warmVShuffleOutput,
      recurringPacketSite, packetSrcReg, recurringSourceAddress,
      List.cons_append, List.nil_append, Nat.reduceEqDiff, ↓reduceIte] at hs ⊢ <;>
    seg_fp hs using
      norm_bits [pagePointerJoin hBase, Nat.mod_eq_of_lt hOffset1, Nat.mod_eq_of_lt hOffset2,
        Nat.mod_eq_of_lt hOff64, hOffset4, Nat.mod_eq_of_lt hOffset3,
        Nat.mod_eq_of_lt hTid64, columnMask16]

end
end PTX.Kernels.TmlFa4Fwd.Loader

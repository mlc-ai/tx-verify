-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveRanks
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueSender
import Kernels.TmlFa4Fwd.Proof.MmaRingAddress
import Kernels.TmlFa4Fwd.Proof.MmaQkAssembly

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

noncomputable section

/-- Low bits of a K descriptor before adding the fragment stride. -/
def keyDescriptorLow (l : Launch) (use : Nat) : Nat := kvStart l use / 16 + 65536

/-- The recurring K source prepares the descriptor of the current key slot. -/
theorem keyDescriptorLocal {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g use : Nat) :
    Seg kernel [] l g 6 2355
      [(1192,b32 (kvSlot use)), (2535,b32 l.sharedBase), (1062,b32 12)]
      2361 [(2592,b32 (keyDescriptorLow l use)), (1062,b32 12)] := by
  have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
  have hBound := hp.shared.2.1
  have hAlign := hp.shared.1
  have h0 : kvSlot use < 4294967296 := by omega
  have h1 : kvSlot use * 32768 < 4294967296 := by omega
  have h2 : l.sharedBase < 4294967296 := by omega
  have h3 : l.sharedBase + kvSlot use * 32768 < 4294967296 := by omega
  let start := l.sharedBase + kvSlot use * 32768 + 68608
  have h4 : l.sharedBase + kvSlot use * 32768 + 68608 < 4294967296 := by omega
  have h5 : (l.sharedBase + kvSlot use * 32768 + 68608) / 16 < 4294967296 := by omega
  have h6 : start / 16 < 2 ^ 16 := by dsimp [start]; omega
  have hMask := descriptorStart_mask (start := start) (by dsimp [start]; omega)
    (by dsimp [start]; omega)
  have hOr : start / 16 ||| 65536 = start / 16 + 65536 := by
    rw [Nat.or_comm, show (65536 : Nat) = 2 ^ 16 * 1 by rfl,
      ← Nat.two_pow_add_eq_or_of_lt h6, Nat.mul_one, Nat.add_comm]
  dsimp only [start] at hMask hOr
  have hStart : l.sharedBase + 68608 + 32768 * kvSlot use =
      l.sharedBase + kvSlot use * 32768 + 68608 := by omega
  intro t ht
  seg_fp ht using
    (try unfold keyDescriptorLow kvStart
     nf_simp
     try simp only [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
        Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5, hMask, hOr, hStart])

end
end PTX.Kernels.TmlFa4Fwd.Thread

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopies
public import Kernels.TmlFa4Fwd.Proof.LoaderEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Reconstruct the shuffled K row pointer, add this lane's BF16 column offset, then set the
decoded source length for the first copy pair. -/
theorem prepareFirstKPairWithColumn (l : Launch) (g : Nat) {stage lane base : Nat} (live : Bool)
    (hBase : base < 2 ^ 64) :
    Seg kernel [] l g 4 546
      [(1855, b32 (base % 2 ^ 32)), (1856, b32 (base / 2 ^ 32)),
        (1082, b32 (kvCopyColumn lane false)), (124, .pred live),
        (1083, b32 (kvCopyAddress l.sharedBase stage lane 0 false))] 550
      ((7547, b64 (2 * kvCopyColumn lane false)) ::
        firstKCopyFacts l stage lane ((base + 2 * kvCopyColumn lane false) % 2 ^ 64)
          (if live then 16 else 0)) := by
  have hLo : base % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hHi : base / 2 ^ 32 < 2 ^ 32 := by omega
  have hCol : kvCopyColumn lane false < 2 ^ 32 := by
    have h := Nat.mod_lt lane (by decide : 0 < 8)
    simp [kvCopyColumn]
    omega
  have hJoin : (base % 4294967296 ||| base / 4294967296 * 4294967296 %
      18446744073709551616) = base := by
    have hShift : base / 4294967296 * 4294967296 < 18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt hShift, Nat.or_comm, Nat.mul_comm]
    change 2 ^ 32 * (base / 2 ^ 32) ||| base % 2 ^ 32 = base
    rw [← Nat.two_pow_add_eq_or_of_lt hLo]
    omega
  cases live <;> intro t ht <;> unfold firstKCopyFacts <;>
    seg_fp ht using norm_bits [hJoin, Nat.mod_eq_of_lt hCol]

/-- The first pair's copies consume the same reconstructed pointer and source size. -/
theorem prepareFirstKPair (l : Launch) (g : Nat) {stage lane base : Nat} (live : Bool)
    (hBase : base < 2 ^ 64) :
    Seg kernel [] l g 4 546
      [(1855, b32 (base % 2 ^ 32)), (1856, b32 (base / 2 ^ 32)),
        (1082, b32 (kvCopyColumn lane false)), (124, .pred live),
        (1083, b32 (kvCopyAddress l.sharedBase stage lane 0 false))] 550
      (firstKCopyFacts l stage lane ((base + 2 * kvCopyColumn lane false) % 2 ^ 64)
        (if live then 16 else 0)) := by
  intro t ht
  obtain ⟨u, hu, hU⟩ := prepareFirstKPairWithColumn l g live hBase t ht
  exact ⟨u, hu, hU.mono hU.2.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

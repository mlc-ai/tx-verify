-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry
public import Kernels.TmlFa4Fwd.Flow.Code.Part005
public import Lemmas.Flow.Swizzle

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem shiftedMask {a k j : Nat} :
    (a * 2 ^ j) &&& ((2 ^ k - 1) * 2 ^ j) = (a % 2 ^ k) * 2 ^ j := by
  simp only [← Nat.shiftLeft_eq, ← Nat.shiftLeft_and_distrib, Nat.and_two_pow_sub_one_eq_mod]

private theorem rowMask (tid : Nat) : tid / 8 &&& 7 = tid / 8 % 8 :=
  Nat.and_two_pow_sub_one_eq_mod _ 3

private theorem columnMask (tid : Nat) : tid * 8 &&& 56 = 8 * (tid % 8) := by
  have h := shiftedMask (a := tid) (k := 3) (j := 3)
  change tid * 8 &&& 56 = tid % 8 * 8 at h
  rwa [Nat.mul_comm (tid % 8)] at h

private theorem sharedMask (tid : Nat) : tid * 16 &&& 1008 = 16 * (tid % 64) := by
  have h := shiftedMask (a := tid) (k := 6) (j := 4)
  change tid * 16 &&& 1008 = tid % 64 * 16 at h
  rwa [Nat.mul_comm (tid % 64)] at h

/-- The decoded lane arithmetic constructs the row selector, BF16 starting column, and
the two lower-plane base offsets of the initial stage. -/
theorem initialKvSwizzle (l : Launch) (g : Nat) {tid : Nat}
    (hTid : tid < 512) (hBase : l.sharedBase + 232448 ≤ 2 ^ 18) :
    Seg kernel [] l g 15 356 [(1061, b32 tid), (2535, b32 l.sharedBase)] 371
      [(1081, b32 (tid / 8 % 8)), (1082, b32 (kvCopyColumn tid false)),
       (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
       (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false))] := by
  intro t ht
  have hTid32 : tid < 4294967296 := by omega
  have hTid64 : tid < 18446744073709551616 := by omega
  have hDiv32 : tid / 8 < 4294967296 := by omega
  have hDiv64 : tid / 8 < 18446744073709551616 := by omega
  have hShl3 : tid * 8 < 4294967296 := by omega
  have hShl4 : tid * 16 < 4294967296 := by omega
  have hShl364 : tid * 8 < 18446744073709551616 := by omega
  have hShl464 : tid * 16 < 18446744073709551616 := by omega
  simp only [kvCopyColumn, kvCopyAddress, kvSwizzle, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero, Nat.reduceMod, Nat.reduceDiv, Nat.shiftRight_eq_div_pow]
  have hOffset := Nat.mod_lt tid (show 0 < 64 by decide)
  have hB32 : l.sharedBase < 4294967296 := by omega
  have hLane32 : 16 * (tid % 64) < 4294967296 := by omega
  have hAdd32 : l.sharedBase + 16 * (tid % 64) < 4294967296 := by omega
  have h0 : l.sharedBase + 16 * (tid % 64) + 68608 < 4294967296 := by omega
  have h1 : l.sharedBase + 16 * (tid % 64) + 69632 < 4294967296 := by omega
  have hd0 : (l.sharedBase + 16 * (tid % 64) + 68608) / 8 < 4294967296 := by omega
  have hd1 : (l.sharedBase + 16 * (tid % 64) + 69632) / 8 < 4294967296 := by omega
  have hMasked (n : Nat) : (n &&& 112) < 4294967296 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have ha0 : l.sharedBase + 16 * (tid % 64) + 68608 =
      l.sharedBase + 68608 + 16 * (tid % 64) := by omega
  have ha1 : l.sharedBase + 16 * (tid % 64) + 69632 =
      l.sharedBase + 68608 + 1024 + 16 * (tid % 64) := by omega
  seg_fp ht using
    nf_simp [Nat.mod_eq_of_lt hTid32, Nat.mod_eq_of_lt hTid64, Nat.mod_eq_of_lt hDiv32,
      Nat.mod_eq_of_lt hDiv64, Nat.mod_eq_of_lt hShl3, Nat.mod_eq_of_lt hShl4,
      Nat.mod_eq_of_lt hShl364, Nat.mod_eq_of_lt hShl464, rowMask, columnMask, sharedMask]
    all_goals
      simp only [Nat.mod_eq_of_lt hB32, Nat.mod_eq_of_lt hLane32, Nat.mod_eq_of_lt hAdd32,
        Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hd0, Nat.mod_eq_of_lt hd1,
        Nat.mod_eq_of_lt (hMasked _), ← BitVec.ofNat_xor]
      simp only [ha0, ha1, Nat.add_zero, Nat.xor_comm]


/-- The initial K/V shared destination geometry is available along the actual loader run. -/
theorem initialKvSwizzleRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState}
    (ht : At t 356 [(1061, b32 (g % l.block)), (2535, b32 l.sharedBase)]) :
    ∃ u, run kernel Assumptions.all l g 15 t = some u ∧ At u 371
      [(1081, b32 ((g % l.block) / 8 % 8)), (1082, b32 (kvCopyColumn (g % l.block) false)),
       (1083, b32 (kvCopyAddress l.sharedBase 0 (g % l.block) 0 false)),
       (1084, b32 (kvCopyAddress l.sharedBase 0 (g % l.block) 1 false))] := by
  have hTid : g % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨u, hu, hU⟩ := initialKvSwizzle l g hTid hp.shared.2.1 t ht
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  exact ⟨u, huA, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

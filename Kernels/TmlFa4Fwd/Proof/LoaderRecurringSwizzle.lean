-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSwizzleSetup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- PCs where the recurring packets compute their two swizzled stage-zero addresses.
The last V window reuses the last K window's results. -/
def recurringSwizzleStart : Fin 3 → Nat
  | 0 => 983
  | 1 => 1227
  | 2 => 1451

def recurringSwizzleFinish : Fin 3 → Nat
  | 0 => 996
  | 1 => 1238
  | 2 => 1464

def recurringSwizzleRegs : Fin 3 → Nat × Nat
  | 0 => (1992, 1988)
  | 1 => (2076, 2072)
  | 2 => (1153, 1152)

def recurringSwizzleInputs (l : Launch) (tid : Nat) (site : Fin 3) : List (Nat × Value) :=
  [(1061, b32 tid), (2535, b32 l.sharedBase)] ++
    match site with
    | 0 => [(1119, b32 (8 * (tid % 8)))]
    | 1 => []
    | 2 => [(1147, b32 (8 * (tid % 8)))]

def recurringSwizzleFacts (l : Launch) (tid : Nat) (site : Fin 3) : List (Nat × Value) :=
  [((recurringSwizzleRegs site).1, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   ((recurringSwizzleRegs site).2, b32 (kvCopyAddress l.sharedBase 0 tid 1 false))]

private theorem repeatLaneMask (tid : Nat) : 16 * tid &&& 1008 = 16 * (tid % 64) := by
  have h := congrArg (fun n => n <<< 4) (Nat.and_two_pow_sub_one_eq_mod tid 6)
  change (tid &&& 63) <<< 4 = (tid % 64) <<< 4 at h
  rw [Nat.shiftLeft_and_distrib] at h
  simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, Nat.mul_comm _ 16] using h

private theorem splitLaneMask (tid : Nat) :
    (16 * tid &&& 896) ||| (16 * (tid % 8)) = 16 * (tid % 64) := by
  have hOr : (tid &&& 56) ||| (tid % 8) = tid % 64 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod tid 3, ← Nat.and_or_distrib_left,
      ← Nat.and_two_pow_sub_one_eq_mod tid 6]
    rfl
  have hShift := congrArg (fun n => n <<< 4) hOr
  change ((tid &&& 56) ||| (tid % 8)) <<< 4 = (tid % 64) <<< 4 at hShift
  rw [Nat.shiftLeft_or_distrib, Nat.shiftLeft_and_distrib] at hShift
  simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, Nat.mul_comm _ 16] using hShift

private theorem recurringSwizzleCore {l : Launch} {g tid : Nat}
    (hTid : tid < 512) (hBase : l.sharedBase + 232448 ≤ 2 ^ 18) (site : Fin 3) :
    Seg kernel [] l g (recurringSwizzleFinish site - recurringSwizzleStart site)
      (recurringSwizzleStart site) (recurringSwizzleInputs l tid site)
      (recurringSwizzleFinish site) (recurringSwizzleFacts l tid site) := by
  have hTid32 : tid < 4294967296 := by omega
  have hTid64 : tid < 18446744073709551616 := by omega
  have hShl4 : tid * 16 < 4294967296 := by omega
  have hShl464 : tid * 16 < 18446744073709551616 := by omega
  have hCol32 : 8 * (tid % 8) < 4294967296 := by omega
  have hCol64 : 8 * (tid % 8) < 18446744073709551616 := by omega
  have hCol' : (8 * (tid % 8)) * 2 = 16 * (tid % 8) := by omega
  have hColBit : 16 * (tid % 8) < 4294967296 := by omega
  have hColBit64 : 16 * (tid % 8) < 18446744073709551616 := by omega
  have hB32 : l.sharedBase < 4294967296 := by omega
  have hMask32 : tid * 16 &&& 896 < 4294967296 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hMask64 : tid * 16 &&& 896 < 18446744073709551616 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hLane32 : 16 * (tid % 64) < 4294967296 := by omega
  have hLane64 : 16 * (tid % 64) < 18446744073709551616 := by omega
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
  have hMask : tid * 16 &&& 1008 = 16 * (tid % 64) := by
    rw [Nat.mul_comm tid 16, repeatLaneMask]
  have hPack : (tid * 16 &&& 896) ||| (16 * (tid % 8)) = 16 * (tid % 64) := by
    rw [Nat.mul_comm tid 16, splitLaneMask]
  fin_cases site <;> intro t ht <;>
    simp only [recurringSwizzleStart, recurringSwizzleFinish, recurringSwizzleInputs,
      recurringSwizzleFacts, recurringSwizzleRegs, kvCopyAddress, kvSwizzle, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero, Nat.reduceMod, Nat.reduceDiv, Nat.shiftRight_eq_div_pow,
      List.append_nil, List.cons_append, List.nil_append] at ht ⊢ <;>
    seg_fp ht using
      nf_simp [Nat.mod_eq_of_lt hTid32, Nat.mod_eq_of_lt hTid64, Nat.mod_eq_of_lt hShl4,
        Nat.mod_eq_of_lt hShl464, Nat.mod_eq_of_lt hCol32, Nat.mod_eq_of_lt hCol64, hCol',
        Nat.mod_eq_of_lt hColBit, Nat.mod_eq_of_lt hColBit64, Nat.mod_eq_of_lt hMask32,
        Nat.mod_eq_of_lt hMask64, Nat.mod_eq_of_lt hLane32, Nat.mod_eq_of_lt hLane64,
        hMask, hPack]
      all_goals
        simp only [Nat.mod_eq_of_lt hB32, Nat.mod_eq_of_lt hAdd32,
          Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hd0, Nat.mod_eq_of_lt hd1,
          Nat.mod_eq_of_lt (hMasked _), ← BitVec.ofNat_xor]
        simp only [ha0, ha1, Nat.add_zero, Nat.xor_comm]

/-- The three actual swizzle prefixes compute the stage-zero bases for recurring copy pairs. -/
theorem recurringSwizzleRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g tid : Nat} (hTid : tid < 512) (site : Fin 3) :
    Seg kernel Assumptions.all l g (recurringSwizzleFinish site - recurringSwizzleStart site)
      (recurringSwizzleStart site) (recurringSwizzleInputs l tid site)
      (recurringSwizzleFinish site) (recurringSwizzleFacts l tid site) := by
  intro t ht
  obtain ⟨u, hu, hU⟩ := recurringSwizzleCore hTid hp.shared.2.1 site t ht
  have hLo : 174 ≤ recurringSwizzleStart site := by fin_cases site <;> decide
  have hHi : recurringSwizzleStart site + (recurringSwizzleFinish site -
      recurringSwizzleStart site) ≤ 1906 := by fin_cases site <;> decide
  have hSeq : ((kernel.code.drop (recurringSwizzleStart site)).take
      (recurringSwizzleFinish site - recurringSwizzleStart site - 1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  exact ⟨u, (loaderLinear (regs := []) hLo hHi ht.1 (by simp) hSeq hu).1, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

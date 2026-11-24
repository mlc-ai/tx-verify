-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageIndex
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingStart

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem laneColumnMask (tid : Nat) : tid * 8 &&& 56 = 8 * (tid % 8) := by
  have h := congrArg (fun n => n <<< 3) (Nat.and_two_pow_sub_one_eq_mod tid 3)
  change (tid &&& 7) <<< 3 = (tid % 8) <<< 3 at h
  rw [Nat.shiftLeft_and_distrib] at h
  simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, Nat.mul_comm (tid % 8)] using h

/-- Both recurring row refreshers calculate the same eight-lane-group offset.
The steady path saves this value across its iterations. -/
theorem recurringLaneOffsetWithColumnAndRowCore {l : Launch} {g tid : Nat}
    (hTid : tid < 512) (site : Fin 2) :
    let start := if site.val = 0 then 923 else 1386
    let dst := if site.val = 0 then 1968 else 2130
    let col := if site.val = 0 then 1119 else 1147
    let row := if site.val = 0 then 1966 else 1146
    Seg kernel [] l g 5 start [(1061, b32 tid)] (start + 5)
      [(dst, b32 (primingLaneRow 0 tid)), (col, b32 (8 * (tid % 8))), (row,b32 (tid/8%8))] := by
  dsimp only
  have h32 : tid < 4294967296 := by omega
  have h64 : tid < 18446744073709551616 := by omega
  have hDiv32 : tid / 8 < 4294967296 := by omega
  have hDiv64 : tid / 8 < 18446744073709551616 := by omega
  have hMul32 : tid * 8 < 4294967296 := by omega
  have hMul64 : tid * 8 < 18446744073709551616 := by omega
  have hRow : tid / 8 &&& 7 = tid / 8 % 8 := Nat.and_two_pow_sub_one_eq_mod _ 3
  have hOr : tid / 8 % 8 ||| (8 * (tid % 8)) = tid / 8 % 8 + 8 * (tid % 8) := by
    have h := lor_eq_add (k := 3) (x := 8 * (tid % 8)) (y := tid / 8 % 8)
      (by omega) (Nat.mod_lt _ (by decide))
    rw [Nat.or_comm, h, Nat.add_comm]
  have hRow32 : tid / 8 % 8 < 4294967296 := by omega
  have hCol32 : 8 * (tid % 8) < 4294967296 := by omega
  have hRow64 : tid / 8 % 8 < 18446744073709551616 := by omega
  have hCol64 : 8 * (tid % 8) < 18446744073709551616 := by omega
  have hJoin32 : tid / 8 % 8 + 8 * (tid % 8) < 4294967296 := by omega
  have hJoin64 : tid / 8 % 8 + 8 * (tid % 8) < 18446744073709551616 := by omega
  let start := if site.val = 0 then 923 else 1386
  let dst := if site.val = 0 then 1968 else 2130
  let col := if site.val = 0 then 1119 else 1147
  let row := if site.val = 0 then 1966 else 1146
  have hCore : Seg kernel [] l g 5 start [(1061, b32 tid)] (start + 5)
      [(dst, b32 (primingLaneRow 0 tid)), (col, b32 (8 * (tid % 8))), (row,b32 (tid/8%8))] := by
    fin_cases site <;> intro t ht <;> simp only [start, dst, col, row, ↓reduceIte] at ht ⊢ <;>
      seg_fp ht using
        nf_simp [Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64,
          Nat.mod_eq_of_lt hDiv32, Nat.mod_eq_of_lt hDiv64, Nat.mod_eq_of_lt hMul32,
          Nat.mod_eq_of_lt hMul64, hRow, laneColumnMask, hOr, primingLaneRow, kvCopyColumn,
          Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hCol32, Nat.mod_eq_of_lt hRow64,
          Nat.mod_eq_of_lt hCol64, Nat.mod_eq_of_lt hJoin32, Nat.mod_eq_of_lt hJoin64,
          Nat.add_zero, Nat.zero_add]
  exact hCore

theorem recurringLaneOffsetWithColumnCore {l : Launch} {g tid : Nat}
    (hTid : tid < 512) (site : Fin 2) :
    let start := if site.val = 0 then 923 else 1386
    let dst := if site.val = 0 then 1968 else 2130
    let col := if site.val = 0 then 1119 else 1147
    Seg kernel [] l g 5 start [(1061, b32 tid)] (start + 5)
      [(dst, b32 (primingLaneRow 0 tid)), (col, b32 (8 * (tid % 8)))] := by
  dsimp only
  intro s hs
  obtain ⟨t,ht,hT⟩ := recurringLaneOffsetWithColumnAndRowCore hTid site s hs
  exact ⟨t,ht,hT.mono ⟨hT.2.2.2.2.1,hT.2.2.2.2.2.1,trivial⟩⟩

/-- The warm cursor subtracts its current iteration from the high tile and shifts by
seven before seeding the first scratch slot. -/
theorem warmPageTileSeedCore {l : Launch} {g high iteration : Nat}
    (hOrder : iteration ≤ high) (hHigh : 128 * high < 2 ^ 32) :
    Seg kernel [] l g 4 917 [(1116, b32 high), (7174, b32 iteration)]
      921 [(1118, b32 (128 * (high - iteration))), (7175, b32 0), (775, .pred true)] := by
  have hH32 : high < 2 ^ 32 := by omega
  have hH64 : high < 2 ^ 64 := by omega
  have hI32 : iteration < 2 ^ 32 := by omega
  have hI64 : iteration < 2 ^ 64 := by omega
  have hD32 : high - iteration < 2 ^ 32 := by omega
  have hD64 : high - iteration < 2 ^ 64 := by omega
  have hOff32 : 128 * (high - iteration) < 2 ^ 32 := by omega
  have hOff64 : 128 * (high - iteration) < 2 ^ 64 := by omega
  have hc : Seg kernel [] l g 4 917 [(1116, b32 high), (7174, b32 iteration)]
      921 [(1118, b32 (128 * (high - iteration))), (7175, b32 0), (775, .pred true)] := by
    intro s hs
    seg_fp hs using
      first
      | decide
      | norm_bits [Nat.mod_eq_of_lt hH32, Nat.mod_eq_of_lt hH64, Nat.mod_eq_of_lt hI32,
          Nat.mod_eq_of_lt hI64, Nat.mod_eq_of_lt hD32, Nat.mod_eq_of_lt hD64,
          Nat.mod_eq_of_lt hOff32, Nat.mod_eq_of_lt hOff64]
  exact hc

/-- The steady cursor uses the same descending tile and combines it with
the lane offset retained from its one-time setup. -/
theorem steadyPageTileSeed {l : Launch} {g high iteration tid : Nat}
    (hOrder : iteration ≤ high) (hHigh : 128 * high + 64 < 2 ^ 32) :
    Seg kernel Assumptions.all l g 5 1396
      [(1116, b32 high), (7181, b32 iteration), (2130, b32 (primingLaneRow 0 tid))]
      1401 [(1148, b32 (primingLaneRow (high - iteration) tid)), (7182, b32 0),
        (778, .pred true)] := by
  let off := primingLaneRow 0 tid
  have hOff : off < 64 := by
    have hm := Nat.mod_lt tid (show 0 < 8 by decide)
    have hr := Nat.mod_lt (tid / 8) (show 0 < 8 by decide)
    simp [off, primingLaneRow, kvCopyColumn]
    omega
  have hOr : off ||| (128 * (high - iteration)) = primingLaneRow (high - iteration) tid := by
    rw [Nat.or_comm, lor_eq_add (k := 7) (by omega) (by omega)]
    simp [off, primingLaneRow, Nat.add_assoc]
  have hH32 : high < 4294967296 := by omega
  have hH64 : high < 18446744073709551616 := by omega
  have hI32 : iteration < 4294967296 := by omega
  have hI64 : iteration < 18446744073709551616 := by omega
  have hD32 : high - iteration < 4294967296 := by omega
  have hD64 : high - iteration < 18446744073709551616 := by omega
  have hOff32 : 128 * (high - iteration) < 4294967296 := by omega
  have hOff64 : 128 * (high - iteration) < 18446744073709551616 := by omega
  have hLane32 : off < 4294967296 := by omega
  have hLane64 : off < 18446744073709551616 := by omega
  have hRow32 : primingLaneRow (high - iteration) tid < 4294967296 := by
    change 128 * (high - iteration) + tid / 8 % 8 + kvCopyColumn tid false < 4294967296
    change 128 * 0 + tid / 8 % 8 + kvCopyColumn tid false < 64 at hOff
    omega
  have hRow64 : primingLaneRow (high - iteration) tid < 18446744073709551616 := by omega
  have hTile : Seg kernel [] l g 2 1396
      [(1116, b32 high), (7181, b32 iteration), (2130, b32 off)]
      1398 [(1145, b32 (128 * (high - iteration))), (2130, b32 off)] := by
    intro s hs
    seg_fp hs using
      norm_bits [Nat.mod_eq_of_lt hH32, Nat.mod_eq_of_lt hH64, Nat.mod_eq_of_lt hI32,
        Nat.mod_eq_of_lt hI64, Nat.mod_eq_of_lt hD32, Nat.mod_eq_of_lt hD64,
        Nat.mod_eq_of_lt hOff32, Nat.mod_eq_of_lt hOff64]
  have hLane : Seg kernel [] l g 3 1398
      [(1145, b32 (128 * (high - iteration))), (2130, b32 off)]
      1401 [(1148, b32 (primingLaneRow (high - iteration) tid)), (7182, b32 0),
        (778, .pred true)] := by
    intro s hs
    seg_fp hs using
      first
      | decide
      | nf_simp [Nat.mod_eq_of_lt hOff32, Nat.mod_eq_of_lt hOff64, Nat.mod_eq_of_lt hLane32,
          Nat.mod_eq_of_lt hLane64, hOr, Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64]
  have hc := hTile.comp hLane
  intro s hs
  obtain ⟨t, ht, hT⟩ := hc s hs
  have hSeq : ((kernel.code.drop 1396).take 4).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact ⟨t, (loaderLinear (regs := []) (lo := 1396) (n := 5)
    (by decide) (by decide) hs.1 (by simp) hSeq ht).1, hT⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

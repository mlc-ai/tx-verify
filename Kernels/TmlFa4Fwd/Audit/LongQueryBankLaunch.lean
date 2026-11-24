-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.SpecWitness
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Audit
open PTX PTX.Proof TensorDescriptor

noncomputable section

set_option maxRecDepth 2000

def longShape : Params where
  batch := 1
  kvHeads := 1
  pages := 128
  pageTableStride := 128
  qOffset b := if b = 0 then 0 else 256
  kLength _ := 2048
  page _ i := i
  qBase := 262144
  biasBase := 4194304
  oBase := 2 ^ 48
  lseBase := 2 ^ 38
  lseStride := 2 ^ 38
  cuQBase := 4096
  usedKBase := 8192
  pageTableBase := 12288
  kLayout := ⟨1048576, 128, 128, 2048⟩
  vLayout := ⟨2097152, 128, 128, 2048⟩
  qMapAddress := 64
  oMapAddress := 192
  biasMapAddress := 320
  qAllocation := .small
  oAllocation := .small
  biasAllocation := .small
  scaleLog2Bits := 0x3E0293EE
  invScaleBits := 0x413504F3
  q _ _ _ := 0
  k _ _ _ _ := 0
  v _ _ _ _ := 0
  bias _ _ _ := none

def longParams : Params :=
  { longShape with bias := fun row _ col =>
      if (col : Int) < longShape.biasColumn 0 row (longShape.keyCount 0 row) then some 1 else none }

def longLaunch : Launch where
  grid := 6
  block := 512
  localBase := 64
  params name := (longParams.scalarWords.find? (fun w => param w.1 == name)).map
    (BitVec.ofNat 64 ∘ (·.2))
  paramBytes name off :=
    (longParams.objectWords.find? (fun (i, start, span, _) =>
      param i == name && start ≤ off && off < start + span)).map
        fun (_, start, _, word) => leByte word (off - start)
  paramObjects name :=
    if name = param 9 then some (mapParam 9, 64)
    else if name = param 10 then some (mapParam 10, 192)
    else if name = param 11 then some (mapParam 11, 320)
    else none
  tensorMaps
    | 64 => some ⟨2, longParams.qMap⟩
    | 192 => some ⟨3, longParams.oMap⟩
    | 320 => some ⟨2, longParams.biasMap⟩
    | _ => none

private def longMemory (loc : Loc) : Option (Option Byte) :=
  let a := loc.addr
  if loc.space ≠ .global then some none
  else if 4096 ≤ a ∧ a < 4104 then
    some (some ((b32 (longParams.qOffset ((a - 4096) / 4))).byteAt ((a - 4096) % 4)))
  else if 8192 ≤ a ∧ a < 8196 then
    some (some ((b32 2048).byteAt ((a - 8192) % 4)))
  else if 12288 ≤ a ∧ a < 12800 then
    some (some ((b32 ((a - 12288) / 4)).byteAt ((a - 12288) % 4)))
  else if 4194304 ≤ a ∧ a < 4194304 + 2560 * 6 * 384 then
    let x := (a - 4194304) / 2
    some (some ((biasValue (longParams.bias (x / 7680) (x / 1280 % 6) (x % 1280))).byteAt
      ((a - 4194304) % 2)))
  else some (some ((Value.float .bf16 0).byteAt (a % 2)))

private theorem longAllocated (loc : Loc) : longMemory loc ≠ none := by
  simp only [longMemory]
  repeat' first | split | exact Option.some_ne_none _

private theorem longBf16 {a k : Nat} (hk : k < 2)
    (ha : 12800 ≤ a + k ∧ a + k < 4194304) (halign : a % 2 = 0) :
    longMemory (globalLoc (a + k)) = some (some ((Value.float .bf16 0).byteAt k)) := by
  have h0 : ¬ (4096 ≤ a + k ∧ a + k < 4104) := by omega
  have h1 : ¬ (8192 ≤ a + k ∧ a + k < 8196) := by omega
  have h2 : ¬ (12288 ≤ a + k ∧ a + k < 12800) := by omega
  have h3 : ¬ (4194304 ≤ a + k ∧ a + k < 4194304 + 2560 * 6 * 384) := by omega
  have hk' : (a + k) % 2 = k := by omega
  simp only [longMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_right h0,
    ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, hk']

/-- A legal isolated launch with a full two-stage Q tile and sixteen KV blocks. -/
theorem longQueryBankExample : ∃ m, Pre longParams longLaunch m := by
  refine ⟨longMemory, ?_⟩
  constructor
  case launch =>
    refine ⟨Launch.oneDimLaunch_clusterGridValid (by exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩),
      ?_, ?_, ?_⟩
    · intro _ h
      have hz : kernel.maxThreads = none := by kernel_rfl
      rw [hz] at h
      contradiction
    · intro s h
      have hz : kernel.reqThreads = some (512, 1, 1) := by kernel_rfl
      rw [hz] at h
      cases h
      rfl
    · intro _ _ _ h _
      have hz : kernel.ptrParams = [] := by kernel_rfl
      simp [hz] at h
  case grid => decide
  case block => rfl
  case cluster => exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  case shape => decide
  case lengths =>
    intro b hb
    have : b = 0 := by change b < 1 at hb; omega
    subst b
    decide
  case pageTable =>
    intro b hb
    have : b = 0 := by change b < 1 at hb; omega
    subst b
    refine ⟨by decide, fun i hi => ⟨hi, ?_⟩⟩
    change i < 128 at hi
    change i < 2^31
    omega
  case values =>
    intro i hi
    simp only [Params.scalarWords, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by decide +kernel, by kernel_rfl⟩
  case objectBytes =>
    intro i off bytes value hh
    simp only [Params.objectWords, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with
      hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh
    all_goals
      obtain ⟨hi, hoff, hbytes, hvalue⟩ := by
        simpa only [Prod.mk.injEq] using hh
      subst i off bytes value
      decide +kernel
  case scales =>
    refine ⟨4278775 / 33554432, 11863283 / 1048576, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · kernel_rfl
    · norm_num
    · norm_num
  case maps =>
    intro i addr binding hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with hh | hh | hh
    all_goals
      simp only [Prod.mk.injEq] at hh
      obtain ⟨hi, ha, hd⟩ := hh
      subst i addr binding
      refine ⟨by kernel_rfl, by decide, by decide, rfl, by decide, ?_⟩
      intro h
      contradiction
  case raggedBase => decide
  case alignment => decide
  case lseStride => decide
  case ranges =>
    intro r hr
    simp only [Params.inputRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  case separate =>
    refine ⟨by unfold Region.Apart; decide, ?_⟩
    intro r hr
    simp only [Params.inputRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Region.Apart <;> decide
  case cuQ =>
    intro b hb k hk
    change b ≤ 1 at hb
    change k < 4 at hk
    let a := 4096 + 4 * b + k
    have ha : 4096 ≤ a ∧ a < 4104 := by unfold a; omega
    have hdiv : (a - 4096) / 4 = b := by unfold a; omega
    have hmod : (a - 4096) % 4 = k := by unfold a; omega
    change longMemory (globalLoc a) = some (some ((b32 (longParams.qOffset b)).byteAt k))
    simp only [longMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_left ha,
      hdiv, hmod]
  case usedK =>
    intro b hb k hk
    have : b = 0 := by change b < 1 at hb; omega
    subst b
    change k < 4 at hk
    let a := 8192 + k
    have h0 : ¬ (4096 ≤ a ∧ a < 4104) := by unfold a; omega
    have h1 : 8192 ≤ a ∧ a < 8196 := by unfold a; omega
    have hmod : (a - 8192) % 4 = k := by unfold a; omega
    change longMemory (globalLoc a) = some (some ((b32 2048).byteAt k))
    simp only [longMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_right h0,
      ite_eq_left h1, hmod]
  case pageBytes =>
    intro b hb i hi k hk
    have : b = 0 := by change b < 1 at hb; omega
    subst b
    change i < 128 at hi
    change k < 4 at hk
    let a := 12288 + 4 * i + k
    have h0 : ¬ (4096 ≤ a ∧ a < 4104) := by unfold a; omega
    have h1 : ¬ (8192 ≤ a ∧ a < 8196) := by unfold a; omega
    have h2 : 12288 ≤ a ∧ a < 12800 := by unfold a; omega
    have hd : (a - 12288) / 4 = i := by unfold a; omega
    have hm : (a - 12288) % 4 = k := by unfold a; omega
    simp only [longShape, longParams, Nat.zero_mul, Nat.zero_add, globalLoc, Loc.at]
    change longMemory (globalLoc a) = some (some ((b32 i).byteAt k))
    simp only [longMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_right h0,
      ite_eq_right h1, ite_eq_left h2, hd, hm]
  case qBytes =>
    intro q hq h hh d hd k hk
    change q < 256 at hq
    change h < 6 at hh
    change k < 2 at hk
    apply longBf16 (a := 262144 + 2 * ((q * 6 + h) * 128 + d)) hk <;> omega
  case kvBytes =>
    intro page hp h hh r hr d hd
    change page < 128 at hp
    change h < 1 at hh
    refine ⟨?_, ?_⟩
    · intro k hk
      change k < 2 at hk
      apply longBf16 (a := 1048576 + 2 * (page * 2048 + h * 128 + r * 128 + d)) hk <;> omega
    · intro k hk
      change k < 2 at hk
      apply longBf16 (a := 2097152 + 2 * (page * 2048 + h * 128 + r * 128 + d)) hk <;> omega
  case biasBytes =>
    intro q hq h hh col hc k hk
    change q < 384 at hq
    change h < 6 at hh
    have hk' : k < 2 := by
      cases he : longParams.bias q h col <;> rw [he] at hk <;> exact hk
    let a := 4194304 + 2 * ((q * 6 + h) * 1280 + col) + k
    have h0 : ¬ (4096 ≤ a ∧ a < 4104) := by unfold a; omega
    have h1 : ¬ (8192 ≤ a ∧ a < 8196) := by unfold a; omega
    have h2 : ¬ (12288 ≤ a ∧ a < 12800) := by unfold a; omega
    have h3 : 4194304 ≤ a ∧ a < 4194304 + 2560 * 6 * 384 := by unfold a; omega
    have hd : (a - 4194304) / 2 = (q * 6 + h) * 1280 + col := by unfold a; omega
    have hm : (a - 4194304) % 2 = k := by unfold a; omega
    have hq' : ((q * 6 + h) * 1280 + col) / 7680 = q := by omega
    have hh' : ((q * 6 + h) * 1280 + col) / 1280 % 6 = h := by omega
    have hc' : ((q * 6 + h) * 1280 + col) % 1280 = col := by omega
    change longMemory (globalLoc a) = some (some ((biasValue (longParams.bias q h col)).byteAt k))
    simp only [longMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_right h0,
      ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, hd, hm, hq', hh', hc']
  case biasMask =>
    intro b hb row _ h _ j col h0 _
    have : b = 0 := by change b < 1 at hb; omega
    subst b
    have hRow : longParams.qOffset 0 + row = row := Nat.zero_add row
    rw [hRow]
    change (if (col.toNat : Int) < longShape.biasColumn 0 row (longShape.keyCount 0 row)
      then some (1 : ℝ) else none).isSome = decide (j < longShape.keyCount 0 row)
    rw [Int.toNat_of_nonneg h0]
    have hslot : col < longShape.biasColumn 0 row (longShape.keyCount 0 row) ↔
        j < longShape.keyCount 0 row := by
      change longShape.biasColumn 0 row j <
        longShape.biasColumn 0 row (longShape.keyCount 0 row) ↔ _
      dsimp only [Params.biasColumn]
      simp only [sub_lt_sub_iff_right, add_lt_add_iff_right, Int.ofNat_lt]
    by_cases hj : j < longShape.keyCount 0 row <;> simp [hslot, hj]
  case outputs => exact fun loc _ => longAllocated loc
  case shared => exact ⟨rfl, by decide, fun _ _ _ _ => longAllocated _⟩
  case localMemory => exact ⟨rfl, by decide, fun _ _ _ _ => longAllocated _⟩

theorem longExampleTrips : Mma.trips longParams 0 0 = 16 := by decide +kernel

end
end PTX.Kernels.TmlFa4Fwd.Audit

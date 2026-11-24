-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Tactics.KernelRfl
public import Mathlib.Tactic.NormNum
import Core.Async.Tensor.TensorStoreMemory
import Kernels.TmlFa4Fwd.Audit.OutputStep
import Kernels.TmlFa4Fwd.Proof.Lib.ScheduleCoords
import all Init.Data.ToString.Extra
import all Init.Data.Repr

namespace PTX.Kernels.TmlFa4Fwd
open TensorDescriptor
noncomputable section

set_option maxRecDepth 2000

private def exampleShape : Params where
  batch := 2
  kvHeads := 1
  pages := 10
  pageTableStride := 10
  qOffset b := if b = 0 then 0 else if b = 1 then 129 else 137
  kLength b := if b = 0 then 145 else 19
  page b i := if b = 0 then i else i + 8
  qBase := 262144
  biasBase := 4194304
  oBase := 2 ^ 30 * 3072 + 4096
  lseBase := 8388608
  lseStride := 144
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

private def exampleParams : Params :=
  { exampleShape with bias := fun q _ col =>
      let b := if q < 129 then 0 else 1
      let row := q - exampleShape.qOffset b
      let cut := exampleShape.biasColumn b row (exampleShape.keyCount b row)
      if (col : Int) < cut then some 1 else none }

private def wordByte (w k : Nat) (x : Nat) : Byte :=
  (Value.bits w (BitVec.ofNat 64 x)).byteAt k

private def exampleMemory (l : Loc) : Option (Option Byte) :=
  let a := l.addr
  if l.space ≠ .global then some none
  else if 4096 ≤ a ∧ a < 4108 then
    let b := (a - 4096) / 4
    some (some (wordByte 32 ((a - 4096) % 4) (exampleParams.qOffset b)))
  else if 8192 ≤ a ∧ a < 8200 then
    let b := (a - 8192) / 4
    some (some (wordByte 32 ((a - 8192) % 4) (exampleParams.kLength b)))
  else if 12288 ≤ a ∧ a < 12368 then
    let i := (a - 12288) / 4
    some (some (wordByte 32 ((a - 12288) % 4) (exampleParams.page (i / 10) (i % 10))))
  else if 4194304 ≤ a ∧ a < 4194304 + 2560 * 6 * 265 then
    let x := (a - 4194304) / 2
    let b := exampleParams.bias (x / 7680) (x / 1280 % 6) (x % 1280)
    some (some ((biasValue b).byteAt ((a - 4194304) % 2)))
  else
    some (some ((Value.float .bf16 0).byteAt (a % 2)))

private def exampleLaunch : Launch where
  grid := 12
  block := 512
  localBase := 64
  params name := (exampleParams.scalarWords.find? (fun w => param w.1 == name)).map
    (BitVec.ofNat 64 ∘ (·.2))
  paramBytes name off :=
    (exampleParams.objectWords.find? (fun (i, start, span, _) =>
      param i == name && start ≤ off && off < start + span)).map
      fun (_, start, _, word) => leByte word (off - start)
  paramObjects name :=
    if name = param 9 then some (mapParam 9, 64)
    else if name = param 10 then some (mapParam 10, 192)
    else if name = param 11 then some (mapParam 11, 320)
    else none
  tensorMaps
    | 64 => some ⟨2, exampleParams.qMap⟩
    | 192 => some ⟨3, exampleParams.oMap⟩
    | 320 => some ⟨2, exampleParams.biasMap⟩
    | _ => none

/-- The example has variable lengths, distinct physical pages, nonzero sheared bias
and both a query-stage tail and a KV-page tail. -/
theorem example_features :
    exampleParams.qLength 0 = 129 ∧ exampleParams.qLength 1 = 8 ∧
    exampleParams.page 0 (15 / 16) ≠ exampleParams.page 0 (16 / 16) ∧
    exampleParams.bias 0 0 (exampleParams.biasColumn 0 0 16).toNat = some 1 ∧
    exampleParams.kLength 0 % 16 = 1 := by
  refine ⟨rfl, rfl, by decide, ?_, rfl⟩
  rfl


private theorem two_requests (b : Nat) (hb : b < exampleParams.batch) :
    b = 0 ∨ b = 1 := by
  change b < 2 at hb
  omega

private theorem example_allocated (l : Loc) : exampleMemory l ≠ none := by
  simp only [exampleMemory]
  repeat' first | split | exact Option.some_ne_none _

private theorem example_shape_valid : exampleLaunch.Valid kernel := by
  refine ⟨Launch.oneDimLaunch_clusterGridValid (by
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩), ?_, ?_, ?_⟩
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

private theorem example_bf16 {a k : Nat} (hk : k < 2)
    (ha : 12368 ≤ a + k ∧ a + k < 4194304)
    (heven : a % 2 = 0) :
    exampleMemory (globalLoc (a + k)) = some (some ((Value.float .bf16 0).byteAt k)) := by
  have h0 : ¬ (4096 ≤ a + k ∧ a + k < 4108) := by omega
  have h1 : ¬ (8192 ≤ a + k ∧ a + k < 8200) := by omega
  have h2 : ¬ (12288 ≤ a + k ∧ a + k < 12368) := by omega
  have h3 : ¬ (4194304 ≤ a + k ∧ a + k < 4194304 + 2560 * 6 * 265) := by omega
  have hm : (a + k) % 2 = k := by omega
  simp only [exampleMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_right h0,
    ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, hm]

theorem example_pre : Pre exampleParams exampleLaunch exampleMemory := by
  constructor
  case launch => exact example_shape_valid
  case grid => decide
  case block => rfl
  case cluster => exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  case shape => decide
  case lengths =>
    intro b hb
    rcases two_requests b hb with rfl | rfl <;> decide
  case pageTable =>
    intro b hb
    rcases two_requests b hb with rfl | rfl <;> decide
  case values =>
    intro i hi
    simp only [Params.scalarWords, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by decide, by kernel_rfl⟩
  case objectBytes =>
    intro i off bytes value h
    simp only [Params.objectWords, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, hoff, hbytes, hvalue⟩ := h
      subst i off bytes value
      decide +kernel
  case scales =>
    refine ⟨4278775 / 33554432, 11863283 / 1048576, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · kernel_rfl
    · norm_num
    · norm_num
  case maps =>
    intro i address binding hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi
    all_goals
      simp only [Prod.mk.injEq] at hi
      obtain ⟨hi, ha, hd⟩ := hi
      subst i address binding
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
    change b ≤ 2 at hb
    change k < 4 at hk
    let a := 4096 + 4 * b + k
    have hp : 4096 ≤ a ∧ a < 4108 := by unfold a; omega
    have hdiv : (a - 4096) / 4 = b := by unfold a; omega
    have hmod : (a - 4096) % 4 = k := by unfold a; omega
    change exampleMemory (globalLoc a) =
      some (some (wordByte 32 k (exampleParams.qOffset b)))
    simp only [exampleMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_left hp,
      hdiv, hmod]
  case usedK =>
    intro b hb k hk
    change b < 2 at hb
    change k < 4 at hk
    let a := 8192 + 4 * b + k
    have h0 : ¬ (4096 ≤ a ∧ a < 4108) := by unfold a; omega
    have hp : 8192 ≤ a ∧ a < 8200 := by unfold a; omega
    have hdiv : (a - 8192) / 4 = b := by unfold a; omega
    have hmod : (a - 8192) % 4 = k := by unfold a; omega
    change exampleMemory (globalLoc a) =
      some (some (wordByte 32 k (exampleParams.kLength b)))
    simp only [exampleMemory, globalLoc, ne_eq, not_true_eq_false, ite_false,
      ite_eq_right h0, ite_eq_left hp, hdiv, hmod]
  case pageBytes =>
    intro b hb i hi k hk
    change b < 2 at hb
    change k < 4 at hk
    have hi' : i < 10 := by
      rcases two_requests b hb with rfl | rfl
      · exact hi
      · change i < 2 at hi
        omega
    let a := 12288 + 4 * (b * 10 + i) + k
    have h0 : ¬ (4096 ≤ a ∧ a < 4108) := by unfold a; omega
    have h1 : ¬ (8192 ≤ a ∧ a < 8200) := by unfold a; omega
    have hp : 12288 ≤ a ∧ a < 12368 := by unfold a; omega
    have hd : (a - 12288) / 4 = b * 10 + i := by unfold a; omega
    have hm : (a - 12288) % 4 = k := by unfold a; omega
    have hbatch : (b * 10 + i) / 10 = b := by omega
    have hpage : (b * 10 + i) % 10 = i := by omega
    change exampleMemory (globalLoc a) =
      some (some (wordByte 32 k (exampleParams.page b i)))
    simp only [exampleMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_right h0,
      ite_eq_right h1, ite_eq_left hp, hd, hm, hbatch, hpage]
  case qBytes =>
    intro q hq h hh d hd k hk
    change q < 137 at hq
    change h < 6 at hh
    change k < 2 at hk
    apply example_bf16 (a := 262144 + 2 * ((q * 6 + h) * 128 + d)) hk
    · omega
    · omega
  case kvBytes =>
    intro p hp h hh r hr d hd
    change p < 10 at hp
    change h < 1 at hh
    refine ⟨?_, ?_⟩
    · intro k hk
      change k < 2 at hk
      apply example_bf16 (a := 1048576 + 2 * (p * 2048 + h * 128 + r * 128 + d)) hk
      · omega
      · omega
    · intro k hk
      change k < 2 at hk
      apply example_bf16 (a := 2097152 + 2 * (p * 2048 + h * 128 + r * 128 + d)) hk
      · omega
      · omega
  case biasBytes =>
    intro q hq h hh col hc k hk
    change q < 265 at hq
    change h < 6 at hh
    have hk' : k < 2 := by
      cases he : exampleParams.bias q h col <;> rw [he] at hk <;> exact hk
    let a := 4194304 + 2 * ((q * 6 + h) * 1280 + col) + k
    have h0 : ¬ (4096 ≤ a ∧ a < 4108) := by unfold a; omega
    have h1 : ¬ (8192 ≤ a ∧ a < 8200) := by unfold a; omega
    have h2 : ¬ (12288 ≤ a ∧ a < 12368) := by unfold a; omega
    have hp : 4194304 ≤ a ∧ a < 4194304 + 2560 * 6 * 265 := by unfold a; omega
    have hdiv : (a - 4194304) / 2 = (q * 6 + h) * 1280 + col := by unfold a; omega
    have hmod : (a - 4194304) % 2 = k := by unfold a; omega
    have hq' : ((q * 6 + h) * 1280 + col) / 7680 = q := by omega
    have hh' : ((q * 6 + h) * 1280 + col) / 1280 % 6 = h := by omega
    have hc' : ((q * 6 + h) * 1280 + col) % 1280 = col := by omega
    change exampleMemory (globalLoc a) =
      some (some ((biasValue (exampleParams.bias q h col)).byteAt k))
    simp only [exampleMemory, globalLoc, ne_eq, not_true_eq_false, ite_false, ite_eq_right h0,
      ite_eq_right h1, ite_eq_right h2, ite_eq_left hp, hdiv, hmod, hq', hh', hc']
  case biasMask =>
    intro b hb row hr h hh j col h0 _
    have hp : (if exampleParams.qOffset b + row < 129 then 0 else 1) = b := by
      rcases two_requests b hb with rfl | rfl
      · change row < 129 at hr
        exact ite_eq_left (show 0 + row < 129 by omega)
      · have hn : ¬ (129 + row < 129) := by omega
        exact ite_eq_right hn
    have hr' : exampleParams.qOffset b + row - exampleShape.qOffset b = row := by
      change exampleShape.qOffset b + row - exampleShape.qOffset b = row
      omega
    change (let req := if exampleParams.qOffset b + row < 129 then 0 else 1
      let r := exampleParams.qOffset b + row - exampleShape.qOffset req
      (if (col.toNat : Int) < exampleShape.biasColumn req r (exampleShape.keyCount req r)
        then (some (1 : ℝ)) else none).isSome) = decide (j < exampleParams.keyCount b row)
    dsimp only
    rw [hp, hr', Int.toNat_of_nonneg h0]
    have hslot : col < exampleShape.biasColumn b row (exampleShape.keyCount b row) ↔
        j < exampleParams.keyCount b row := by
      change exampleShape.biasColumn b row j <
        exampleShape.biasColumn b row (exampleShape.keyCount b row) ↔
          j < exampleShape.keyCount b row
      dsimp only [Params.biasColumn]
      simp only [sub_lt_sub_iff_right, add_lt_add_iff_right, Int.ofNat_lt]
    by_cases hj : j < exampleParams.keyCount b row <;> simp [hslot, hj]
  case outputs => exact fun l _ => example_allocated l
  case shared => exact ⟨rfl, by decide, fun _ _ _ _ => example_allocated _⟩
  case localMemory => exact ⟨rfl, by decide, fun _ _ _ _ => example_allocated _⟩

/-- The audit launch places the O descriptor and the LSE base far above the metadata. -/
public def isolatedParams : Params :=
  { exampleParams with
    oBase := 2 ^ 48
    lseBase := 2 ^ 38
    lseStride := 2 ^ 38 }

/-- The adjusted descriptor and LSE fields are supplied through the same host ABI. -/
public def isolatedLaunch : Launch :=
  { exampleLaunch with
    paramBytes := fun name off =>
      (isolatedParams.objectWords.find? (fun (i, start, span, _) =>
        param i == name && start ≤ off && off < start + span)).map
          fun (_, start, _, word) => leByte word (off - start)
    tensorMaps := fun addr =>
      if addr = 192 then some ⟨3, isolatedParams.oMap⟩ else exampleLaunch.tensorMaps addr }

/-- Every location of the audit memory backed for the original example remains allocated. -/
private theorem isolatedPre : Pre isolatedParams isolatedLaunch exampleMemory := by
  refine { example_pre with
    launch := ?_
    objectBytes := ?_
    maps := ?_
    raggedBase := by decide
    alignment := by decide
    lseStride := by decide
    ranges := ?_
    separate := ?_
    outputs := fun l _ => example_allocated l }
  · refine ⟨example_shape_valid.1, ?_, ?_, ?_⟩
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
  · intro i off bytes value h
    simp only [Params.objectWords, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, hoff, hbytes, hvalue⟩ := h
      subst i off bytes value
      decide +kernel
  · intro i address binding h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    all_goals
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, ha, hd⟩ := h
      subst i address binding
      refine ⟨by kernel_rfl, by decide, by decide, rfl, by decide, ?_⟩
      intro h
      contradiction
  · intro r hr
    simp only [Params.inputRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨by unfold Region.Apart; decide, ?_⟩
    intro r hr
    simp only [Params.inputRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Region.Apart <;> decide

public theorem isolatedExample :
    ∃ m, Pre isolatedParams isolatedLaunch m :=
  ⟨exampleMemory, isolatedPre⟩

public theorem isolatedAddresses :
    isolatedParams.cuQBase = 4096 ∧ isolatedParams.lseBase = 274877906944 ∧
      isolatedParams.lseStride = 274877906944 ∧ 137438953472 ≤ isolatedParams.oMap.base :=
  ⟨rfl, rfl, rfl, by decide⟩

public theorem isolatedSchedule :
    isolatedLaunch.grid = 12 ∧ isolatedParams.batch = 2 ∧ isolatedParams.heads = 6 ∧
      isolatedParams.qLength 0 = 129 ∧ isolatedParams.qLength 1 = 8 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The exact launch O descriptor admits an aligned origin that addresses CuQ. The executed
write guard therefore needs a fact about the actual origin in addition to descriptor validity. -/
theorem arbitraryOutputOriginMayWriteCuQ :
    ∃ (p : Params) (l : Launch) (m : Mem0), Pre p l m ∧
      let s : TensorStore.Spec :=
        ⟨⟨3, p.oMap, fun _ => 0, ⟨.shared, 0, l.sharedBase⟩, none⟩, none⟩
      TensorStore.Valid 0 s ∧ TensorDescriptor.BoxAligned p.oMap s.origin ∧
        TensorStore.writeLoc s 0 0 0 = some (globalLoc p.cuQBase) := by
  refine ⟨exampleParams, exampleLaunch, exampleMemory, example_pre, ?_⟩
  dsimp only
  refine ⟨⟨by decide, by simp, ?_, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro ys h
    cases h
  · simp [TensorDescriptor.BoxAligned]
  · decide

private def adjacentCuQBase : Nat := exampleParams.oBase + exampleParams.oRegion.bytes

private def adjacentParams : Params := { exampleParams with cuQBase := adjacentCuQBase }

private def adjacentLaunch : Launch :=
  { exampleLaunch with
    paramBytes := fun name off =>
      (adjacentParams.objectWords.find? (fun (i, start, span, _) =>
        param i == name && start ≤ off && off < start + span)).map
          fun (_, start, _, word) => leByte word (off - start) }

private def adjacentMemory (loc : Loc) : Option (Option Byte) :=
  if loc.space = .global ∧ adjacentCuQBase ≤ loc.addr ∧ loc.addr < adjacentCuQBase + 12 then
    exampleMemory (globalLoc (4096 + (loc.addr - adjacentCuQBase)))
  else exampleMemory loc

private theorem adjacentMemoryBelow {loc : Loc} (h : loc.addr < adjacentCuQBase) :
    adjacentMemory loc = exampleMemory loc :=
  ite_eq_right (fun hAlias => Nat.not_le_of_gt h hAlias.2.1)

private theorem adjacentMemoryAllocated (loc : Loc) : adjacentMemory loc ≠ none := by
  unfold adjacentMemory
  split <;> apply example_allocated

private theorem adjacentPre : Pre adjacentParams adjacentLaunch adjacentMemory := by
  refine { example_pre with
    objectBytes := ?_
    maps := ?_
    alignment := by decide
    ranges := ?_
    separate := ?_
    cuQ := ?_
    usedK := ?_
    pageBytes := ?_
    qBytes := ?_
    kvBytes := ?_
    biasBytes := ?_
    outputs := fun loc _ => adjacentMemoryAllocated loc
    shared := ⟨rfl, by decide, fun _ _ _ _ => adjacentMemoryAllocated _⟩
    localMemory := ⟨rfl, by decide, fun _ _ _ _ => adjacentMemoryAllocated _⟩ }
  · intro i off bytes value h
    simp only [Params.objectWords, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, hoff, hbytes, hvalue⟩ := h
      subst i off bytes value
      decide +kernel
  · intro i address binding h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    all_goals
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, ha, hd⟩ := h
      subst i address binding
      refine ⟨by kernel_rfl, by decide, by decide, rfl, by decide, ?_⟩
      intro h
      contradiction
  · intro r hr
    simp only [Params.inputRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨by unfold Region.Apart; decide, ?_⟩
    intro r hr
    simp only [Params.inputRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Region.Apart <;> decide
  · intro i hi k hk
    change i ≤ 2 at hi
    change k < 4 at hk
    let addr := adjacentCuQBase + 4 * i + k
    have hLo : adjacentCuQBase ≤ addr := by dsimp [addr]; omega
    have hHi : addr < adjacentCuQBase + 12 := by dsimp [addr]; omega
    have hIndex : addr - adjacentCuQBase = 4 * i + k := by dsimp [addr]; omega
    change adjacentMemory (globalLoc addr) = _
    have hIn : (globalLoc addr).space = .global ∧
        adjacentCuQBase ≤ (globalLoc addr).addr ∧ (globalLoc addr).addr < adjacentCuQBase + 12 :=
      ⟨rfl, hLo, hHi⟩
    rw [adjacentMemory, ite_eq_left hIn]
    change exampleMemory (globalLoc (4096 + (addr - adjacentCuQBase))) = _
    rw [hIndex, ← Nat.add_assoc]
    exact example_pre.cuQ i hi k hk
  · intro i hi k hk
    change i < 2 at hi
    change k < 4 at hk
    change adjacentMemory ((globalLoc (8192 + 4 * i)).at k) = _
    rw [adjacentMemoryBelow (loc := (globalLoc (8192 + 4 * i)).at k) (by
      change 8192 + 4 * i + k < 3298535308288
      omega)]
    exact example_pre.usedK i hi k hk
  · intro b hb i hi k hk
    change b < 2 at hb
    change i < (exampleParams.kLength b + 15) / 16 at hi
    have hi' : i < 10 := hi.trans_le (example_pre.pageTable b hb).1
    change k < 4 at hk
    change adjacentMemory ((globalLoc (12288 + 4 * (b * 10 + i))).at k) = _
    rw [adjacentMemoryBelow (loc := (globalLoc (12288 + 4 * (b * 10 + i))).at k) (by
      change 12288 + 4 * (b * 10 + i) + k < 3298535308288
      omega)]
    exact example_pre.pageBytes b hb i hi k hk
  · intro q hq h hh d hd k hk
    change q < 137 at hq
    change h < 6 at hh
    change k < 2 at hk
    change adjacentMemory ((exampleParams.qLoc q h d).at k) = _
    rw [adjacentMemoryBelow (loc := (exampleParams.qLoc q h d).at k) (by
      change 262144 + 2 * ((q * 6 + h) * 128 + d) + k < 3298535308288
      omega)]
    exact example_pre.qBytes q hq h hh d hd k hk
  · intro page hp h hh r hr d hd
    change page < 10 at hp
    change h < 1 at hh
    constructor
    · intro k hk
      change k < 2 at hk
      change adjacentMemory ((exampleParams.kLayout.loc page h r d).at k) = _
      rw [adjacentMemoryBelow (loc := (exampleParams.kLayout.loc page h r d).at k) (by
        change 1048576 + 2 * (page * 2048 + h * 128 + r * 128 + d) + k < 3298535308288
        omega)]
      exact (example_pre.kvBytes page hp h hh r hr d hd).1 k hk
    · intro k hk
      change k < 2 at hk
      change adjacentMemory ((exampleParams.vLayout.loc page h r d).at k) = _
      rw [adjacentMemoryBelow (loc := (exampleParams.vLayout.loc page h r d).at k) (by
        change 2097152 + 2 * (page * 2048 + h * 128 + r * 128 + d) + k < 3298535308288
        omega)]
      exact (example_pre.kvBytes page hp h hh r hr d hd).2 k hk
  · intro q hq h hh col hc k hk
    change q < 265 at hq
    change h < 6 at hh
    have hk' : k < 2 := by
      change k < (biasValue (exampleParams.bias q h col)).bytes at hk
      cases he : exampleParams.bias q h col <;> rw [he] at hk <;> exact hk
    change adjacentMemory ((exampleParams.biasLoc q h col).at k) = _
    rw [adjacentMemoryBelow (loc := (exampleParams.biasLoc q h col).at k) (by
      change 4194304 + 2 * ((q * 6 + h) * 1280 + col) + k < 3298535308288
      omega)]
    exact example_pre.biasBytes q hq h hh col hc k hk

private def adjacentObserved : Params :=
  { adjacentParams with qOffset := fun i => if i = adjacentParams.batch then 138
      else adjacentParams.qOffset i }

private def adjacentWriter : Nat := 6 * adjacentLaunch.block + 416

private def adjacentStore : TensorStore.Spec :=
  Epilogue.writebackStoreSpec adjacentObserved adjacentLaunch adjacentWriter 1 0 0 0 0

private def adjacentReadState : TState :=
  { pc := 2953
    regs := fun r => ([(2535, PTX.Proof.b32 adjacentLaunch.sharedBase),
      (2390, PTX.Proof.b32 (adjacentLaunch.sharedBase + 208)),
      (7226, PTX.Proof.b32 (2 ^ 30)), (7227, PTX.Proof.b32 0),
      (7290, .ptr 64 false (.param (param 10)) 0),
      (7867, PTX.Proof.b64 (adjacentCuQBase + 4))] : List (Nat × Value)).lookup r }

private theorem adjacentReadToStore :
    ∃ out, Run kernel Assumptions.all adjacentLaunch adjacentWriter adjacentReadState
      [Epilogue.endpointEvent adjacentObserved 1 0, Epilogue.endpointEvent adjacentObserved 1 1,
        ⟨2958, .wait (Epilogue.readyLoc adjacentLaunch adjacentWriter 0) 0 true true .cta⟩,
        ⟨2963, .tensorStore adjacentParams.oMapAddress adjacentStore⟩] (some out) := by
  let t0 := adjacentReadState
  let t1 := next (setReg t0 2392 (PTX.Proof.b32 129))
  let t2 := next (setReg t1 2393 (PTX.Proof.b32 138))
  let t3 := next (setReg (next (setReg (next (setReg t2 2394 (PTX.Proof.b32 (2 ^ 30 + 129))))
    2395 (PTX.Proof.b32 (2 ^ 30 - 9)))) 7229 (PTX.Proof.b32 0))
  let t4 := next (setReg t3 9748 (.pred true))
  let t5 := next (setReg (next (setReg {t4 with pc := 2961} 7868
    (.ptr 64 true (.param (param 10)) 0))) 7869 (PTX.Proof.b64 0))
  let a0 := Epilogue.endpointAccess adjacentObserved 1
  let a1 := Epilogue.endpointAccess adjacentObserved 2
  let b0 := ((PTX.Proof.b32 129).toBytes.map some : List (Option Byte))
  let b1 := ((PTX.Proof.b32 138).toBytes.map some : List (Option Byte))
  let ready := Epilogue.readyLoc adjacentLaunch adjacentWriter 0
  have read0 : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t0
      (Epilogue.endpointEvent adjacentObserved 1 0) (some t1) := by
    refine ⟨.read a0 (afterLoad t0 [2392]), ?_, b0, rfl, rfl, ?_⟩
    · set_option maxRecDepth 100000 in kernel_rfl
    · have hScalar := PTX.Proof.rebuild_scalar (v := PTX.Proof.b32 129) (by decide) rfl
      rw [PTX.Proof.afterLoad_ok rfl rfl hScalar]
      rfl
  have read1 : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t1
      (Epilogue.endpointEvent adjacentObserved 1 1) (some t2) := by
    refine ⟨.read a1 (afterLoad t1 [2393]), ?_, b1, rfl, rfl, ?_⟩
    · set_option maxRecDepth 100000 in kernel_rfl
    · have hScalar := PTX.Proof.rebuild_scalar (v := PTX.Proof.b32 138) (by decide) rfl
      rw [PTX.Proof.afterLoad_ok rfl rfl hScalar]
      rfl
  have readyPath : run kernel Assumptions.all adjacentLaunch adjacentWriter 3 t2 = some t3 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have waitStep : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t3
      ⟨2958, .wait ready 0 true true .cta⟩ (some t4) := by
    refine ⟨.wait ready 0 (fun ok => next (setReg t3 9748 (.pred ok))) true .cta,
      ?_, true, rfl, rfl⟩
    set_option maxRecDepth 100000 in kernel_rfl
  have storePath : run kernel Assumptions.all adjacentLaunch adjacentWriter 3 t4 = some t5 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have storeStep : EStep kernel Assumptions.all adjacentLaunch adjacentWriter t5
      ⟨2963, .tensorStore adjacentParams.oMapAddress adjacentStore⟩ (some (next t5)) := by
    let words : List (BitVec 64) := [0, 2 ^ 30 - 9, 0, 138]
    let source := Epilogue.sharedSlot adjacentLaunch adjacentWriter 0 0
    have hOrigin : Epilogue.originOf words = oCoordinate adjacentObserved 1 0 0 0 := by
      funext axis
      fin_cases axis <;> rfl
    have hCoords : (Epilogue.storeCoords 0 0).mapM (readBits adjacentLaunch adjacentWriter t5 32) =
        .ok words := by kernel_rfl
    have hSource : sharedEffAddr adjacentLaunch adjacentWriter t5 false 2535 3072 =
        .ok source := by kernel_rfl
    have hPolicy : cachePolicyRead adjacentLaunch adjacentWriter t5 (some (.reg 7869)) =
        .ok () := by kernel_rfl
    have hOut := Epilogue.storeTemplate adjacentPre 0 0 adjacentWriter t5 source words
      rfl rfl rfl hCoords hSource (by decide) hPolicy (by
        intro axis
        fin_cases axis <;> decide) (by decide)
    have hSpec : Epilogue.storeSpec adjacentParams source words = adjacentStore := by
      unfold Epilogue.storeSpec
      rw [hOrigin]
      rfl
    refine ⟨.tensorStore adjacentParams.oMapAddress adjacentStore (next t5), ?_, rfl, rfl⟩
    rw [Epilogue.epilogue_out_all_eq_nil (show Epilogue.EpiloguePc t5.pc from
      .inl ⟨by decide, by decide⟩), hOut, hSpec]
  exact ⟨next t5, .step .refl read0 (.step .refl read1 (.step (run_rtg readyPath) waitStep
    (.step (run_rtg storePath) storeStep (.nil _))))⟩

/-- A legal launch admits a local writeback trace in which the observed final CuQ
word increases by one and the resulting store covers that same word. -/
theorem writebackGeometryCanCoverChangedCuQ :
    ∃ (p : Params) (l : Launch) (m : Mem0), Pre p l m ∧ p.qOffset p.batch = 137 ∧
      let changed := { p with qOffset := fun i => if i = p.batch then 138 else p.qOffset i }
      let g := 6 * l.block + 416
      let store := Epilogue.writebackStoreSpec changed l g 1 0 0 0 0
      Epilogue.assignedCoordinates changed 1 6 = (0, 0) ∧
      (⟨store.outer, store.descriptor⟩ : (n : Nat) × Descriptor n) = ⟨3, p.oMap⟩ ∧
      TensorStore.Valid 6 store ∧ BoxAligned store.descriptor store.origin ∧
      (∃ start out, Run kernel Assumptions.all l g start
        [Epilogue.endpointEvent changed 1 0, Epilogue.endpointEvent changed 1 1,
          ⟨2958, .wait (Epilogue.readyLoc l g 0) 0 true true .cta⟩,
          ⟨2963, .tensorStore p.oMapAddress store⟩] (some out)) ∧
      ∀ k < 4, TensorStore.writeLoc store 2 8 k =
        some ((globalLoc (p.cuQBase + 4 * p.batch)).at k) := by
  refine ⟨adjacentParams, adjacentLaunch, adjacentMemory, adjacentPre, rfl, ?_⟩
  refine ⟨by decide +kernel, rfl, ?_, by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_, rfl, rfl, rfl⟩
    intro ys h
    cases h
  · obtain ⟨out, hr⟩ := adjacentReadToStore
    exact ⟨adjacentReadState, out, hr⟩
  · intro k hk
    have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

end
end PTX.Kernels.TmlFa4Fwd

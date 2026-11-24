-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit
open TensorDescriptor

noncomputable section

/-- A single CTA of the batch-invariant path, with eleven raw KV blocks. -/
private def exampleParams (extraLengthPresent : Bool) (mainLength : Option (Fin 130))
    (pageZero : Bool) :
    Params where
  b := 1
  s_q := 1
  topk := 704
  extra_topk := 0
  page := 1
  extraPage := 0
  numBlocks := 1
  extraNumBlocks := 0
  blockStride := 528
  extraBlockStride := 0
  topkLen := fun _ => (mainLength.map Fin.val).getD 704
  extraTopkLen := fun _ => 0
  idx := fun _ _ _ => if pageZero then 0 else -1
  extraIdx := fun _ _ _ => -1
  q := fun _ _ _ _ => 0
  kvByte := fun _ _ => 0
  extraKvByte := fun _ _ => 0
  scale := 1
  sink := fun _ => none
  param0Base := 0
  param1Base := 1024
  qBase := 4096
  outBase := 131072
  lseBase := 262144
  kvBase := 266240
  extraKvBase := 0
  indicesBase := 270336
  extraIndicesBase := 0
  topkLenBase := mainLength.map (fun _ => 274448)
  extraTopkLenBase := if extraLengthPresent then some 274432 else none
  sinkBase := none
  qClass := .small
  oClass := .small
  kvClass := .small
  extraKvClass := .small
  sharedBase := 0

private def scalarWord (extraLengthPresent mainLengthPresent : Bool) (off : Nat) : Nat :=
  if off < 4 then leByte 1 off |>.toNat
  else if off < 12 then leByte 64 (off - 8) |>.toNat
  else if off < 32 then leByte 0x3f800000 (off - 28) |>.toNat
  else if off < 40 then leByte 1 (off - 36) |>.toNat
  else if off < 44 then leByte 704 (off - 40) |>.toNat
  else if off < 80 then leByte 270336 (off - 72) |>.toNat
  else if off < 88 then
    if mainLengthPresent then leByte 274448 (off - 80) |>.toNat else 0
  else if off < 96 then 0
  else if off < 104 then leByte 262144 (off - 96) |>.toNat
  else if off < 144 then 0
  else if off < 152 then
    if extraLengthPresent then (leByte 274432 (off - 144)).toNat else 0
  else if off < 164 then 0
  else if off < 168 then leByte 528 (off - 164) |>.toNat
  else if off < 172 then 0
  else if off < 176 then leByte 704 (off - 172) |>.toNat
  else if off < 180 then leByte 704 (off - 176) |>.toNat
  else if off < 184 then leByte 64 (off - 180) |>.toNat
  else if off < 188 then leByte 64 (off - 184) |>.toNat
  else 0

private def exampleLaunch (extraLengthPresent mainLengthPresent : Bool) : Launch where
  grid := 1
  block := 384
  params := fun _ => none
  clusterPlaces := gridPlace 1 1
  paramObjects := fun name =>
    if name = param "0" then some (scalarsParam, 0)
    else if name = param "1" then some (mapParam, 1024) else none
  paramBytes := fun _ off =>
    some (BitVec.ofNat 8 (scalarWord extraLengthPresent mainLengthPresent off))
  tensorMaps := fun addr =>
    if addr = 1152 then some ⟨3, mapQ 4096 512 32768 32768 1 1 .zero .small⟩
    else if addr = 1536 then some ⟨3, mapO 131072 512 32768 32768 1 1 .zero .small⟩
    else if addr = 1792 then some ⟨1, mapKv 266240 1 528 .small⟩
    else none

private def exampleMemory (mainLength : Option (Fin 130)) (pageZero : Bool) : Mem0 := fun loc =>
  if loc.space = .shared then some none
  else if loc.addr < 131072 then
    some (some ((Value.float .bf16 0).byteAt ((loc.addr - 4096) % 2)))
  else if loc.addr < 266240 then some none
  else if loc.addr < 270336 then some (some (.bits 8 0, 0))
  else if loc.addr < 274432 then
    some (some (word32Byte (if pageZero then 0 else 0xffffffff) (loc.addr % 4)))
  else if loc.addr < 274448 then some (some (word32Byte 0 (loc.addr % 4)))
  else some (some (word32Byte ((mainLength.map Fin.val).getD 704) (loc.addr % 4)))

private theorem validExample (present main : Bool) :
    (exampleLaunch present main).Valid kernel := by
  refine ⟨(by cases present <;> cases main <;> decide +kernel),
    ?_, ?_, ?_⟩
  · rw [kernel_maxThreads]
    intro n hn
    cases hn
    change 384 ≤ 384
    decide
  · intro s hs
    change none = some s at hs
    contradiction
  · intro name p v h
    change (name, p) ∈ [] at h
    simp at h

private theorem examplePre (present : Bool) (mainLength : Option (Fin 130)) (pageZero : Bool) :
    Pre (exampleParams present mainLength pageZero) (exampleLaunch present mainLength.isSome)
      (exampleMemory mainLength pageZero) := by
  constructor
  case launchValid => exact validExample present mainLength.isSome
  case scalePos => norm_num [exampleParams]
  case param0Object => simp [exampleLaunch, exampleParams]
  case param1Object =>
    have h : param "1" ≠ param "0" := by
      intro h
      have hs : ("1" : String) = "0" :=
        (String.append_right_inj (kernel.name ++ "_param_")).mp h
      exact (by decide : ("1" : String) ≠ "0") hs
    simp [exampleLaunch, exampleParams, h]
  case paramScale =>
    refine ⟨0x3f800000, by decide, ?_, ?_⟩
    · cases present <;> cases mainLength.isSome <;> decide +kernel
    · norm_num [exampleParams, f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq,
        FloatFmt.mantBits, FloatFmt.expBits, FloatFmt.bias, FloatFmt.layout]
  all_goals
    simp only [exampleParams, exampleLaunch, intBytes, ptrBytes, tensorBytes, lseBytes, cacheBytes,
      OptionalGlobalRange, OptionalApart, Apart, slotValid]
  all_goals try (solve | rfl | omega)
  case paddedRange =>
    intro _ _
    cases mainLength with
    | none => decide +kernel
    | some n =>
      have hn := n.isLt
      simp [origPadded, ceilToMultiple, topkBlock]
      omega
  case paramTopkLen =>
    cases mainLength with
    | none => exact ⟨by cases present <;> decide +kernel, fun _ _ => rfl⟩
    | some n =>
      refine ⟨?_, by change 274448 % 4 = 0; decide, ?_⟩
      · change ∀ k < 8, some (BitVec.ofNat 8 (scalarWord present true (80 + k))) =
          some (leByte 274448 k)
        cases present <;> decide +kernel
      · intro e he k hk
        refine ⟨?_, fun _ _ => ?_⟩
        · have heq : e = 0 := by omega
          subst e
          have h0 : ¬274448 + k < 131072 := by omega
          have h1 : ¬274448 + k < 266240 := by omega
          have h2 : ¬274448 + k < 270336 := by omega
          have h3 : ¬274448 + k < 274432 := by omega
          have h4 : ¬274448 + k < 274448 := by omega
          have hk0 : (274448 + k) % 4 = k := by omega
          simp [exampleMemory, h0, h1, h2, h3, h4, hk0]
        · have hn := n.isLt
          exact show n.val ≤ 704 by omega
  case topkLenAddressable => cases mainLength <;> simp
  case topkLenApartO => cases mainLength <;> simp
  case topkLenApartLse => cases mainLength <;> simp
  case paramExtraTopkLen =>
    cases present
    · change (∀ k < 8, _) ∧ (∀ e < 1, True)
      exact ⟨by cases mainLength.isSome <;> decide +kernel,
        fun _ _ => trivial⟩
    · change (∀ k < 8, _) ∧ 274432 % 4 = 0 ∧ (∀ e < 1, ∀ k < 4, _ ∧ _)
      refine ⟨by cases mainLength.isSome <;> decide +kernel, by decide, ?_⟩
      intro e he k hk
      have h0 : ¬274432 + 4 * e + k < 131072 := by omega
      have h1 : ¬274432 + 4 * e + k < 266240 := by omega
      have h2 : ¬274432 + 4 * e + k < 270336 := by omega
      have h3 : ¬274432 + 4 * e + k < 274432 := by omega
      have hk0 : (274432 + 4 * e + k) % 4 = k := by omega
      have h4 : 274432 + 4 * e + k < 274448 := by omega
      simp [exampleMemory, h0, h1, h2, h3, h4, hk0]
  case extraTopkLenAddressable => cases present <;> simp
  case extraTopkLenApartO => cases present <;> simp
  case extraTopkLenApartLse => cases present <;> simp
  case qInput =>
    intro e he q hq h hh t ht byte hb
    have haddr : 4096 + 2 * (((e + q) * 64 + h) * 512 + t) + byte < 131072 := by omega
    have hbyte : (4096 + 2 * (((e + q) * 64 + h) * 512 + t) + byte - 4096) % 2 =
        byte := by omega
    simp [Loc.at, exampleMemory, haddr, hbyte]
  case kvInput =>
    intro r hr byte hb
    have hr0 : r = 0 := by omega
    subst r
    have hlo : ¬266240 + byte < 266240 := by omega
    have hmid : ¬266240 + byte < 131072 := by omega
    have hhi : 266240 + byte < 270336 := by omega
    simp [exampleMemory, hlo, hmid, hhi]
  case idxInput =>
    intro e he q hq j hj k hk
    have ha : ¬270336 + 4 * ((e + q) * 704 + j) + k < 270336 := by omega
    have hb : ¬270336 + 4 * ((e + q) * 704 + j) + k < 266240 := by omega
    have hc : ¬270336 + 4 * ((e + q) * 704 + j) + k < 131072 := by omega
    have hd : (270336 + 4 * ((e + q) * 704 + j) + k) % 4 = k := by omega
    have hhi : 270336 + 4 * ((e + q) * 704 + j) + k < 274432 := by omega
    cases pageZero <;> simp [exampleMemory, ha, hb, hc, hd, hhi,
      show i32Bits (-1) = 0xffffffff by rfl, show i32Bits 0 = 0 by rfl]
  case e4m3Ok =>
    intro e he q hq extra j hj t ht
    cases extra <;> simp [rowBytes]
  case ue8m0Ok =>
    intro e he q hq extra j hj t ht
    cases extra <;> simp [rowBytes]
  case oAllocated =>
    intro byte hb
    have hlo : ¬131072 + byte < 131072 := by omega
    have hhi : 131072 + byte < 266240 := by omega
    simp [exampleMemory, hlo, hhi]
  case lseAllocated =>
    intro byte hb
    have hlo : ¬262144 + byte < 131072 := by omega
    have hhi : 262144 + byte < 266240 := by omega
    simp [exampleMemory, hlo, hhi]
  case sharedAllocated => simp [exampleMemory]
  all_goals first
    | solve | simp
    | solve | decide +kernel
    | solve | cases present <;> cases mainLength.isSome <;> decide +kernel

theorem batchInvariant_pre :
    ∃ P L mem0, P.topk = 704 ∧ P.topkLen 0 = 704 ∧ P.topkLenBase = none ∧ Pre P L mem0 :=
  ⟨exampleParams false none false, exampleLaunch false false, exampleMemory none false,
    rfl, rfl, rfl, examplePre false none false⟩

theorem zeroExtraBudget_presentLength_pre :
    ∃ P L mem0, P.extra_topk = 0 ∧ P.extraTopkLen 0 = 0 ∧
      P.extraTopkLenBase = some 274432 ∧ Pre P L mem0 :=
  ⟨exampleParams true none false, exampleLaunch true false, exampleMemory none false,
    rfl, rfl, rfl, examplePre true none false⟩

/-- A present main length pointer supports the first padding boundary and an empty row. -/
theorem presentMainLength_pre (n : Fin 66) :
    ∃ P L mem0, P.topkLenBase = some 274448 ∧ P.topkLen 0 = n.val ∧ Pre P L mem0 := by
  let m : Fin 130 := ⟨n.val, n.isLt.trans (by decide)⟩
  exact ⟨exampleParams false (some m) false, exampleLaunch false true,
    exampleMemory (some m) false, rfl, rfl, examplePre false (some m) false⟩

/-- One CTA with shared base zero and page-zero indices, for auditing buffer reuse at small
runtime lengths. The runtime length determines which entries are used. -/
theorem pageZero_pre (n : Fin 130) :
    ∃ P L mem0, P.b = 1 ∧ P.s_q = 1 ∧ L.sharedBase = 0 ∧ P.topkLen 0 = n.val ∧
      P.extraTopkLen 0 = 0 ∧ (∀ j, P.idx 0 0 j = 0) ∧ Pre P L mem0 :=
  ⟨exampleParams false (some n) true, exampleLaunch false true,
    exampleMemory (some n) true, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
    examplePre false (some n) true⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Audit

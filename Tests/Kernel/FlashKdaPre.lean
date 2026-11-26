-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Spec
public import Lemmas.Flow.Bf16Widen

@[expose] public section

/-!
# The precondition of the FlashKDA forward kernel can be met

The correctness theorem of the FlashKDA forward recurrence kernel (`correct` in
`Kernels/FlashKdaFwd/Theorem.lean`) has one hypothesis, `Pre P L mem0` (`Spec.lean`). There `P`
are the kernel's symbolic parameters (the shape of the batch, the real-valued inputs and the
addresses), `L` is the launch (grid, scalar parameters, parameter objects, tensor maps) and
`mem0` is the memory before the launch. If no `P`, `L` and `mem0` satisfied `Pre`, the theorem
would hold for no launch at all. This file shows that some do (`pre_satisfiable`), by writing
down the smallest batch `Pre` admits (it asks for at least one head and one token) and checking
every field of `Pre` on it.

## The instance (`OneToken`)

* **Batch.** One sequence, one head, one token. The grid is `(1, 1, 1)`: one CTA (thread block)
  of 192 threads, which is its own cluster. The sequence has one tile (a group of 16 consecutive
  tokens); its row 0 is the token and its rows 1 to 15 are padding. The workspace (the buffer the
  preparation kernel fills before this kernel runs) has room for one tile per head
  (`total_tiles = 1`), so it has one slot.
* **Inputs.** Every real input is zero: the 128 values `v` of the token, its gate logit `beta`,
  its key, query and log-decay rows, and the 128 × 128 initial state. The output scale is 1.
* **Workspace.** The six arrays of the tile hold what the preparation contract
  (`Recurrence.Tile.Prepared`) fixes for these inputs. The three arrays of key and query rows
  with the decay applied or removed (`k_decayed`, `q_decayed`, `k_restored`) and the array of
  query-key inner products (`Mqk`) are zero. `g_total`, the decay accumulated over the tile
  (`exp` of a sum of log-decays), is 1 in all 128 features. `INV`, the inverse of a unit
  lower-triangular matrix, is the 16 × 16 identity. These two are nonzero for any inputs: no
  workspace that meets the contract is all zero.
* **`cu_seqlens`.** The two 64-bit integers `0` and `1`: the sequence starts at token 0 and the
  batch has 1 token.
* **Addresses.** The seven global arrays start one mebibyte (`0x100000` bytes) apart, at
  `0x100000` (`cu_seqlens`), `0x200000` (`v`), `0x300000` (`beta`), `0x400000` (workspace),
  `0x500000` (initial state), `0x600000` (final state) and `0x700000` (`out`); the longest of
  them has 65536 bytes. The eleven 256-byte parameter objects lie back to back from `0x1000`.
  The kernel's `shared_mem` starts at address 0 of the CTA's shared window.
* **Memory before the launch** (`memory`). Exactly the bytes `Pre` speaks about are allocated:
  the five input arrays with the contents above (16 + 256 + 2 + 13824 + 65536 bytes), the two
  output arrays with unknown contents (65536 + 256 bytes), and the 98392 bytes of shared memory
  of CTA 0 with unknown contents. Every other location is unallocated.
* **Launch** (`launch`). Besides the shapes it supplies three tables. The six scalar parameters:
  the address of `out`, `T_total = 1` (tokens), `H = 1` (heads), `N = 1` (sequences), the
  address of `cu_seqlens` and `total_tiles = 1`. The eleven by-value parameter objects, each
  holding a tensor map (the descriptor of one global array for the hardware copy engine), all of
  the small allocation class, so that `Pre` asks for no large-allocation backing behind `v` and
  `beta`. And the eight parameter-object bytes the kernel reads: the 32-bit integer 1 at offset
  128 of the objects 0 and 10.
-/

namespace PTX.Kernels.FlashKdaFwd
open PTX TensorDescriptor Recurrence

noncomputable section

namespace OneToken

/-! ## Addresses -/

/-- The global address of `cu_seqlens`, the array of the first-token indices (16 bytes). -/
def offsetsBase : ℕ := 0x100000

/-- The global address of the values `v` (256 bytes). -/
def valuesBase : ℕ := 0x200000

/-- The global address of the gate logits `beta` (2 bytes). -/
def logitsBase : ℕ := 0x300000

/-- The global address of the workspace (13824 bytes). -/
def workspaceBase : ℕ := 0x400000

/-- The global address of the initial state (65536 bytes). -/
def initialBase : ℕ := 0x500000

/-- The global address of the final state (65536 bytes). -/
def finalBase : ℕ := 0x600000

/-- The global address of the output `out` (256 bytes). -/
def outputBase : ℕ := 0x700000

/-- The address of the by-value parameter object `i` (256 bytes each). -/
def objectBase (i : Fin 11) : ℕ := 0x1000 + 256 * i.val

/-! ## Parameters, launch and memory -/

/-- The numbers the workspace holds for the one tile: the preparation contract for a tile whose
keys, queries and log-decays are zero. -/
def tile : Tile where
  decayedKey := fun _ _ => 0
  decayedQuery := fun _ _ => 0
  restoredKey := fun _ _ => 0
  totalDecay := fun _ => 1
  inverse := 1
  score := 0

/-- The symbolic parameters: one sequence of one token, one head, all real inputs zero. -/
def params : Params where
  sequences := 1
  heads := 1
  length := fun _ => 1
  totalTiles := 1
  key := fun _ _ _ _ => 0
  query := fun _ _ _ _ => 0
  logDecay := fun _ _ _ _ => 0
  betaLogit := fun _ _ _ => 0
  value := fun _ _ _ _ => 0
  initial := fun _ _ _ _ => 0
  scale := 1
  tile := fun _ _ _ => tile
  valuesBase := valuesBase
  logitsBase := logitsBase
  workspaceBase := workspaceBase
  initialBase := initialBase
  offsetsBase := offsetsBase
  finalBase := finalBase
  outputBase := outputBase
  objectBase := objectBase
  allocation := fun _ => .small
  sharedBase := 0

/-- The launch: a grid of one CTA of 192 threads, the six scalar parameters (`param "11"` to
`param "16"`: `out_raw_ptr`, `T_total`, `H`, `N`, `cu_seqlens`, `total_tiles`), the eleven
parameter objects (`param "0"` to `param "10"`), the tensor map each of them holds, and the
32-bit integer 1 at offset 128 of the objects 0 and 10. The shapes not written here are the
defaults of `Launch`: the CTA shape `(192, 1, 1)`, the grid shape `(1, 1, 1)`, clusters of the
one shape `(1, 1, 1)` and one cluster. The place of the clusters is written out, because `Pre`
asks for the function `gridPlace` and the default of `Launch` (`ClusterPlace.uniform`) is another
function: the two agree on the one cluster of this launch, number 0, and differ from number 1
on. -/
def launch : Launch where
  grid := 1
  block := 192
  sharedBase := 0
  clusterPlaces := gridPlace 1 1
  params := fun name =>
    if name = param "11" then some (BitVec.ofNat 64 outputBase)
    else if name = param "12" then some (BitVec.ofNat 64 1)
    else if name = param "13" then some (BitVec.ofNat 64 1)
    else if name = param "14" then some (BitVec.ofNat 64 1)
    else if name = param "15" then some (BitVec.ofNat 64 offsetsBase)
    else if name = param "16" then some (BitVec.ofNat 64 1)
    else none
  paramObjects := fun name =>
    if name = param "0" then some (mapObject "0", objectBase 0)
    else if name = param "1" then some (mapObject "1", objectBase 1)
    else if name = param "2" then some (mapObject "2", objectBase 2)
    else if name = param "3" then some (mapObject "3", objectBase 3)
    else if name = param "4" then some (mapObject "4", objectBase 4)
    else if name = param "5" then some (mapObject "5", objectBase 5)
    else if name = param "6" then some (mapObject "6", objectBase 6)
    else if name = param "7" then some (mapObject "7", objectBase 7)
    else if name = param "8" then some (mapObject "8", objectBase 8)
    else if name = param "9" then some (mapObject "9", objectBase 9)
    else if name = param "10" then some (mapObject "10", objectBase 10)
    else none
  tensorMaps := fun address =>
    if address = objectBase 0 then some ⟨2, mapV valuesBase 1 1 .small⟩
    else if address = objectBase 1 then some ⟨0, mapBeta logitsBase 1 1 .small⟩
    else if address = objectBase 2 then some ⟨2, mapKDecayed workspaceBase 1 1 .small⟩
    else if address = objectBase 3 then some ⟨2, mapQDecayed workspaceBase 1 1 .small⟩
    else if address = objectBase 4 then some ⟨2, mapKRestored workspaceBase 1 1 .small⟩
    else if address = objectBase 5 then some ⟨1, mapGTotal workspaceBase 1 1 .small⟩
    else if address = objectBase 6 then some ⟨2, mapInv workspaceBase 1 1 .small⟩
    else if address = objectBase 7 then some ⟨2, mapMqk workspaceBase 1 1 .small⟩
    else if address = objectBase 8 then some ⟨2, mapInitialState initialBase 1 1 .small⟩
    else if address = objectBase 9 then some ⟨2, mapFinalState finalBase 1 1 .small⟩
    else if address = objectBase 10 then some ⟨2, mapOut outputBase 1 1 .small⟩
    else none
  paramBytes := fun name offset =>
    if (name = param "0" ∨ name = param "10") ∧ 128 ≤ offset ∧ offset < 132 then
      some (leByte 1 (offset - 128))
    else none

/-- The byte at offset `o` of the workspace. With one slot, the six arrays start at the offsets
`0` (`k_decayed`), `4096` (`q_decayed`), `8192` (`k_restored`), `12288` (`g_total`), `12800`
(`INV`) and `13312` (`Mqk`). The first three and the last hold the bfloat16 number 0 in every
element, `g_total` the binary32 number 1, and `INV` the identity: element `(row, column)` of
`INV` is at offset `12800 + 32 * row + 2 * column`. -/
def workspaceByte (o : ℕ) : Byte :=
  if o < 12288 then (Value.float .bf16 0).byteAt (o % 2)
  else if o < 12800 then (Value.float .f32 1).byteAt (o % 4)
  else if o < 13312 then
    (Value.float .bf16 (if (o - 12800) / 32 = (o - 12800) % 32 / 2 then 1 else 0)).byteAt (o % 2)
  else (Value.float .bf16 0).byteAt (o % 2)

/-- The content of the global byte at address `a` before the launch: `some (some b)` is the
known byte `b`, `some none` an allocated byte of unknown content, `none` an address that is not
allocated. The regions are, in this order: the entries 0 and 1 of `cu_seqlens` (the integers 0
and 1), `v` and `beta` (the 16-bit pattern 0, which is the bfloat16 number 0), the workspace,
the initial state (the binary32 number 0), and the two output arrays. -/
def globalByte (a : ℕ) : Option (Option Byte) :=
  if offsetsBase ≤ a ∧ a < offsetsBase + 8 then
    some (some (word64Byte 0 (a - offsetsBase)))
  else if offsetsBase + 8 ≤ a ∧ a < offsetsBase + 16 then
    some (some (word64Byte 1 (a - (offsetsBase + 8))))
  else if valuesBase ≤ a ∧ a < valuesBase + 256 then
    some (some ((Value.bits 16 (BitVec.ofNat 64 0)).byteAt ((a - valuesBase) % 2)))
  else if logitsBase ≤ a ∧ a < logitsBase + 2 then
    some (some ((Value.bits 16 (BitVec.ofNat 64 0)).byteAt (a - logitsBase)))
  else if workspaceBase ≤ a ∧ a < workspaceBase + 13824 then
    some (some (workspaceByte (a - workspaceBase)))
  else if initialBase ≤ a ∧ a < initialBase + 65536 then
    some (some ((Value.float .f32 0).byteAt ((a - initialBase) % 4)))
  else if finalBase ≤ a ∧ a < finalBase + 65536 then some none
  else if outputBase ≤ a ∧ a < outputBase + 256 then some none
  else none

/-- The memory before the launch: the global bytes of `globalByte`, and the `sharedBytes` bytes
of shared memory of CTA 0 that the kernel uses, allocated with unknown contents. Nothing else is
allocated. -/
def memory : Mem0
  | ⟨.global, 0, a⟩ => globalByte a
  | ⟨.shared, 0, a⟩ => if a < sharedBytes then some none else none
  | _ => none

/-! ## Shapes and sizes of the instance -/

/-- Parameter names are distinct for distinct indices: `param i` is a fixed prefix followed by
`i`. The proof does not evaluate the prefix, which contains the kernel's 1,400-character mangled
name. -/
theorem param_inj {i j : String} : param i = param j ↔ i = j := by
  unfold param
  exact String.append_right_inj _

/-- The eleven parameter objects have distinct addresses. -/
theorem objectBase_inj {i j : Fin 11} : objectBase i = objectBase j ↔ i = j := by
  unfold objectBase
  rw [Fin.ext_iff]
  omega

/-- With one token per sequence, sequence `i` starts at token `i`. -/
theorem firstToken_one (i : ℕ) : firstToken (fun _ => 1) i = i := by simp [firstToken]

/-- With one token per sequence, the tiles of sequence `i` start at workspace slot `i`. -/
theorem firstTile_one (i : ℕ) : firstTile (fun _ => 1) i = i := by simp [firstTile, tiles]

/-- The batch has one token. -/
theorem total_eq : params.total = 1 := firstToken_one 1

/-- `v` and `out` have 256 bytes: 128 bfloat16 numbers. -/
theorem tokenBytes_eq : params.tokenBytes = 256 := by
  simp [Params.tokenBytes, Params.total, firstToken_one, params]

/-- `beta` has 2 bytes: one bfloat16 number. -/
theorem logitBytes_eq : params.logitBytes = 2 := by
  simp [Params.logitBytes, Params.total, firstToken_one, params]

/-- The workspace has 13824 bytes: the six arrays of one slot. -/
theorem workspaceBytes_eq : params.workspaceBytes = 13824 := by
  simp [Params.workspaceBytes, Params.slots, params]

/-- A state has 65536 bytes: 128 × 128 binary32 numbers. -/
theorem stateBytes_eq : params.stateBytes = 65536 := by
  simp [Params.stateBytes, params]

/-- `cu_seqlens` has 16 bytes: two 64-bit integers. -/
theorem offsetBytes_eq : params.offsetBytes = 16 := by
  simp [Params.offsetBytes, params]

/-- The seven array bases as numbers, for linear arithmetic. -/
theorem bases_eq : offsetsBase = 0x100000 ∧ valuesBase = 0x200000 ∧ logitsBase = 0x300000 ∧
    workspaceBase = 0x400000 ∧ initialBase = 0x500000 ∧ finalBase = 0x600000 ∧
    outputBase = 0x700000 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Proves an equation between two addresses of the instance: unfolds the memory layout of
`Spec.lean` on the instance, down to sums of the array bases and numerals, and compares the two
sides by linear arithmetic. -/
local macro "address" : tactic =>
  `(tactic| (simp only [Params.offsetLoc, Params.valueLoc, Params.logitLoc, Params.rowLoc,
    Params.totalDecayLoc, Params.squareLoc, Params.initialLoc, Params.array, Params.slot,
    Params.total, workspaceArray, firstToken_one, firstTile_one, Loc.at, params] <;> omega))

/-- Selects the region of `globalByte` or of `workspaceByte` that the hypotheses put the address
in: the conditions of the regions before it are refuted, and its own condition is proved, by
linear arithmetic with the array bases as numbers. -/
local macro "region" : tactic =>
  `(tactic| (have := bases_eq; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]))

/-! ## The contents of the memory, region by region -/

/-- The workspace arrays `k_decayed`, `q_decayed`, `k_restored` (offsets below 12288) and `Mqk`
(offsets from 13312) hold the bfloat16 number 0. -/
theorem workspaceByte_zero {o k : ℕ} (ho : o < 12288 ∨ 13312 ≤ o) (hk : o % 2 = k) :
    workspaceByte o = (Value.float .bf16 0).byteAt k := by
  unfold workspaceByte
  rcases ho with ho | ho
  · rw [ite_eq_left ho, hk]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hk]

/-- The workspace array `g_total` holds the binary32 number 1. -/
theorem workspaceByte_totalDecay {o k : ℕ} (ho : 12288 ≤ o ∧ o < 12800) (hk : o % 4 = k) :
    workspaceByte o = (Value.float .f32 1).byteAt k := by
  unfold workspaceByte
  region
  rw [hk]

/-- The workspace array `INV` holds the 16 × 16 identity matrix. -/
theorem workspaceByte_inverse {o k : ℕ} {t j : Fin 16} (ho : o = 12800 + 32 * t + 2 * j + k)
    (hk : k < 2) :
    workspaceByte o = (Value.float .bf16 ((1 : Matrix (Fin 16) (Fin 16) ℝ) t j)).byteAt k := by
  have h1 : (o - 12800) / 32 = t := by omega
  have h2 : (o - 12800) % 32 / 2 = j := by omega
  have h3 : o % 2 = k := by omega
  unfold workspaceByte
  region
  rw [h1, h2, h3, Matrix.one_apply]
  simp only [Fin.val_inj]

/-- Entry 0 of `cu_seqlens` is the 64-bit integer 0. -/
theorem memory_offset0 {a k : ℕ} (ha : a = offsetsBase + k) (hk : k < 8) :
    memory ⟨.global, 0, a⟩ = some (some (word64Byte 0 k)) := by
  have e : a - offsetsBase = k := by omega
  show globalByte a = _
  unfold globalByte
  region
  rw [e]

/-- Entry 1 of `cu_seqlens` is the 64-bit integer 1. -/
theorem memory_offset1 {a k : ℕ} (ha : a = offsetsBase + 8 + k) (hk : k < 8) :
    memory ⟨.global, 0, a⟩ = some (some (word64Byte 1 k)) := by
  have e : a - (offsetsBase + 8) = k := by omega
  show globalByte a = _
  unfold globalByte
  region
  rw [e]

/-- Every element of `v` is the 16-bit pattern 0. -/
theorem memory_values {a o k : ℕ} (ha : a = valuesBase + o) (ho : o < 256) (hk : o % 2 = k) :
    memory ⟨.global, 0, a⟩ = some (some ((Value.bits 16 (BitVec.ofNat 64 0)).byteAt k)) := by
  have e : a - valuesBase = o := by omega
  show globalByte a = _
  unfold globalByte
  region
  rw [e, hk]

/-- The one element of `beta` is the 16-bit pattern 0. -/
theorem memory_logits {a k : ℕ} (ha : a = logitsBase + k) (hk : k < 2) :
    memory ⟨.global, 0, a⟩ = some (some ((Value.bits 16 (BitVec.ofNat 64 0)).byteAt k)) := by
  have e : a - logitsBase = k := by omega
  show globalByte a = _
  unfold globalByte
  region
  rw [e]

/-- The byte at offset `o` of the workspace is `workspaceByte o`. -/
theorem memory_workspace {a o : ℕ} {b : Byte} (ha : a = workspaceBase + o) (ho : o < 13824)
    (hb : workspaceByte o = b) : memory ⟨.global, 0, a⟩ = some (some b) := by
  have e : a - workspaceBase = o := by omega
  show globalByte a = _
  unfold globalByte
  region
  rw [e, hb]

/-- Every entry of the initial state is the binary32 number 0. -/
theorem memory_initial {a o k : ℕ} (ha : a = initialBase + o) (ho : o < 65536)
    (hk : o % 4 = k) :
    memory ⟨.global, 0, a⟩ = some (some ((Value.float .f32 0).byteAt k)) := by
  have e : a - initialBase = o := by omega
  show globalByte a = _
  unfold globalByte
  region
  rw [e, hk]

/-- The final state is allocated, with unknown contents. -/
theorem memory_final {k : ℕ} (hk : k < 65536) :
    memory ⟨.global, 0, finalBase + k⟩ = some none := by
  show globalByte _ = _
  unfold globalByte
  region

/-- The output is allocated, with unknown contents. -/
theorem memory_output {k : ℕ} (hk : k < 256) :
    memory ⟨.global, 0, outputBase + k⟩ = some none := by
  show globalByte _ = _
  unfold globalByte
  region

/-! ## The fields of `Pre` about the launch -/

/-- The launch is one the kernel's declarations admit: its counts are the products of its
shapes, the one cluster is the one CTA, and the block of 192 threads is within `.maxntid`. -/
theorem launch_valid : launch.Valid kernel := by
  unfold Launch.Valid
  refine ⟨by decide, fun n h => ?_, fun s h => ?_, fun name p v h => ?_⟩
  · rw [kernel_maxThreads] at h
    cases h
    exact Nat.le_refl 192
  · rw [kernel_reqThreads] at h
    cases h
  · rw [kernel_ptrParams] at h
    cases h

/-- The four bytes at offset 128 of the parameter objects 0 and 10 are the 32-bit integer 1. -/
theorem scale_stored {i : String} (hi : i = "0" ∨ i = "10") :
    intBytes 1 128 (param i) launch := by
  intro k hk
  simp only [launch]
  rw [ite_eq_left ⟨by simpa only [param_inj] using hi, by omega, by omega⟩,
    Nat.add_sub_cancel_left]

/-! ## The fields of `Pre` about the inputs -/

/-- `cu_seqlens` holds the first-token indices 0 and 1. -/
theorem offsets_stored (i : ℕ) (hi : i ≤ 1) (k : ℕ) (hk : k < 8) :
    memory ((params.offsetLoc i).at k) =
      some (some (word64Byte (firstToken params.length i) k)) := by
  rw [show firstToken params.length i = i from firstToken_one i]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · exact memory_offset0 (by address) hk
  · exact memory_offset1 (by address) hk

/-- The 128 values of the token are stored as the bfloat16 pattern 0, the number 0. -/
theorem values_stored (v : Fin 128) :
    bf16Bits memory (params.valueLoc (firstToken params.length 0 + 0) 0 v)
      (params.value 0 0 0 v) := by
  unfold bf16Bits
  exact ⟨0, by decide, 0, Flow.bf16_decode_zero, Rat.cast_zero, fun k hk =>
    memory_values (o := 2 * v + k) (by address) (by omega) (by omega)⟩

/-- The gate logit of the token is stored as the bfloat16 pattern 0, the number 0. -/
theorem logits_stored :
    bf16Bits memory (params.logitLoc 0 (firstToken params.length 0 + 0))
      (params.betaLogit 0 0 0) := by
  unfold bf16Bits
  exact ⟨0, by decide, 0, Flow.bf16_decode_zero, Rat.cast_zero, fun k hk =>
    memory_logits (by address) hk⟩

/-- The workspace slot 0 holds the numbers of `tile`. -/
theorem tile_stored : params.TileStored memory 0 tile where
  decayedKey t f k hk :=
    memory_workspace (o := 256 * t + 2 * f + k) (by address) (by omega)
      (workspaceByte_zero (by omega) (by omega))
  decayedQuery t f k hk :=
    memory_workspace (o := 4096 + 256 * t + 2 * f + k) (by address) (by omega)
      (workspaceByte_zero (by omega) (by omega))
  restoredKey t f k hk :=
    memory_workspace (o := 8192 + 256 * t + 2 * f + k) (by address) (by omega)
      (workspaceByte_zero (by omega) (by omega))
  totalDecay f k hk :=
    memory_workspace (o := 12288 + 4 * f + k) (by address) (by omega)
      (workspaceByte_totalDecay (by omega) (by omega))
  inverse t j k hk :=
    memory_workspace (o := 12800 + 32 * t + 2 * j + k) (by address) (by omega)
      (workspaceByte_inverse rfl hk)
  score t j k hk :=
    memory_workspace (o := 13312 + 32 * t + 2 * j + k) (by address) (by omega)
      (workspaceByte_zero (by omega) (by omega))

/-- `tile` is what the preparation kernel stores for a tile of any number `len` of real tokens
whose keys, queries and log-decays are zero, for every output scale: the accumulated decay is 1,
the decayed and restored keys and queries are zero, and the matrix to invert is the identity. -/
theorem tile_prepared (x : Tokens 128) (len : ℕ) (scale : ℝ) (hk : ∀ t, x.key t = 0)
    (hq : ∀ t, x.query t = 0) (hg : ∀ t, x.logDecay t = 0) : tile.Prepared x len scale := by
  have hdecay : ∀ t, masked len x.logDecay t = 0 := fun t => by
    unfold masked
    split_ifs
    · exact hg t
    · rfl
  have hcum : ∀ t, tileCum x len t = fun _ => 1 := fun t => by
    funext i
    simp [tileCum, cum, hdecay]
  have hkey : ∀ t, tileKey x len t = 0 := fun t => by
    unfold tileKey masked
    split_ifs
    · exact hk t
    · rfl
  have hlower : unitLower (coefficient (tileCum x len) (tileKey x len) x.strength) = 1 := by
    ext t j
    by_cases h : t = j <;>
      simp [unitLower, coefficient, dot, restored, weighted, hkey, Matrix.one_apply, h]
  exact {
    decayedKey := fun t => by
      funext i
      simp [weighted, hcum, hkey, tile]
    restoredKey := fun t i => by simp [restored, hcum, hkey, tile]
    totalDecay := (hcum 16).symm
    inverse := by rw [hlower, one_mul]; rfl
    decayedQuery := fun t _ i => by simp [weighted, hcum, hq, tile]
    score := fun t _ j => by simp [dot, tile] }

/-- The initial state is stored as binary32 zeros. -/
theorem initial_stored (v k : Fin 128) :
    f32At memory (params.initialLoc 0 0 v k) (params.initial 0 0 v k) := fun b hb =>
  memory_initial (o := 512 * v + 4 * k + b) (by address) (by omega) (by omega)

/-! ## The fields of `Pre` about the outputs and the shared memory -/

/-- Proves that two arrays of the instance do not overlap, from their bases and lengths. -/
local macro "apart" : tactic =>
  `(tactic| (simp only [Apart, tokenBytes_eq, logitBytes_eq, workspaceBytes_eq, stateBytes_eq,
    offsetBytes_eq]; decide))

/-- `out` overlaps none of the five input arrays. -/
theorem output_inputsApart : params.InputsApart params.outputBase params.tokenBytes where
  offsets := by apart
  values := by apart
  logits := by apart
  workspace := by apart
  initial := by apart

/-- The final state overlaps none of the five input arrays. -/
theorem final_inputsApart : params.InputsApart params.finalBase params.stateBytes where
  offsets := by apart
  values := by apart
  logits := by apart
  workspace := by apart
  initial := by apart

/-- The shared memory the kernel uses is allocated in CTA 0. -/
theorem shared_allocated (byte : ℕ) (hb : byte < sharedBytes) :
    memory ⟨.shared, 0, params.sharedBase + byte⟩ ≠ none := by
  show (if 0 + byte < sharedBytes then some none else none) ≠ none
  rw [ite_eq_left (by omega)]
  exact Option.some_ne_none _

/-! ## The precondition -/

/-- The one-token launch satisfies the precondition of the kernel. The fields are in the order
of `Pre`: (a) the launch shape, (b) the parameters, parameter objects and tensor maps, (c) ranges
and alignment, (d) the contents of the inputs, (e) the outputs, (f) the shared memory. -/
theorem pre : Pre params launch memory where
  -- (a) The launch shape.
  gridShape := rfl
  grid := rfl
  block := rfl
  ntid := rfl
  clusterSize := rfl
  clusterNctaid := rfl
  preferredNctaid := rfl
  nclusters := rfl
  clusterPlaces := rfl
  launchValid := launch_valid
  -- (b) The scalar parameters, the parameter objects and their tensor maps.
  paramOutput := by simp [launch, params]
  paramTokens := by simp [launch, param_inj, Params.total, firstToken_one, params]
  paramHeads := by simp [launch, param_inj, params]
  paramSequences := by simp [launch, param_inj, params]
  paramOffsets := by simp [launch, param_inj, params]
  paramTiles := by simp [launch, param_inj, params]
  object0 := by simp [launch, params]
  object1 := by simp [launch, param_inj, params]
  object2 := by simp [launch, param_inj, params]
  object3 := by simp [launch, param_inj, params]
  object4 := by simp [launch, param_inj, params]
  object5 := by simp [launch, param_inj, params]
  object6 := by simp [launch, param_inj, params]
  object7 := by simp [launch, param_inj, params]
  object8 := by simp [launch, param_inj, params]
  object9 := by simp [launch, param_inj, params]
  object10 := by simp [launch, param_inj, params]
  objectAlign := fun i => by
    show (0x1000 + 256 * i.val) % 128 = 0
    omega
  objectRange := fun i => by
    show 0x1000 + 256 * i.val + 256 ≤ 2 ^ 64
    omega
  objectDistinct := fun _ _ h => objectBase_inj.mp h
  map0 := by simp [launch, Params.total, firstToken_one, params]
  map1 := by simp [launch, objectBase_inj, Params.total, firstToken_one, params]
  map2 := by simp [launch, objectBase_inj, params]
  map3 := by simp [launch, objectBase_inj, params]
  map4 := by simp [launch, objectBase_inj, params]
  map5 := by simp [launch, objectBase_inj, params]
  map6 := by simp [launch, objectBase_inj, params]
  map7 := by simp [launch, objectBase_inj, params]
  map8 := by simp [launch, objectBase_inj, params]
  map9 := by simp [launch, objectBase_inj, params]
  map10 := by simp [launch, objectBase_inj, Params.total, firstToken_one, params]
  scaleV := scale_stored (.inl rfl)
  scaleOut := scale_stored (.inr rfl)
  valuesBacking := fun h => by cases h
  logitsBacking := fun h => by cases h
  -- (c) Ranges and alignment.
  headsPos := Nat.one_pos
  totalPos := by rw [total_eq]; decide
  planesRange := by decide
  tokensRange := by rw [total_eq]; decide
  headTokensRange := by rw [total_eq]; decide
  slotsRange := by decide
  tilesFit := (firstTile_one 1).le
  valuesAlign := by decide
  logitsAlign := by decide
  workspaceAlign := by decide
  initialAlign := by decide
  finalAlign := by decide
  outputAlign := by decide
  offsetsAlign := by decide
  valuesRange := by rw [tokenBytes_eq]; decide
  logitsRange := by rw [logitBytes_eq]; decide
  workspaceRange := by rw [workspaceBytes_eq]; decide
  initialRange := by rw [stateBytes_eq]; decide
  finalRange := by rw [stateBytes_eq]; decide
  outputRange := by rw [tokenBytes_eq]; decide
  offsetsRange := by rw [offsetBytes_eq]; decide
  -- (d) The contents of the inputs.
  offsets := offsets_stored
  values := fun s hs h hh t ht v => by
    obtain rfl : s = 0 := Nat.lt_one_iff.mp hs
    obtain rfl : h = 0 := Nat.lt_one_iff.mp hh
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    exact values_stored v
  logits := fun s hs h hh t ht => by
    obtain rfl : s = 0 := Nat.lt_one_iff.mp hs
    obtain rfl : h = 0 := Nat.lt_one_iff.mp hh
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    exact logits_stored
  workspace := fun s hs h hh b hb => by
    obtain rfl : s = 0 := Nat.lt_one_iff.mp hs
    obtain rfl : h = 0 := Nat.lt_one_iff.mp hh
    obtain rfl : b = 0 := Nat.lt_one_iff.mp hb
    rw [show params.slot 0 0 0 = 0 by address]
    exact tile_stored
  prepared := fun s _ h _ b _ v =>
    tile_prepared _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  initialState := fun s hs h hh v k => by
    obtain rfl : s = 0 := Nat.lt_one_iff.mp hs
    obtain rfl : h = 0 := Nat.lt_one_iff.mp hh
    exact initial_stored v k
  -- (e) The outputs: allocated, apart from each other and from the inputs.
  outputAllocated := fun k hk => by
    rw [tokenBytes_eq] at hk
    exact (memory_output hk).trans_ne (Option.some_ne_none _)
  finalAllocated := fun k hk => by
    rw [stateBytes_eq] at hk
    exact (memory_final hk).trans_ne (Option.some_ne_none _)
  outputApartFinal := by apart
  outputApartInputs := output_inputsApart
  finalApartInputs := final_inputsApart
  -- (f) The shared memory.
  sharedAlignment := by decide
  sharedBase := rfl
  sharedRange := by decide
  sharedAllocated := fun cta hc byte hb => by
    obtain rfl : cta = 0 := Nat.lt_one_iff.mp hc
    exact shared_allocated byte hb

end OneToken

/-- **The precondition of the FlashKDA forward kernel is satisfiable**: the launch `OneToken`
(one sequence, one head, one token, all inputs zero) meets every field of `Pre`. So the
correctness theorem `correct` speaks about at least this launch. -/
theorem pre_satisfiable : ∃ (P : Params) (L : Launch) (mem0 : Mem0), Pre P L mem0 :=
  ⟨OneToken.params, OneToken.launch, OneToken.memory, OneToken.pre⟩

end
end PTX.Kernels.FlashKdaFwd

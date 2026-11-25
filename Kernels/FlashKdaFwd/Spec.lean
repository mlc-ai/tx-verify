-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Async.Tensor.TensorAllocation
public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Data.Fin.VecNotation
public import Kernels.FlashKdaFwd.Data.Decoded
public import Kernels.FlashKdaFwd.Data.Recurrence
public import Kernels.FlashKdaFwd.Data.TensorMaps

@[expose] public section

/-!
# The FlashKDA forward recurrence kernel: specification

The kernel is `_flash_kda_fwd_recurrence` of FlashKDA (`csrc/smxx/fwd_kernel2.cuh:137`), compiled
for a packed batch of variable-length sequences with an FP32 state in and out (template
arguments `CHUNK = 16`, `D = 128`, three input stages, two output stages, 192 threads,
`HasStateIn = HasStateOut = StateFP32 = IsVarlen = true`). The host code that launches it is
`launch_fwd` in `csrc/smxx/fwd_launch.cu`.

Words used below. A *CTA* is one thread block of the launch; this kernel runs one CTA of 192
threads per (sequence, head) pair, on the grid `(N sequences, H heads, 1)`. A *token* is one
position of a sequence; the batch stores its sequences back to back, `T_total` tokens in all. A
*tile* is 16 consecutive tokens of one sequence; the last tile of a sequence may be partial, and
its rows beyond the sequence are *padding* rows. The *workspace* is the buffer in which the
preparation kernel (`_flash_kda_fwd_prepare`, `fwd_kernel1.cuh`), launched before this one,
leaves six arrays per tile; a *slot* is the index of one tile's data in each of these arrays. A
*tensor map* is a host-built descriptor of a global array for the hardware copy engine (TMA).

What the kernel does, for each sequence `s`, head `h` and value channel `v`: starting from the
state row `initial s h v`, it applies the tokens of the sequence in order (`Recurrence.step`).
After token `t` it writes the output `scale * ⟨state, query t⟩` for this token, and after the last
token the final state row. `Post` states exactly that, and that no other global byte changes.

`Pre` describes one launch of the kernel as `fwd_launch.cu` makes it and the memory before it:
the launch shape, the parameters and the eleven tensor maps, number ranges, the input arrays,
the storage of the outputs and the shared-memory window. It says nothing about the execution;
the schedule, the use of buffers, synchronization and termination are proof obligations.

Floating-point values denote exact real numbers under the kernel's assumptions
(`Assumptions.lean`): the workspace, the initial state and the results are real numbers, and
`Post` is the exact real recurrence. Only the two inputs that the kernel reads as bit patterns,
the values `v` and the gate logits `beta`, are stated as finite bfloat16 patterns.

Two limits of the statement, to be read before anything else:

* The program is not upstream FlashKDA but upstream with one added line
  (`checks/proxy_fence.patch`, one more `fence.proxy.async` in the compiled code): the
  unpatched kernel has a data race in the model, so no theorem of this form holds for it.
* The theorem is about exact real arithmetic. `Pre` asks the workspace to hold the exact real
  quantities of the preparation kernel's contract (`Recurrence.Tile.Prepared`), as float
  payloads; a real run of that kernel stores rounded bfloat16 values, so the theorem gives the
  algorithm's correctness over the reals and no bound on rounding error. The preparation kernel
  itself is not verified here.
-/

namespace PTX.Kernels.FlashKdaFwd
open PTX TensorDescriptor Recurrence
noncomputable section

/-- All 3836 decoded instructions of the frozen program (upstream FlashKDA with the one-line
proxy-fence patch of `checks/proxy_fence.patch`). -/
abbrev kernel : Kernel := Decoded.kernel

theorem kernel_code_length : kernel.code.length = 3836 := Decoded.code_length

theorem kernel_groupUniform : kernel.TcGroupUniform := by
  unfold Kernel.TcGroupUniform
  decide +kernel

/-- Bytes of shared memory one CTA uses, from the start of the kernel's `shared_mem`: the BF16
state (32768), the FP32 state buffer shared with the tile buffers (65536) and eleven 8-byte
mbarriers. The host requests `sizeof(SharedStorageK2) = 98432`, this number rounded up to the
structure's 128-byte alignment. -/
def sharedBytes : Nat := 98392

/-- The name of parameter `param_i` of the entry. -/
def param (i : String) : String := kernel.name ++ "_param_" ++ i

/-- The declaration of one of the eleven by-value `TiledCopy` parameters:
`.param .align 128 .b8 name[256]`. The first 128 bytes are the tensor map. -/
def mapObject (i : String) : ParamObjectDecl := ⟨param i, 8, 256, 128⟩

/-- The six scalar parameters of the compiled PTX have the widths of `out_raw_ptr` (64),
`T_total`, `H`, `N` (32 each), `cu_seqlens` (64) and `total_tiles` (32). Their names are
`param "11"` to `param "16"`. That the declared names are these is not stated as a theorem:
Lean's kernel needs about two minutes and ten gigabytes to compare the 1,400-character mangled
names with the computed `param i`. A wrong name could not go unnoticed, since the program
reads its parameters under the declared names and `Pre` supplies them under `param i`. -/
theorem kernel_paramWidths : kernel.params.map Prod.snd = [64, 32, 32, 32, 64, 32] := by
  decide +kernel

/-- The by-value parameters of the compiled PTX are eleven objects `.align 128 .b8 name[256]`
(`mapObject "0"` to `mapObject "10"`; for the names see `kernel_paramWidths`). -/
theorem kernel_paramObjectShapes :
    kernel.paramObjects.map (fun d => (d.elementBits, d.count, d.alignment)) =
      List.replicate 11 (8, 256, 128) := by
  decide +kernel

/-- The PTX declares no aligned pointer parameter, so `Launch.Valid` asks nothing of the two
pointers; `Pre` states their alignment. -/
theorem kernel_ptrParams : kernel.ptrParams = [] := by decide +kernel

/-- The PTX bounds the block size and does not fix it. -/
theorem kernel_maxThreads : kernel.maxThreads = some 192 := by decide +kernel

theorem kernel_reqThreads : kernel.reqThreads = none := by decide +kernel

/-- The kernel has no static shared variable: its shared memory is the launch's dynamic
`shared_mem` array, at `Launch.sharedBase`. -/
theorem kernel_sharedBytes : kernel.sharedBytes = 0 := by decide +kernel

/-- The kernel's symbolic parameters: the shape of the batch, the real-valued inputs, the
workspace contents and the addresses of the launch. Sequences, heads and tokens are numbered
from zero; functions are only read at indices inside the batch. -/
structure Params where
  /-- The number of sequences `N` of the packed batch. -/
  sequences : ℕ
  /-- The number of heads `H`. -/
  heads : ℕ
  /-- The number of tokens of each sequence. -/
  length : ℕ → ℕ
  /-- The capacity `total_tiles` of the workspace, in tiles per head. -/
  totalTiles : ℕ
  /-- Key, query and log-decay rows by `(sequence, head, token)`; the kernel sees them only
  through the workspace. `logDecay` is the natural logarithm of the decay factor (the
  recurrence uses `exp`); the preparation kernel works with base-2 exponents, which are these
  numbers divided by `ln 2`. -/
  key : ℕ → ℕ → ℕ → Row 128
  query : ℕ → ℕ → ℕ → Row 128
  logDecay : ℕ → ℕ → ℕ → Row 128
  /-- The gate logit `beta` by `(sequence, head, token)`. -/
  betaLogit : ℕ → ℕ → ℕ → ℝ
  /-- The value `v` by `(sequence, head, token, value channel)`. -/
  value : ℕ → ℕ → ℕ → Fin 128 → ℝ
  /-- The initial state by `(sequence, head, value channel)`: a row indexed by the key
  feature. -/
  initial : ℕ → ℕ → Fin 128 → Row 128
  /-- The output scale; it reaches the kernel through the workspace array `q_decayed`. -/
  scale : ℝ
  /-- The numbers the workspace holds for tile `b` of `(sequence, head)`, as
  `tile sequence head b`. -/
  tile : ℕ → ℕ → ℕ → Tile
  /-- Global base addresses of the arrays the kernel reads: `v`, `beta`, the workspace, the
  initial state and `cu_seqlens`. -/
  valuesBase : ℕ
  logitsBase : ℕ
  workspaceBase : ℕ
  initialBase : ℕ
  offsetsBase : ℕ
  /-- Global base addresses of the arrays the kernel writes: the final state and `out`. -/
  finalBase : ℕ
  outputBase : ℕ
  /-- The addresses of the eleven by-value parameter objects, by parameter index. -/
  objectBase : Fin 11 → ℕ
  /-- The allocation classes of the eleven tensor maps, by parameter index. -/
  allocation : Fin 11 → AllocationClass
  /-- The address of the kernel's `shared_mem` in the shared window of each CTA. -/
  sharedBase : ℕ

/-! ## The real-valued result -/

/-- The token stream of sequence `s`, head `h` and value channel `v`. The gate strength of a
token is `Recurrence.strength` of its gate logit. -/
def Params.tokens (P : Params) (s h : ℕ) (v : Fin 128) : Tokens 128 where
  key := P.key s h
  query := P.query s h
  value t := P.value s h t v
  strength t := Recurrence.strength (P.betaLogit s h t)
  logDecay := P.logDecay s h

/-- The state row of `(s, h, v)` after the first `t` tokens of sequence `s`. -/
def Params.state (P : Params) (s h : ℕ) (v : Fin 128) (t : ℕ) : Row 128 :=
  tokenState (P.tokens s h v) (P.initial s h v) t

/-- The output of token `t` of sequence `s`, head `h`, value channel `v`: the scaled inner
product of the state after this token with the token's query. -/
def Params.output (P : Params) (s h t : ℕ) (v : Fin 128) : ℝ :=
  P.scale * dot (P.state s h v (t + 1)) (P.query s h t)

/-! ## The layout of global memory (`fwd_launch.cu`) -/

/-- `T_total`: the number of tokens of the packed batch. -/
def Params.total (P : Params) : ℕ := firstToken P.length P.sequences

/-- `n_ht = H * total_tiles`: the number of slots of each workspace array. -/
def Params.slots (P : Params) : ℕ := P.heads * P.totalTiles

/-- `ws_idx`: the workspace slot of tile `b` of sequence `s` and head `h`
(`fwd_kernel2.cuh:384`, `head_idx * total_tiles + tile_base + t`). -/
def Params.slot (P : Params) (s h b : ℕ) : ℕ := h * P.totalTiles + firstTile P.length s + b

/-- The base of the workspace array with per-tile offset `offset` (see `workspaceArray`). -/
def Params.array (P : Params) (offset : ℕ) : ℕ :=
  workspaceArray P.workspaceBase P.heads P.totalTiles offset

/-- Entry `i` of `cu_seqlens`, an `int64`. -/
def Params.offsetLoc (P : Params) (i : ℕ) : Loc := ⟨.global, 0, P.offsetsBase + 8 * i⟩

/-- The value of global token `token`, head `h`, channel `v`: `v` is a bf16 `[T_total, H, 128]`
array. -/
def Params.valueLoc (P : Params) (token h : ℕ) (v : Fin 128) : Loc :=
  ⟨.global, 0, P.valuesBase + 256 * (token * P.heads + h) + 2 * v.val⟩

/-- The gate logit of head `h` and global token `token`: `beta` is a bf16 `[H, T_total]`
array. -/
def Params.logitLoc (P : Params) (h token : ℕ) : Loc :=
  ⟨.global, 0, P.logitsBase + 2 * (h * P.total + token)⟩

/-- Element `(row t, feature f)` of slot `i` of one of the three bf16 `[n_ht, 16, 128]`
workspace arrays, the one at per-tile offset `offset`. -/
def Params.rowLoc (P : Params) (offset i : ℕ) (t : Fin 16) (f : Fin 128) : Loc :=
  ⟨.global, 0, P.array offset + 4096 * i + 256 * t.val + 2 * f.val⟩

/-- Element `f` of slot `i` of the FP32 `[n_ht, 128]` workspace array `g_total`. -/
def Params.totalDecayLoc (P : Params) (i : ℕ) (f : Fin 128) : Loc :=
  ⟨.global, 0, P.array 12288 + 512 * i + 4 * f.val⟩

/-- Element `(row t, column j)` of slot `i` of one of the two bf16 `[n_ht, 16, 16]` workspace
arrays, the one at per-tile offset `offset`. -/
def Params.squareLoc (P : Params) (offset i : ℕ) (t j : Fin 16) : Loc :=
  ⟨.global, 0, P.array offset + 512 * i + 32 * t.val + 2 * j.val⟩

/-- Entry `(value channel v, key feature k)` of the initial state of `(s, h)`: an FP32
`[N * H, 128, 128]` array. -/
def Params.initialLoc (P : Params) (s h : ℕ) (v k : Fin 128) : Loc :=
  ⟨.global, 0, P.initialBase + 65536 * (s * P.heads + h) + 512 * v.val + 4 * k.val⟩

/-- Entry `(value channel v, key feature k)` of the final state of `(s, h)`: an FP32
`[N * H, 128, 128]` array. -/
def Params.stateLoc (P : Params) (s h : ℕ) (v k : Fin 128) : Loc :=
  ⟨.global, 0, P.finalBase + 65536 * (s * P.heads + h) + 512 * v.val + 4 * k.val⟩

/-- The output of token `t` of sequence `s`, head `h`, channel `v`: `out` is a bf16
`[T_total, H, 128]` array, and the token's global index is `firstToken P.length s + t`. -/
def Params.outLoc (P : Params) (s h t : ℕ) (v : Fin 128) : Loc :=
  ⟨.global, 0, P.outputBase + 256 * ((firstToken P.length s + t) * P.heads + h) + 2 * v.val⟩

/-- Bytes of `v` and of `out`. -/
def Params.tokenBytes (P : Params) : ℕ := 256 * (P.total * P.heads)

/-- Bytes of `beta`. -/
def Params.logitBytes (P : Params) : ℕ := 2 * (P.heads * P.total)

/-- Bytes of the six workspace arrays: `13824 = 3 * 4096 + 3 * 512` per slot. -/
def Params.workspaceBytes (P : Params) : ℕ := 13824 * P.slots

/-- Bytes of the initial state and of the final state. -/
def Params.stateBytes (P : Params) : ℕ := 65536 * (P.sequences * P.heads)

/-- Bytes of `cu_seqlens`: `N + 1` entries. -/
def Params.offsetBytes (P : Params) : ℕ := 8 * (P.sequences + 1)

/-! ## Memory contents -/

/-- Byte `k` of a little-endian 64-bit integer in global memory. -/
def word64Byte (x k : Nat) : Byte := (Value.bits 64 (BitVec.ofNat 64 x)).byteAt k

/-- The two bytes at `l` are a raw 16-bit pattern that is the bfloat16 encoding of the finite
number `x`. -/
def bf16Bits (m : Mem0) (l : Loc) (x : ℝ) : Prop :=
  ∃ n < 65536, ∃ q : ℚ, FloatFmt.bf16.decode n = some q ∧ (q : ℝ) = x ∧
    ∀ k < 2, m (l.at k) = some (some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt k))

/-- The two bytes at `l` are the bfloat16 number with the real value `x`, as a float payload:
what a store of a bfloat16 value leaves in memory in this model. -/
def bf16At (m : Mem0) (l : Loc) (x : ℝ) : Prop :=
  ∀ k < 2, m (l.at k) = some (some ((Value.float .bf16 x).byteAt k))

/-- The four bytes at `l` are the binary32 number with the real value `x`, as a float
payload. -/
def f32At (m : Mem0) (l : Loc) (x : ℝ) : Prop :=
  ∀ k < 4, m (l.at k) = some (some ((Value.float .f32 x).byteAt k))

/-- Slot `i` of the six workspace arrays holds the numbers of `w`, every element as a float
payload: `k_decayed`, `q_decayed`, `k_restored` at the per-tile offsets `0`, `4096`, `8192`,
`g_total` at `12288`, `INV` at `12800` and `Mqk` at `13312`. All 16 rows are stated, the padding
rows of a partial tile too: the kernel loads whole tiles. -/
structure Params.TileStored (P : Params) (m : Mem0) (i : ℕ) (w : Tile) : Prop where
  decayedKey : ∀ t f, bf16At m (P.rowLoc 0 i t f) (w.decayedKey t f)
  decayedQuery : ∀ t f, bf16At m (P.rowLoc 4096 i t f) (w.decayedQuery t f)
  restoredKey : ∀ t f, bf16At m (P.rowLoc 8192 i t f) (w.restoredKey t f)
  totalDecay : ∀ f, f32At m (P.totalDecayLoc i f) (w.totalDecay f)
  inverse : ∀ t j, bf16At m (P.squareLoc 12800 i t j) (w.inverse t j)
  score : ∀ t j, bf16At m (P.squareLoc 13312 i t j) (w.score t j)

/-! ## Launch helpers -/

/-- Byte `k` of the little-endian integer `x`. -/
def leByte (x k : Nat) : BitVec 8 := BitVec.ofNat 8 (x / 256 ^ k)

/-- A 32-bit integer field of a by-value parameter object: four little-endian bytes. -/
def intBytes (x off : Nat) (p : String) (L : Launch) : Prop :=
  ∀ k < 4, L.paramBytes p (off + k) = some (leByte x k)

/-- Two byte ranges, of the lengths `an` and `bn`, starting at `a` and `b`, do not overlap. -/
def Apart (an bn a b : Nat) : Prop := a + an ≤ b ∨ b + bn ≤ a

/-- The byte range of `bytes` bytes at `base` overlaps none of the five arrays the kernel
reads. -/
structure Params.InputsApart (P : Params) (base bytes : ℕ) : Prop where
  offsets : Apart bytes P.offsetBytes base P.offsetsBase
  values : Apart bytes P.tokenBytes base P.valuesBase
  logits : Apart bytes P.logitBytes base P.logitsBase
  workspace : Apart bytes P.workspaceBytes base P.workspaceBase
  initial : Apart bytes P.stateBytes base P.initialBase

/-- The cluster placement of an `(N, H, 1)` grid of single-CTA clusters: CTA `k` has
`%ctaid = (k % N, k / N % H, 0)`, so the kernel's `seq_idx = blockIdx.x` is `k % N` and its
`head_idx = blockIdx.y` is `k / N % H`. This is CUDA's linear block order, `x` varying fastest;
`ClusterPlace.uniform` linearizes cluster identifiers with `z` fastest, which for single-CTA
clusters would swap the roles of `%ctaid.x` and `%ctaid.y`. -/
def gridPlace (sequences heads : Nat) : Nat → ClusterPlace := fun k =>
  let p : Dim3 := ⟨k % sequences, k / sequences % heads, 0⟩
  ⟨p, ⟨1, 1, 1⟩, p, ⟨sequences, heads, 1⟩⟩

/-! ## The precondition -/

/-- The launch and the memory before it, without execution or protocol assumptions. -/
structure Pre (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  /-- (a) The launch shape (`fwd_launch.cu:186-214`): grid `(N, H, 1)`, block `(192, 1, 1)`,
  no clusters (every CTA is its own cluster). The PTX only bounds the block size
  (`.maxntid 192`); the kernel's warp roles need exactly 192 threads. -/
  gridShape : L.nctaid = ⟨P.sequences, P.heads, 1⟩
  grid : L.grid = P.sequences * P.heads
  block : L.block = 192
  ntid : L.ntid = ⟨192, 1, 1⟩
  clusterSize : L.clusterSize.val = 1
  clusterNctaid : L.clusterNctaid = ⟨1, 1, 1⟩
  preferredNctaid : L.preferredNctaid = ⟨1, 1, 1⟩
  nclusters : L.nclusters = L.grid
  clusterPlaces : L.clusterPlaces = gridPlace P.sequences P.heads
  launchValid : L.Valid kernel
  /-- (b) The scalar parameters, by name: `out_raw_ptr`, `T_total`, `H`, `N`, `cu_seqlens`,
  `total_tiles` (`fwd_launch.cu:213`). The kernel never reads `N` (parameter 14). -/
  paramOutput : L.params (param "11") = some (BitVec.ofNat 64 P.outputBase)
  paramTokens : L.params (param "12") = some (BitVec.ofNat 64 P.total)
  paramHeads : L.params (param "13") = some (BitVec.ofNat 64 P.heads)
  paramSequences : L.params (param "14") = some (BitVec.ofNat 64 P.sequences)
  paramOffsets : L.params (param "15") = some (BitVec.ofNat 64 P.offsetsBase)
  paramTiles : L.params (param "16") = some (BitVec.ofNat 64 P.totalTiles)
  /-- (b) The eleven by-value `TiledCopy` objects (parameters 0 to 10, in the order of
  `fwd_launch.cu:207-212`): each is an independent 256-byte object at a 128-byte aligned
  address. -/
  object0 : L.paramObjects (param "0") = some (mapObject "0", P.objectBase 0)
  object1 : L.paramObjects (param "1") = some (mapObject "1", P.objectBase 1)
  object2 : L.paramObjects (param "2") = some (mapObject "2", P.objectBase 2)
  object3 : L.paramObjects (param "3") = some (mapObject "3", P.objectBase 3)
  object4 : L.paramObjects (param "4") = some (mapObject "4", P.objectBase 4)
  object5 : L.paramObjects (param "5") = some (mapObject "5", P.objectBase 5)
  object6 : L.paramObjects (param "6") = some (mapObject "6", P.objectBase 6)
  object7 : L.paramObjects (param "7") = some (mapObject "7", P.objectBase 7)
  object8 : L.paramObjects (param "8") = some (mapObject "8", P.objectBase 8)
  object9 : L.paramObjects (param "9") = some (mapObject "9", P.objectBase 9)
  object10 : L.paramObjects (param "10") = some (mapObject "10", P.objectBase 10)
  objectAlign : ∀ i, P.objectBase i % 128 = 0
  objectRange : ∀ i, P.objectBase i + 256 ≤ 2 ^ 64
  objectDistinct : Function.Injective P.objectBase
  /-- (b) The tensor map each object holds (`Data/TensorMaps.lean`): `v`, `beta`, the six
  workspace arrays, the initial state, the final state and `out`. -/
  map0 : L.tensorMaps (P.objectBase 0) =
    some ⟨2, mapV P.valuesBase P.heads P.total (P.allocation 0)⟩
  map1 : L.tensorMaps (P.objectBase 1) =
    some ⟨0, mapBeta P.logitsBase P.heads P.total (P.allocation 1)⟩
  map2 : L.tensorMaps (P.objectBase 2) =
    some ⟨2, mapKDecayed P.workspaceBase P.heads P.totalTiles (P.allocation 2)⟩
  map3 : L.tensorMaps (P.objectBase 3) =
    some ⟨2, mapQDecayed P.workspaceBase P.heads P.totalTiles (P.allocation 3)⟩
  map4 : L.tensorMaps (P.objectBase 4) =
    some ⟨2, mapKRestored P.workspaceBase P.heads P.totalTiles (P.allocation 4)⟩
  map5 : L.tensorMaps (P.objectBase 5) =
    some ⟨1, mapGTotal P.workspaceBase P.heads P.totalTiles (P.allocation 5)⟩
  map6 : L.tensorMaps (P.objectBase 6) =
    some ⟨2, mapInv P.workspaceBase P.heads P.totalTiles (P.allocation 6)⟩
  map7 : L.tensorMaps (P.objectBase 7) =
    some ⟨2, mapMqk P.workspaceBase P.heads P.totalTiles (P.allocation 7)⟩
  map8 : L.tensorMaps (P.objectBase 8) =
    some ⟨2, mapInitialState P.initialBase P.sequences P.heads (P.allocation 8)⟩
  map9 : L.tensorMaps (P.objectBase 9) =
    some ⟨2, mapFinalState P.finalBase P.sequences P.heads (P.allocation 9)⟩
  map10 : L.tensorMaps (P.objectBase 10) =
    some ⟨2, mapOut P.outputBase P.heads P.total (P.allocation 10)⟩
  /-- (b) The only parameter-object bytes the kernel reads besides the maps: the 32-bit word
  at offset 128 of `tma_load_v` and of `tma_store_out` (`ld.param.b32 r, [obj+128]`,
  instructions 1413 and 2949), which it multiplies with the feature coordinate `8 * i` of each
  copy. It is the one run-time member of the object's `AuxTmaParams`: the mangled type lists
  the strides `ScaledBasis<C<1>, 2>`, `ScaledBasis<C<1>, 1>`, `ScaledBasis<int, 0>`, so only the
  scale of TMA dimension 0 is stored. CuTe sets it to the element stride of that dimension in
  the host layout (`cute/atom/copy_traits_sm90_tma.hpp:1093`), and the host layout
  `make_stride(D, D * H, 1)` gives the feature dimension the stride `1` (`fwd_launch.cu:50`).
  The other nine objects have a static unit stride there and store nothing. -/
  scaleV : intBytes 1 128 (param "0") L
  scaleOut : intBytes 1 128 (param "10") L
  /-- (b) A tile's box of `v` or of `beta` can reach past the end of the array (the copy engine
  fills those elements with zero); with a large-class map that needs the device's
  large-allocation backing behind the array. The other nine maps are only used in bounds. -/
  valuesBacking : P.allocation 0 = .large → TensorLargeBacking L mem0 P.valuesBase
  logitsBacking : P.allocation 1 = .large → TensorLargeBacking L mem0 P.logitsBase
  /-- (c) Shape ranges. The batch has a head and a token (CuTe rejects empty tensors); single
  sequences may be empty. The quantities the code computes as signed 32-bit numbers fit: the
  state plane `H * seq + head`, the padded length `seq_len + 15`, the logit index
  `T_total * head + token` and the workspace slot `total_tiles * head + tile_base + t`. The
  workspace has room for the tiles of all sequences. -/
  headsPos : 0 < P.heads
  totalPos : 0 < P.total
  planesRange : P.sequences * P.heads < 2 ^ 31
  tokensRange : P.total + 15 < 2 ^ 31
  headTokensRange : P.heads * P.total < 2 ^ 31
  slotsRange : P.heads * P.totalTiles < 2 ^ 31
  tilesFit : firstTile P.length P.sequences ≤ P.totalTiles
  /-- (c) Addresses: every array lies in the 64-bit address space; the arrays behind tensor
  maps are 16-byte aligned (the copy engine's requirement, asserted by CuTe) and `cu_seqlens`
  is aligned for its 8-byte loads. -/
  valuesAlign : P.valuesBase % 16 = 0
  logitsAlign : P.logitsBase % 16 = 0
  workspaceAlign : P.workspaceBase % 16 = 0
  initialAlign : P.initialBase % 16 = 0
  finalAlign : P.finalBase % 16 = 0
  outputAlign : P.outputBase % 16 = 0
  offsetsAlign : P.offsetsBase % 8 = 0
  valuesRange : P.valuesBase + P.tokenBytes ≤ 2 ^ 64
  logitsRange : P.logitsBase + P.logitBytes ≤ 2 ^ 64
  workspaceRange : P.workspaceBase + P.workspaceBytes ≤ 2 ^ 64
  initialRange : P.initialBase + P.stateBytes ≤ 2 ^ 64
  finalRange : P.finalBase + P.stateBytes ≤ 2 ^ 64
  outputRange : P.outputBase + P.tokenBytes ≤ 2 ^ 64
  offsetsRange : P.offsetsBase + P.offsetBytes ≤ 2 ^ 64
  /-- (d) `cu_seqlens[i]`, for `i ≤ N`, is the global index of the first token of sequence
  `i`, an `int64` (so `cu_seqlens[N] = T_total`). -/
  offsets : ∀ i ≤ P.sequences, ∀ k < 8,
    mem0 ((P.offsetLoc i).at k) = some (some (word64Byte (firstToken P.length i) k))
  /-- (d) The values and the gate logits are finite bfloat16 bit patterns: the kernel widens
  them to FP32 with integer instructions. The sequences are packed back to back, so the tokens
  `firstToken P.length s + t` named here are all `T_total` tokens and these two fields cover
  every element of `v` and of `beta`; a partial tile also loads the rows of the tokens that
  follow its sequence. -/
  values : ∀ s < P.sequences, ∀ h < P.heads, ∀ t < P.length s, ∀ v : Fin 128,
    bf16Bits mem0 (P.valueLoc (firstToken P.length s + t) h v) (P.value s h t v)
  logits : ∀ s < P.sequences, ∀ h < P.heads, ∀ t < P.length s,
    bf16Bits mem0 (P.logitLoc h (firstToken P.length s + t)) (P.betaLogit s h t)
  /-- (d) The workspace holds, for every tile of every sequence and head, the numbers
  `P.tile s h b` as float payloads (`TileStored`), and these numbers are what the preparation
  kernel computes from the 16 tokens of the tile (`Recurrence.Tile.Prepared`; the contract does
  not depend on the value channel `v`). In a partial tile the padding rows of `q_decayed` and
  `Mqk` are left open by that contract: they are finite numbers of any value. -/
  workspace : ∀ s < P.sequences, ∀ h < P.heads, ∀ b < tiles (P.length s),
    P.TileStored mem0 (P.slot s h b) (P.tile s h b)
  prepared : ∀ s < P.sequences, ∀ h < P.heads, ∀ b < tiles (P.length s), ∀ v : Fin 128,
    (P.tile s h b).Prepared (suffix (P.tokens s h v) (16 * b)) (liveRows (P.length s) b) P.scale
  /-- (d) The initial state, as float payloads. -/
  initialState : ∀ s < P.sequences, ∀ h < P.heads, ∀ v k : Fin 128,
    f32At mem0 (P.initialLoc s h v k) (P.initial s h v k)
  /-- (e) The two output arrays are allocated (their contents do not matter), do not overlap
  each other and overlap none of the arrays the kernel reads. Every byte the kernel reads has
  known contents by (d), so the inputs need no separate allocation premise. All arrays are in
  global memory. -/
  outputAllocated : ∀ k < P.tokenBytes, mem0 ⟨.global, 0, P.outputBase + k⟩ ≠ none
  finalAllocated : ∀ k < P.stateBytes, mem0 ⟨.global, 0, P.finalBase + k⟩ ≠ none
  outputApartFinal : Apart P.tokenBytes P.stateBytes P.outputBase P.finalBase
  outputApartInputs : P.InputsApart P.outputBase P.tokenBytes
  finalApartInputs : P.InputsApart P.finalBase P.stateBytes
  /-- (f) The shared-memory window of every CTA: the kernel's `shared_mem` starts at a
  128-byte aligned address (its declared alignment, `.align 128`), and the bytes it uses are
  allocated. -/
  sharedAlignment : P.sharedBase % 128 = 0
  sharedBase : L.sharedBase = P.sharedBase
  sharedRange : P.sharedBase + sharedBytes ≤ 2 ^ 18
  sharedAllocated : ∀ cta < L.grid, ∀ byte < sharedBytes,
    mem0 ⟨.shared, cta, P.sharedBase + byte⟩ ≠ none

/-! ## The postcondition -/

/-- `l` is one of the two bytes of the output of a token of the batch. -/
def Params.OutputByte (P : Params) (l : Loc) : Prop :=
  ∃ s < P.sequences, ∃ h < P.heads, ∃ t < P.length s, ∃ v : Fin 128, ∃ k < 2,
    l = (P.outLoc s h t v).at k

/-- `l` is one of the four bytes of an entry of the final state. -/
def Params.StateByte (P : Params) (l : Loc) : Prop :=
  ∃ s < P.sequences, ∃ h < P.heads, ∃ v : Fin 128, ∃ k : Fin 128, ∃ b < 4,
    l = (P.stateLoc s h v k).at b

/-- The final global memory: every token's output is the scaled inner product of the state
after that token with the token's query; the final state of every sequence and head is the
state after its last token (the initial state for an empty sequence); and every other global
byte is as before the launch. The outputs of the tokens of the batch are all of `out`, since
the sequences are packed; the kernel writes the padding rows of a partial tile nowhere.

The results are stated as float payloads (`bf16At`, `f32At`), the form in which `Pre` asks for
the initial state: the final state of one launch can be the initial state of the next. Read as
numbers they are these reals (`memFloat fmt m l = .ok x`; `Theorem.lean` states this reading). -/
def Post (P : Params) (mem0 : Mem0) (m : FinalMem) : Prop :=
  (∀ s < P.sequences, ∀ h < P.heads, ∀ t < P.length s, ∀ v : Fin 128,
    bf16At m (P.outLoc s h t v) (P.output s h t v)) ∧
  (∀ s < P.sequences, ∀ h < P.heads, ∀ v k : Fin 128,
    f32At m (P.stateLoc s h v k) (P.state s h v (P.length s) k)) ∧
  ∀ l, l.space = .global → ¬ P.OutputByte l → ¬ P.StateByte l → m l = mem0 l

/-! ## Consequences of the precondition -/

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- A batch with a token has a tile. -/
theorem firstTile_pos {length : ℕ → ℕ} {n : ℕ} (h : 0 < firstToken length n) :
    0 < firstTile length n := by
  by_contra h0
  have hz : firstTile length n = 0 := by omega
  have ht : ∀ j ∈ Finset.range n, tiles (length j) = 0 := Finset.sum_eq_zero_iff.mp hz
  have : firstToken length n = 0 := Finset.sum_eq_zero fun j hj => by
    have := ht j hj
    unfold tiles at this
    omega
  omega

theorem Pre.sequencesPos (h : Pre P L mem0) : 0 < P.sequences := by
  have ht := h.totalPos
  by_contra h0
  have hz : P.sequences = 0 := by omega
  simp [Params.total, firstToken, hz] at ht

theorem Pre.headsLt (h : Pre P L mem0) : P.heads < 2 ^ 31 :=
  lt_of_le_of_lt (Nat.le_mul_of_pos_right _ h.totalPos) h.headTokensRange

theorem Pre.sequencesLt (h : Pre P L mem0) : P.sequences < 2 ^ 31 :=
  lt_of_le_of_lt (Nat.le_mul_of_pos_right _ h.headsPos) h.planesRange

theorem Pre.tokensValid (h : Pre P L mem0) : 0 < P.total ∧ P.total ≤ 2 ^ 32 :=
  ⟨h.totalPos, by have := h.tokensRange; omega⟩

theorem Pre.headsValid (h : Pre P L mem0) : 0 < P.heads ∧ P.heads < 2 ^ 32 :=
  ⟨h.headsPos, by have := h.headsLt; omega⟩

theorem Pre.slotsValid (h : Pre P L mem0) :
    0 < P.heads * P.totalTiles ∧ P.heads * P.totalTiles ≤ 2 ^ 32 :=
  ⟨Nat.mul_pos h.headsPos (lt_of_lt_of_le (firstTile_pos h.totalPos) h.tilesFit),
    by have := h.slotsRange; omega⟩

theorem Pre.planesValid (h : Pre P L mem0) :
    0 < P.sequences * P.heads ∧ P.sequences * P.heads ≤ 2 ^ 32 :=
  ⟨Nat.mul_pos h.sequencesPos h.headsPos, by have := h.planesRange; omega⟩

/-- A workspace array starts at a 16-byte aligned address. -/
theorem Pre.arrayAlign (h : Pre P L mem0) {offset : ℕ} (ho : offset % 16 = 0) :
    workspaceArray P.workspaceBase P.heads P.totalTiles offset % 16 = 0 := by
  have hw := h.workspaceAlign
  have hm : P.heads * P.totalTiles * offset % 16 = 0 :=
    Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ho) _)
  unfold workspaceArray
  omega

/-- The eleven tensor maps of the launch satisfy the limits of the host API. -/
theorem Pre.mapVValid (h : Pre P L mem0) :
    Valid (mapV P.valuesBase P.heads P.total (P.allocation 0)) :=
  tokenMap_valid h.valuesAlign h.tokensValid h.headsValid

theorem Pre.mapBetaValid (h : Pre P L mem0) :
    Valid (mapBeta P.logitsBase P.heads P.total (P.allocation 1)) :=
  logitMap_valid h.logitsAlign
    ⟨Nat.mul_pos h.headsPos h.totalPos, by have := h.headTokensRange; omega⟩

theorem Pre.mapKDecayedValid (h : Pre P L mem0) :
    Valid (mapKDecayed P.workspaceBase P.heads P.totalTiles (P.allocation 2)) :=
  tileRowsMap_valid (h.arrayAlign (by decide)) h.slotsValid

theorem Pre.mapQDecayedValid (h : Pre P L mem0) :
    Valid (mapQDecayed P.workspaceBase P.heads P.totalTiles (P.allocation 3)) :=
  tileRowsMap_valid (h.arrayAlign (by decide)) h.slotsValid

theorem Pre.mapKRestoredValid (h : Pre P L mem0) :
    Valid (mapKRestored P.workspaceBase P.heads P.totalTiles (P.allocation 4)) :=
  tileRowsMap_valid (h.arrayAlign (by decide)) h.slotsValid

theorem Pre.mapGTotalValid (h : Pre P L mem0) :
    Valid (mapGTotal P.workspaceBase P.heads P.totalTiles (P.allocation 5)) :=
  totalDecayMap_valid (h.arrayAlign (by decide)) h.slotsValid

theorem Pre.mapInvValid (h : Pre P L mem0) :
    Valid (mapInv P.workspaceBase P.heads P.totalTiles (P.allocation 6)) :=
  tileSquareMap_valid (h.arrayAlign (by decide)) h.slotsValid

theorem Pre.mapMqkValid (h : Pre P L mem0) :
    Valid (mapMqk P.workspaceBase P.heads P.totalTiles (P.allocation 7)) :=
  tileSquareMap_valid (h.arrayAlign (by decide)) h.slotsValid

theorem Pre.mapInitialStateValid (h : Pre P L mem0) :
    Valid (mapInitialState P.initialBase P.sequences P.heads (P.allocation 8)) :=
  stateMap_valid h.initialAlign h.planesValid

theorem Pre.mapFinalStateValid (h : Pre P L mem0) :
    Valid (mapFinalState P.finalBase P.sequences P.heads (P.allocation 9)) :=
  stateMap_valid h.finalAlign h.planesValid

theorem Pre.mapOutValid (h : Pre P L mem0) :
    Valid (mapOut P.outputBase P.heads P.total (P.allocation 10)) :=
  tokenMap_valid h.outputAlign h.tokensValid h.headsValid

end
end PTX.Kernels.FlashKdaFwd

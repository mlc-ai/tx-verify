-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Instr
public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.PNat.Defs

@[expose] public section

/-!
# Values, bytes, locations, launch

Data only. A floating payload is an ideal real number, so equality of values is decidable
only classically and the definitions are `noncomputable`: the model is read and reasoned
about, never run.
-/

namespace PTX

noncomputable section

/-! ## OBJ-CLC-RESPONSE — opaque cancellation response
Statement: A cancellation response is an opaque 16-byte value. It remembers which request it answers
  and, when the request succeeded, the three coordinates of the first CTA of the cancelled cluster.
  Copying the response keeps its identity.

Defs: ClcResponse

Source:
- §9.7.15.18–19

Direction: representation

Effect: The 16-byte opaque response retains the dynamic request identity and, on success, the first
  CTA's three coordinates; no bit encoding is asserted. Copying the response preserves its identity;
  multicast replicas are not independent cancellations.
-/
/-- The response of a `clusterlaunchcontrol.try_cancel` request: the identity of the request and,
on success, the coordinates of the first CTA that was cancelled. -/
structure ClcResponse where
  request : Nat
  firstCta : Option (BitVec 32 × BitVec 32 × BitVec 32)
  deriving DecidableEq

/-! ## THREAD-VALUE — register values
Statement: A register value is an integer bit vector of its width, a floating payload as an ideal
  real number in its format, a predicate, a pair of packed values, a symbolic pointer, an opaque
  cancellation response, or a slice of one of these. Every data value has a bit pattern, so integer
  instructions read a float as its bits. A symbolic pointer is a generic or state-space address
  that remembers the memory it names: the target CTA and the producing CTA of a shared address, the
  name of a kernel parameter object, the thread that owns a local address, or the constant memory.
  A cache eviction policy is an opaque 64-bit value, and a NaN whose pattern the manual leaves
  unspecified is an opaque value of its format's width.

Defs: PtrTarget, Value, Value.bytes

Source:
- §5.1.7 (shared windows, quoted in THREAD-SHARED-POINTER)
- §6.4.1.1 (generic address windows, quoted in THREAD-CVTA)
- §5.1.1: "Registers may be typed (signed integer, unsigned integer, floating point, predicate) or
    untyped."
- §5.2 (fundamental types)
- §5.2.5 (packed data types); numeric interpretation selected through ASM-INTERFACE

Direction: representation

Effect: A register value is an integer bit vector of its width; a float payload is the number it
  denotes in its format (an ideal real number under an ideal profile); a predicate is a Boolean; a
  packed value is a pair, low half first. Every data value has a bit pattern (`Value.bitPattern`,
  THREAD-BITS): a float payload's is its encoding in its format, so a register is read as bits by
  integer instructions and as a number by floating ones. A value's size in bytes is its width.
  A symbolic pointer `.ptr w generic sp off` is a `w`-bit address of byte `off` of the memory that
  `sp` names, in its generic representation (`generic = true`) or its state-space one (THREAD-CVTA).
  It assumes no encoding of window bases or CTA-rank bits and has no bit pattern, so arbitrary
  integer inspection of a pointer has no rule, and moves preserve its representation. A shared
  pointer (a generic or `.shared::cluster` address, THREAD-SHARED-POINTER) retains its target CTA
  and the CTA whose thread produced it. A parameter pointer retains the launch-wide parameter name,
  independent of the parameter contents, and its offset is 0, since no rule moves it. A generic
  local pointer retains the thread whose local memory it addresses, and a generic constant pointer
  names the constant memory; local and constant pointers are generic only. A cache eviction policy
  is an opaque 64-bit value without a bit pattern (THREAD-CACHE-POLICY). `.nan fmt` is a NaN of
  format `fmt` whose pattern the manual leaves unspecified (§9.7.3: "Single-precision instructions
  return an unspecified NaN"): it has the format's size and no bit pattern, so a floating
  instruction reads it as NaN (THREAD-NUM), a store and reload keep it, and every reader that needs
  its bits faults.
-/

/-- The memory a symbolic pointer names (THREAD-VALUE). -/
inductive PtrTarget where
  /-- The shared memory of CTA `cta`, in a pointer that a thread of CTA `issuer` produced. -/
  | shared (issuer cta : Nat)
  /-- The kernel parameter object `name`, shared by the whole launch. -/
  | param (name : String)
  /-- The local memory of thread `owner`. -/
  | «local» (owner : Nat)
  /-- The constant memory. -/
  | const
  deriving DecidableEq

/-- A value held in a register or stored in memory (THREAD-VALUE). -/
inductive Value where
  /-- A `width`-bit integer stored zero-extended in 64 bits. -/
  | bits (width : Nat) (x : BitVec 64)
  | float (fmt : FloatFmt) (x : ℝ)
  | pred (b : Bool)
  /-- A `width`-bit symbolic pointer to byte `offset` of the memory `target` names, in its generic
  representation when `generic` holds and in its state-space representation otherwise. -/
  | ptr (width : Nat) (generic : Bool) (target : PtrTarget) (offset : BitVec 64)
  /-- An opaque 16-byte response, with its request identity preserved. -/
  | clc (response : ClcResponse)
  /-- The opaque 64-bit cache eviction policy that `createpolicy` writes (THREAD-CACHE-POLICY). -/
  | policy
  /-- A NaN of format `fmt` whose pattern is unspecified (THREAD-FLOAT). -/
  | nan (fmt : FloatFmt)
  /-- Two values packed into one register or vector element; `lo` is the low half. -/
  | pair (lo hi : Value)
  /-- A byte slice of an opaque payload, preserving its origin across register moves. -/
  | slice (whole : Value) (offset size : Nat)
  deriving DecidableEq

/-- The size of a value in bytes. -/
def Value.bytes : Value → Nat
  | .bits w _ => w / 8
  | .float f _ => f.bytes
  | .pred _ => 0
  | .ptr w _ _ _ => w / 8
  | .clc _ => 16
  | .policy => 8
  | .nan f => f.bytes
  | .pair lo hi => lo.bytes + hi.bytes
  | .slice _ _ size => size

/-! ## MEM-BYTE — memory bytes
Statement: Memory is a set of bytes, and the content of a byte is byte `k` of the value that a write
  stored there, or the content that the initial write `W0` gave it. A packed pair stores its low
  half first.

Defs: Byte, Value.byteAt, Value.toBytes

Source:
- §8.2 (memory is bytes); choice: abstract contents, little-endian packing

Direction: reading

Effect: Memory is a set of bytes, with no global memory state: a byte's content is what a write
  event wrote to it, or what the initial write `W0` wrote. Contents are abstract: byte `k` of a
  stored scalar `Value`. A packed pair stores its low half first (little-endian, external fact
  EXT-ENDIAN).

### EXT-ENDIAN — byte order

Statement: The model stores multi-byte values and packed pairs little-endian, low half first. The
  PTX ISA does not state a byte order for them.

Evidence: CUDA's little-endian memory. PTX ISA §5.2.5 defines the packed data types but gives no
  byte order in memory, so this is not ISA text; the address of each element of a vector access is
  EXT-VECTOR-ELEM.

Direction: reading

Effect: If it does not hold, a value read at a different width or offset than it was written (a byte
  of a word, a half of a packed pair) is not the one the model gives, and every result computed from
  it, including addresses and control flow, may differ from the hardware's. Disclosed by every
  kernel: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64,
  Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.
-/

/-- The content of one memory byte: byte `k` of the stored scalar value `v`. -/
abbrev Byte := Value × Nat

/-- Byte `k` of `v` in memory, little-endian: a packed pair stores `lo` first. -/
def Value.byteAt : Value → Nat → Byte
  | .slice whole offset _, k => whole.byteAt (offset + k)
  | .pair lo hi, k => if k < lo.bytes then lo.byteAt k else hi.byteAt (k - lo.bytes)
  | .clc response, k => (.clc response, k)
  | .policy, k => (.policy, k)
  | .nan f, k => (.nan f, k)
  | .bits w x, k => (.bits w x, k)
  | .float f x, k => (.float f x, k)
  | .pred b, k => (.pred b, k)
  | .ptr w generic target offset, k => (.ptr w generic target offset, k)

/-- The `v.bytes` bytes a write of `v` stores. -/
def Value.toBytes (v : Value) : List Byte := (List.range v.bytes).map v.byteAt

/-! ## ERR-FAULT-REASON — undefined behaviour of one instruction
Statement: A fault names the reason that one instruction has undefined behaviour, and every fault
  makes the whole execution undefined. An instruction form or an arithmetic result for which neither
  the model nor a kernel assumption has a rule is a fault, so no result is left open.

Defs: Fault, Exec

Source:
- §9.7: "behavior is undefined"

Direction: representation

Effect: A fault is the reason an instruction is undefined. Every fault is undefined behaviour of
  the execution (ERR-UNSAFE); the reason is only for reading. `noRule` covers every instruction form
  the model has no rule for, and every arithmetic operation whose result the model does not give: a
  floating operation no assumption supplies a rule for (`mmaRule`, `reduceRule`, scalar floating
  profiles) and operands that are not values of the operation's type. For all arithmetic, scalar
  instructions (`.error .noRule`), MMA (ERR-TC-MMA) and tensor reductions
  (DEP-REDUCTION-VALUES, `ReduceNoRule`) report a missing rule as undefined behaviour, so no result
  is left open.

Review: The sources are the "behavior is undefined" sentences of the individual instruction
  descriptions (§9.7), whose results are not given meaning here.
-/

/-- Undefined behaviour detected by an instruction rule. -/
inductive Fault where
  | pcOutOfRange | uninitialized | typeMismatch | badParam
  | misaligned | badValue | badBarrier
  /-- An instruction form for which neither the core nor a kernel assumption has a rule. -/
  | noRule
  /-- A `trap` instruction (THREAD-RUN). No assumption gives it a rule. -/
  | trap
  deriving DecidableEq, Repr

/-- A rule either returns a result or reports undefined behaviour. -/
abbrev Exec := Except Fault

/-! ## MEM-LOCATION — locations and footprints
Statement: A location is a state space, its owner (the CTA for shared memory, the thread for local
  memory, 0 for global and constant memory) and a byte address. A memory access covers a number of
  bytes from a location, and two accesses overlap when some byte lies in both. Distinct addresses
  are distinct bytes, so launches with aliased addresses are not supported.

Defs: Loc, Loc.at, Loc.InRange, Acc, Acc.Strong, Acc.Covers, Acc.Overlap, Acc.SameFootprint

Source:
- §8.2 (memory operations)
- §8.2.1 (overlap)
- §8.3 (state spaces)
- §8.4: "strong operation A memory fence operation, or a memory operation with a .relaxed , .acquire
    , .release , .acq_rel , .volatile , or .mmio qualifier."
- EXT-LAUNCH (no aliases)

Direction: scope

Effect: A location is a state space, its owner (shared memory is per CTA, local memory per thread;
  global and constant memory use `0`) and a byte address. A footprint is `size` bytes from a
  location; two footprints overlap when some byte is in both. The memory semantics (`.relaxed`,
  `.acquire`, `.release`, both for `.acq_rel`, none for a weak access) and the scope are kept apart
  from footprint equality (`Acc.SameFootprint`); an access with one of these qualifiers is strong
  (`Acc.Strong`, §8.4). Distinct addresses are distinct bytes: §8.2.2 defines aliases (distinct
  virtual addresses that map to one memory location) and does not exclude them, so the model
  supports only launches without aliases, an obligation of EXT-LAUNCH.
-/

/-- A byte location: a state space, its owner and a byte address. -/
structure Loc where
  space : Space
  /-- The CTA owning a shared location, the thread owning a local location; always `0` for global
  and constant memory. -/
  cta : Nat
  addr : Nat
  deriving DecidableEq, Repr

def Loc.at (l : Loc) (k : Nat) : Loc := { l with addr := l.addr + k }

def Loc.InRange (base : Loc) (n : Nat) (l : Loc) : Prop :=
  l.space = base.space ∧ l.cta = base.cta ∧ base.addr ≤ l.addr ∧ l.addr < base.addr + n

instance (base : Loc) (n : Nat) (l : Loc) : Decidable (base.InRange n l) := by
  unfold Loc.InRange; infer_instance

/-- The bytes a memory operation accesses: `size` bytes from `loc` (§8.2). -/
structure Acc where
  loc : Loc
  size : Nat
  /-- Generic-proxy memory semantics; footprint ignores these qualifiers. -/
  acquire : Bool := false
  release : Bool := false
  scope : MbarScope := .cta
  /-- Position of this scalar operation among the elements of its vector access (EXT-VECTOR-ELEM);
  `0` for a scalar access. -/
  elem : Nat := 0
  /-- The `.relaxed` qualifier: with `acquire` and `release` it records the memory semantics, and
  the access is strong when one of the three is set (`Acc.Strong`). -/
  relaxed : Bool := false
  deriving DecidableEq, Repr

/-- The access is a strong operation (§8.4): it has the `.relaxed`, `.acquire`, `.release` or
`.acq_rel` qualifier. -/
def Acc.Strong (a : Acc) : Prop := a.relaxed = true ∨ a.acquire = true ∨ a.release = true

def Acc.SameFootprint (a b : Acc) : Prop := a.loc = b.loc ∧ a.size = b.size

def Acc.Covers (a : Acc) (l : Loc) : Prop := a.loc.InRange a.size l

/-- Two accesses overlap when some byte is in both (§8.2.1). -/
def Acc.Overlap (a b : Acc) : Prop := ∃ l, a.Covers l ∧ b.Covers l

/-! ## PROG-LAUNCH — the launch
Statement: A launch is a grid of CTAs with the same number of threads each, grouped into clusters.
  Each of the grid, the CTA and the cluster has a shape of up to three dimensions, given by its
  extents in `x`, `y` and `z`. A cluster has the regular or the preferred cluster shape, and the
  launch places each cluster in the grid. The launch also fixes whether the cluster
  launch is explicit, the kernel parameters, the host-created tensor maps, the by-value parameter
  objects and the special register values that the driver or the machine sets before a thread
  starts.

Defs: Dim3, Dim3.get, Dim3.prod, Dim3.coord, ClusterPlace, ClusterPlace.uniform, Launch,
  Launch.threads, Launch.OneDim,
  Launch.tidOf, Launch.oneDim_tidOf

Source:
- §5.1.6.1 (kernel parameters)
- §2.2.1: "Each CTA has a 1D, 2D, or 3D shape specified by a three-element vector ntid (with
    elements ntid.x , ntid.y , and ntid.z )."
- §2.2.2: "Each cluster of CTAs has 1D, 2D or 3D shape specified by the parameter cluster_nctaid ."
- §2.2.2: "The total number of CTAs across all the dimensions in the cluster is specified by
    cluster_nctarank ."
- §2.2.2: "If the user specifies the cluster dimensions at launch time then it will be treated as
    explicit cluster launch, otherwise it will be treated as implicit cluster launch with default
    dimension 1x1x1."
- §2.2.3: "Each grid of CTAs has 1D, 2D, or 3D shape specified by the parameter nctaid ."
- §10.2: "The total number of threads in a CTA is (%ntid.x * %ntid.y * %ntid.z) ."
- §10.7: "The %nctaid special register contains a 3D grid shape vector, with each element having a
    value of at least 1 ."
- §9.7.17.1: "warp-rank of a warp is defined as: (%tid.x + %tid.y * %ntid.x + %tid.z * %ntid.x *
    %ntid.y) / 32"

Direction: representation

Applies: Every launch

Premises: None; `Launch.clusterGridValid` (PROG-CLUSTER, part of CORRECT-LAUNCH) relates the
  counts to the shapes.

Effect: Representation of the launch; THREAD-SREG reads its geometry.
  The launch counts its CTAs (`grid`), the threads of a CTA (`block`) and the CTAs of a regular
  cluster (`clusterSize`), and gives the shapes `nctaid`, `ntid` and `clusterNctaid`, whose extents
  multiply to these counts in every launch the theorems speak about (`Launch.clusterGridValid`,
  CORRECT-LAUNCH). `preferredNctaid` is the preferred cluster shape, and `nclusters` and
  `clusterPlaces` place each cluster (PROG-CLUSTER, EXT-PREFERRED-CLUSTER); unless given, the
  clusters are the regular clusters tiling the grid (`ClusterPlace.uniform`). Thread `g` is thread
  `g % block` of CTA `g / block`. The number `g % block` is the linear thread index of §9.7.17.1,
  `%tid.x + %tid.y * %ntid.x + %tid.z * %ntid.x * %ntid.y`, so the thread's `%tid` is
  `Launch.tidOf`, with `x` varying fastest. The CTA number `g / block` is the model's own numbering
  of the CTAs: the CTAs of one cluster are consecutive (PROG-CLUSTER), and PROG-CLUSTER gives the
  `%ctaid` of each number. The shapes default to the one-dimensional shapes of the counts with
  regular clusters (`Launch.OneDim`), in which `Launch.tidOf` is `(g % block, 0, 0)`
  (`Launch.oneDim_tidOf`).
  Parameters are raw bits. `explicitCluster` says whether the cluster dimensions were given at
  launch (`%is_explicit_cluster`); a launch without them has the cluster shape 1x1x1 (§2.2.2,
  CORRECT-LAUNCH). `tensorMaps` supplies the immutable, host-created descriptor properties including
  allocation class available at launch (EXT-LAUNCH); device-side map mutation and dynamic
  tensormap-proxy publication are not modeled. `tensorLargeAllocMinBytes` records the actual device
  attribute when known, never a kernel-selected lower bound. `paramObjects` supplies the actual
  launch ABI bindings for by-value objects; addresses, declarations and descriptor contents must
  agree with the passed host objects (EXT-LAUNCH). `paramBytes` supplies the bytes of those objects,
  which `ld.param` reads (THREAD-MOVE); a byte that is not supplied cannot be read. `sregInit` gives
  each thread the values of the special registers that THREAD-SREG leaves unconstrained. A kernel
  theorem quantifies over the launch, so when its premises do not name `sregInit` it holds for every
  choice of these values.
-/

/-- Extents, or coordinates, in the three dimensions `x`, `y` and `z`. -/
structure Dim3 where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

/-- The component of a dimension. -/
def Dim3.get (d : Dim3) : Dim → Nat
  | .x => d.x
  | .y => d.y
  | .z => d.z

/-- The number of points of a shape: the product of its extents. -/
def Dim3.prod (d : Dim3) : Nat := d.x * d.y * d.z

/-- The coordinates in shape `d` of the point with linear index `i`, with `x` varying fastest:
`i = x + y * d.x + z * d.x * d.y` for `i < d.prod`. -/
def Dim3.coord (d : Dim3) (i : Nat) : Dim3 := ⟨i % d.x, i / d.x % d.y, i / (d.x * d.y)⟩

/-- The place of one cluster in the grid: the `%ctaid` of its CTA of rank 0 (`origin`), its shape
in CTAs (`%cluster_nctaid`), and the `%clusterid` and `%nclusterid` its threads read. -/
structure ClusterPlace where
  origin : Dim3
  shape : Dim3
  id : Dim3
  count : Dim3
  deriving DecidableEq, Repr

/-- The places of the clusters of a grid of shape `grid` tiled by clusters of one shape `cluster`:
cluster `k` has the `%clusterid` whose coordinates in the grid of clusters have linear index `k`
with `z` varying fastest, and its origin is that `%clusterid` times the cluster extents. -/
def ClusterPlace.uniform (grid cluster : Dim3) (k : Nat) : ClusterPlace :=
  let n : Dim3 := ⟨grid.x / cluster.x, grid.y / cluster.y, grid.z / cluster.z⟩
  let id : Dim3 := ⟨k / (n.y * n.z), k / n.z % n.y, k % n.z⟩
  ⟨⟨id.x * cluster.x, id.y * cluster.y, id.z * cluster.z⟩, cluster, id, n⟩

/-- The launch configuration: the counts and shapes of the grid, the CTA and the cluster, kernel
parameters, shared memory base, tensor maps and by-value parameter objects (PROG-LAUNCH). -/
structure Launch where
  /-- The number of CTAs of the grid. -/
  grid : Nat
  /-- The number of threads of a CTA. -/
  block : Nat
  /-- Raw parameter bits, zero-extended. -/
  params : String → Option (BitVec 64)
  /-- Address of the first byte of static shared memory in the shared window. -/
  sharedBase : Nat := 0
  /-- Address of the first `.local` variable in each thread's local memory
  (EXT-LOCAL-CONST-LAYOUT). -/
  localBase : Nat := 0
  /-- Address of the first `.const` variable in the constant memory (EXT-LOCAL-CONST-LAYOUT). -/
  constBase : Nat := 0
  /-- The number of CTAs of a cluster; implicit clusters have size one. -/
  clusterSize : PNat := 1
  /-- Host-created, immutable tensor maps of rank `outer + 1`, published before launch. Device
  updates and descriptors read dynamically through the tensormap proxy need separate rules. -/
  tensorMaps : Nat → Option ((outer : Nat) × TensorDescriptor.Descriptor outer) := fun _ => none
  /-- Actual CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE, when supplied.
  An unknown attribute cannot justify a large-class out-of-bounds operation. -/
  tensorLargeAllocMinBytes : Option Nat := none
  /-- Actual by-value parameter declarations and their generic base addresses.
  This is launch/ABI data, not the scalar bits stored in a parameter. The immutable
  tensorMaps entry at such an address describes that parameter's actual contents. -/
  paramObjects : String → Option (ParamObjectDecl × Nat) := fun _ => none
  /-- Byte `k` of by-value parameter object `name` as passed by the host, if supplied. -/
  paramBytes : String → Nat → Option (BitVec 8) := fun _ _ => none
  /-- The value of special register `s` that the driver or the machine fixes for thread `g` before
  it starts, for the registers THREAD-SREG leaves unconstrained (`SRegKind.initial`). -/
  sregInit : Nat → SReg → Nat := fun _ _ => 0
  /-- The CTA shape `%ntid`; one-dimensional unless given. -/
  ntid : Dim3 := ⟨block, 1, 1⟩
  /-- The grid shape in CTAs, `%nctaid`; one-dimensional unless given. -/
  nctaid : Dim3 := ⟨grid, 1, 1⟩
  /-- The regular cluster shape in CTAs (the CUDA cluster dimension); one-dimensional unless
  given. -/
  clusterNctaid : Dim3 := ⟨clusterSize.val, 1, 1⟩
  /-- The preferred cluster shape in CTAs (EXT-PREFERRED-CLUSTER); the regular shape unless
  given. -/
  preferredNctaid : Dim3 := clusterNctaid
  /-- The number of clusters. -/
  nclusters : Nat := grid / clusterSize.val
  /-- The place of each cluster, by the model's cluster number (PROG-CLUSTER); clusters of the
  regular shape tiling the grid unless given. -/
  clusterPlaces : Nat → ClusterPlace := ClusterPlace.uniform nctaid clusterNctaid
  /-- The cluster dimensions were given at launch (`%is_explicit_cluster`, §2.2.2). -/
  explicitCluster : Bool := decide (clusterSize.val ≠ 1)

/-- The number of threads of the launch. -/
def Launch.threads (L : Launch) : Nat := L.grid * L.block

/-- The launch is one-dimensional with clusters of one shape: the grid, the CTA and the cluster
extend in `x` only, the preferred cluster shape is the regular one, and the clusters are the
regular clusters tiling the grid. -/
def Launch.OneDim (L : Launch) : Prop :=
  L.ntid = ⟨L.block, 1, 1⟩ ∧ L.nctaid = ⟨L.grid, 1, 1⟩ ∧
  L.clusterNctaid = ⟨L.clusterSize.val, 1, 1⟩ ∧ L.nclusters = L.grid / L.clusterSize.val ∧
  L.preferredNctaid = L.clusterNctaid ∧
  L.clusterPlaces = ClusterPlace.uniform L.nctaid L.clusterNctaid

/-- The `%tid` of thread `g`: the coordinates of its linear thread index `g % block` in the CTA
shape. -/
def Launch.tidOf (L : Launch) (g : Nat) : Dim3 := L.ntid.coord (g % L.block)

/-- In a one-dimensional launch `%tid` is `(g % block, 0, 0)`. -/
theorem Launch.oneDim_tidOf {L : Launch} (h : L.OneDim) (g : Nat) :
    L.tidOf g = ⟨g % L.block, 0, 0⟩ := by
  obtain ⟨hn, -⟩ := h
  simp only [Launch.tidOf, Dim3.coord, hn, Nat.mod_mod, Nat.mod_one, Nat.mul_one, Dim3.mk.injEq,
    true_and]
  rcases Nat.eq_zero_or_pos L.block with h0 | hpos
  · simp [h0]
  · exact Nat.div_eq_of_lt (Nat.mod_lt g hpos)

/-! ## PROG-LAUNCH-MEMORY — memory at launch
Statement: At kernel start each byte is either not allocated, allocated with an unknown content, or
  allocated with a known content. An access to an unallocated byte is undefined behaviour, and each
  execution fixes one value for every unknown byte.

Defs: Mem0

Source:
- §8.2.6 (initialization: the initial write W0)
- EXT-LAUNCH

Direction: reading

Effect: `W0` records what it wrote per byte: `none` = not allocated, `some none` = allocated with an
  unknown value, `some (some b)` = byte `b`. `Execution.initial` fixes each unknown byte within an
  execution; it is not the absence of a readable byte. That this describes the device memory at
  kernel start is external fact EXT-LAUNCH.
-/

/-- Memory at launch, as written by `W0` (§8.2.6): `none` = not allocated (any access is
undefined); `some none` = allocated with an unknown constant value; `some (some b)` =
byte `b`. -/
abbrev Mem0 := Loc → Option (Option Byte)

end

end PTX

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorCopy
public import Core.Async.BulkGroup

@[expose] public section

namespace PTX.TensorStore
noncomputable section

/-! ## DEP-TENSOR-STORE-EFFECTS — tensor shared-to-global addresses and independent effects
Statement: A tensor store copies each in-bounds global byte from the corresponding swizzled byte of
  its shared source, and an out-of-bounds element has no global destination. A tensor reduction
  performs each in-bounds element as one read-modify-write that reads the shared byte and the old
  global byte of each element byte. Read completion and full completion are separate, and full
  completion requires every in-bounds write.

Defs: TensorStore.Spec, TensorStore.ReduceSupported, TensorStore.Valid, TensorStore.destination,
  TensorStore.Effects, TensorStore.CopyOk, TensorStore.Extends, TensorStore.Observation,
  TensorStore.Observation.Extends, TensorStore.SnapshotExtends, TensorStore.completion

Source:
- §9.7.10.28.5.3 (tensor shared-to-global)
- §9.7.10.28.5.4 (reduction)
- §9.7.10.28.6.2 (read/full completion)
- CUDA Programming Guide §4.13.4 (negative indices and out of bounds; TMA swizzling)
- EXT-TMA-STORE-OOB

Direction: reading

Applies: Non-interleaved 1D–5D tiled and 2D `.tile::scatter4` shared::cta-to-global tensor stores,
  and 1D–5D tiled `cp.reduce.async.bulk.tensor` reductions

Premises: An immutable published tensor map, a local shared source, and nonnegative coordinates
  (scatter4: also the row coordinates). Source values are constrained by separate read-source/proxy
  rules.

Effect: Address/effect validity and a bulk-group completion adapter. With scatter4 row
  coordinates, box row `r` is tensor row `rows r` (EXT-TMA-SCATTER4). A reduction writes all global
  bytes of an element together, each after reading its shared byte and its old destination byte.
  The written value and the atomicity of concurrent reductions are DEP-REDUCTION-VALUES. The store
  reads the same shared swizzle layout that a matching load would produce. OOB slots may be read or
  skipped in shared memory: the footprint adapter must reserve all selected source slots, and
  neither choice creates a global write. Read completion closes the source observations, so later
  extension cannot add an OOB read after a read wait has permitted source reuse. Full completion
  requires every in-bounds write. The descriptor's input fill policy does not create output
  stores.

### EXT-TMA-STORE-OOB — out-of-bounds elements of a tensor store are not written

Statement: A tiled tensor store whose bounding box crosses the tensor boundary writes only the
  in-bounds elements. An out-of-bounds element has no global destination, and its shared source
  may be read or skipped.

Source:
- §5.5.3.3: "PTX Tensor operation can detect and handle the case when the Bounding Box crosses the
    tensor boundary in any dimension"
- CUDA C++ Programming Guide §4.13.4 (negative indices and out of bounds), read as: out-of-bounds
    elements of a store are not written
- `Tools/probes/tma_scatter4.ptx` and `Tools/probes/tma_reduce.ptx` (rows, columns and elements past
    the extent unwritten or unchanged, on a B200)

Why it is not spec text: The text states the fill of out-of-bounds elements for loads and no rule
  for stores. The two fill modes it lists are stated for the elements of a box "set to 0" or to
  OOB-NaN, which is a load. The probes cover `.tile::scatter4` and tensor reductions; no probe
  stores a plain tiled box across the boundary.

Direction: reading

Effect: If hardware wrote a value for an out-of-bounds element, that write would be missing from
  the model's footprints and conflicts with it would be missed. Disclosed by every kernel whose
  statement names `Op.cpTensorStore`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192.

### EXT-TMA-REDUCE — tensor reductions use the store's layout

Statement: A tensor reduction reads the same swizzled shared layout and reduces the same global
  elements as a tensor store with the same descriptor. Out-of-bounds elements are left unchanged.
  The reduced values are DEP-REDUCTION-VALUES.

Why it is not spec text: §9.7.10.28.5.4 describes the reduction element-wise without restating the
  store layout.

Evidence: On a B200 `Tools/probes/tma_reduce.ptx` with `run_tma_reduce.cu` (2D u32/s32 map,
  pattern-filled shared source) gave every tensor element `old ⊕ src` for the shared element at the
  store's swizzled position, and left out-of-bounds elements and the rest of the tensor unchanged,
  for add, min and max (signed and unsigned), and, or, xor, inc and dec, with no/32B/64B/128B
  swizzles, offsets 0 to 640 and partially out-of-bounds boxes. inc or dec of an s32 map, a
  negative coordinate and an inner start that is not 16-byte aligned fail with an illegal
  instruction; a 64-byte-aligned source is misaligned.

Direction: reading

Effect: The destination element of each reduction and the shared source element it reads are fixed
  by the store's layout; if the hardware layout differs, the reduced tensor differs from the one
  proven. Disclosed by every kernel whose statement names `Op.cpTensorStore (reduce ≠ none)`: none.
-/
/-- A tensor store or reduction: its box, with the shared source, and the reduction operation, if
the instruction is `cp.reduce.async.bulk.tensor`. -/
structure Spec extends TensorBox where
  /-- `cp.reduce.async.bulk.tensor`: the reduction; `none`: a store. -/
  reduce : Option AtomOp := none

/-- The element types of each reduction (§9.7.10.28.5.4 table; `.b32`/`.b64` are the 32- and
64-bit integer formats). The `atom` operations `.exch` and `.cas` are not reductions. -/
def ReduceSupported : AtomOp → TensorDescriptor.Format → Bool
  | .add, f => f ∈ [.u32, .s32, .u64, .f32, .f16, .bf16]
  | .min, f | .max, f => f ∈ [.u32, .s32, .u64, .s64, .f16, .bf16]
  | .inc, f | .dec, f => f = .u32
  | .and, f | .or, f | .xor, f => f ∈ [.u32, .s32, .u64, .s64]
  | .exch, _ | .cas, _ => false

/-- The store is a valid issue by the CTA `issuerCta`: a valid descriptor, nonnegative coordinates,
and a 128-byte aligned shared source in the issuer's own CTA. -/
def Valid (issuerCta : Nat) (s : Spec) : Prop :=
  TensorDescriptor.Valid s.descriptor ∧ (∀ axis, 0 ≤ s.origin axis) ∧
    (∀ ys, s.rows = some ys → ∀ j, 0 ≤ ys j) ∧
    s.sharedBase.space = .shared ∧ s.sharedBase.cta = issuerCta ∧ s.sharedBase.addr % 128 = 0

/-- The global location of a slot's byte, if its element is inside the tensor; the store writes
nothing for other slots. -/
def destination (s : Spec) (slot : TensorTransfer.Slot s.descriptor) : Option Loc :=
  (s.globalAddress slot).map fun address => ⟨.global, 0, address⟩

/-- The recorded effects of one tensor store or reduction: the shared read, the global write and
(for a reduction) the old global byte read of each slot, and whether read completion and full
completion have occurred. -/
structure Effects (s : Spec) where
  read : TensorTransfer.Slot s.descriptor → Option Byte := fun _ => none
  write : TensorTransfer.Slot s.descriptor → Option Byte := fun _ => none
  readsDone : Bool := false
  fullDone : Bool := false
  /-- A reduction's read of the old destination byte it reduces. -/
  old : TensorTransfer.Slot s.descriptor → Option Byte := fun _ => none

/-- The effects obey the rules of a tensor store: written slots lie in bounds and were read, a store
writes the byte it read, read completion implies every in-bounds slot was read, full completion
implies all writes, and a reduction writes all bytes of an element together with their old bytes. -/
structure CopyOk (s : Spec) (e : Effects s) : Prop where
  writes : ∀ slot byte, e.write slot = some byte →
    (∃ loc, destination s slot = some loc) ∧
      ∃ source, e.read slot = some source ∧ (s.reduce = none → byte = source)
  readsComplete : e.readsDone = true → ∀ slot loc, destination s slot = some loc →
    ∃ byte, e.read slot = some byte
  complete : e.fullDone = true → e.readsDone = true ∧
    ∀ slot loc, destination s slot = some loc → ∃ byte, e.write slot = some byte
  /-- A reduction writes all bytes of an element together, each with its old byte. -/
  element : ∀ slot byte, e.write slot = some byte → s.reduce.isSome →
    ∀ other : TensorTransfer.Slot s.descriptor, other.1 = slot.1 → other.2.1 = slot.2.1 →
      (∃ b, e.write other = some b) ∧ ∃ b, e.old other = some b
  /-- Only a reduction reads old destination bytes, and only with the element's write. -/
  old : ∀ slot byte, e.old slot = some byte → s.reduce.isSome ∧ ∃ w, e.write slot = some w

/-- The effects `b` extend the effects `a` of the same store: nothing recorded in `a` is lost. -/
def Extends {s : Spec} (a b : Effects s) : Prop :=
  (∀ slot byte, a.read slot = some byte → b.read slot = some byte) ∧
  (∀ slot byte, a.write slot = some byte → b.write slot = some byte) ∧
  (a.readsDone = true → b.readsDone = true) ∧
  (a.fullDone = true → b.fullDone = true) ∧
  (a.readsDone = true → b.read = a.read) ∧
  (∀ slot byte, a.old slot = some byte → b.old slot = some byte)

/-- The frozen specification of one actual tensor store with its effects so far. -/
structure Observation where
  spec : Spec
  effects : Effects spec

/-- The observation `b` extends `a`: the same specification, with extended effects. -/
def Observation.Extends (a b : Observation) : Prop :=
  ∃ h : a.spec = b.spec, TensorStore.Extends (h ▸ a.effects) b.effects

/-- Every observation of `a` is also in `b` as an extended observation of the same issue. -/
def SnapshotExtends {ι : Type} (a b : ι → Option Observation) : Prop :=
  ∀ i old, a i = some old → ∃ newer, b i = some newer ∧ old.Extends newer

/-- Actual completion flags supply the group wait predicates; commit never sets them. -/
def completion {ι : Type} (snapshots : ι → Option Observation) : BulkGroup.Completion ι :=
  ⟨fun i => ∃ o, snapshots i = some o ∧ o.effects.readsDone = true,
   fun i => ∃ o, snapshots i = some o ∧ o.effects.fullDone = true⟩

/-! ## CORRECT-TENSOR-STORE-SIZE — count output-copy effects and completion stages
Statement: The effects of a tensor store are counted as one for each recorded read and write, one
  for read completion and one for full completion. The count only measures progress and adds no
  permitted or forbidden behavior.

Defs: TensorStore.Effects.readSlots, TensorStore.Effects.writeSlots, TensorStore.Effects.size

Source:
- none (finite progress measure)

Direction: representation

Applies: One output tensor operation's effects

Premises: Its descriptor determines a finite set of byte slots.

Effect: A progress measure only.
-/
def Effects.readSlots {s : Spec} (e : Effects s) : Finset (TensorTransfer.Slot s.descriptor) :=
  Finset.univ.filter fun slot => (e.read slot).isSome

def Effects.writeSlots {s : Spec} (e : Effects s) : Finset (TensorTransfer.Slot s.descriptor) :=
  Finset.univ.filter fun slot => (e.write slot).isSome

def Effects.size {s : Spec} (e : Effects s) : Nat :=
  e.readSlots.card + e.writeSlots.card + (if e.readsDone then 1 else 0) +
    (if e.fullDone then 1 else 0)

end
end PTX.TensorStore

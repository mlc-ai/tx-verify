-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tma

@[expose] public section

namespace PTX
noncomputable section

/-! ## THREAD-TENSOR-ISSUE — issuing a tensor load
Statement: A tensor load produces one issue event that records the descriptor, the signed 32-bit
  origin, the shared destination and the mbarrier, and it produces no data write and no
  completion. A multicast load issues one copy to each destination CTA of its mask in rank order,
  each with its own destination and mbarrier at the same offsets. The optional cache policy must
  be a defined value and does not change any event. An operand that fails the alignment, map,
  mask or routing checks, or whose box start is not 16-byte aligned (`requireBoxAligned`,
  DEP-TENSOR-LOAD-EFFECTS), produces an undefined-behaviour event.

Defs: tensorMulticast, tensorLoadCopy, tensorLoadCopy_boxAligned, cachePolicyRead, tensorTmpl

Source:
- §9.7.10.28.5.3 (cache hint): "When the optional argument cache_policy is specified, the qualifier
    .level::cache_hint is required. The 64-bit operand cache_policy specifies the cache eviction
    policy that may be used during the memory access. cache_policy is a hint to the cache subsystem
    and may not always be respected. It is treated as a performance hint only, and does not change
    the memory consistency behavior of the program."
- §5.5.3.4
- CUDA Driver API cuTensorMapEncodeTiled
- EXT-TMA-GEOMETRY (64-byte map and 128-byte shared alignment)

Direction: scope

Applies: 1D–5D tiled and 2D `.tile::gather4` global-to-shared loads, including
  `.multicast::cluster` and `.L2::cache_hint`, using immutable host-published tensor maps

Premises: The cache policy, when present, is a defined 64-bit value (`cachePolicyRead`, as for
  stores and prefetches). The box start is 16-byte aligned (`requireBoxAligned`). Map address is
  64-byte aligned and resolves in Launch.tensorMaps to a descriptor of the
  instruction's rank (gather4: a 2D map whose box dimension 1 is one, EXT-TMA-GATHER4). Descriptor
  properties, shared alignment and CTA-group routing pass their checks; a multicast load's own
  `dstMem` and `mbar` operands pass the same routing check as a non-multicast load's, so `mbar` is
  in the CTA group of `dstMem` (§9.7.10.28.5.3: "When .cta_group::1 is specified, the mbarrier
  object mbar that is specified must be in the shared memory of the same CTA as the shared memory
  destination dstMem"; with `.cta_group::2`, "either the same CTA as the shared memory destination
  dstMem or in its peer-CTA") before the copies are fanned out.

Effect: Thread event construction. Dynamic descriptor mutation/publication is not modeled by the
  launch map. A gather4 load records the map's descriptor with four rows (`Descriptor.fourRows`),
  the origin `(x, y0)` and the four row coordinates. A multicast load names at most the cluster's
  ranks in `ctaMask` and issues its copies through sub-steps, and with `.cta_group::2` it signals
  the pair CTA with the parity of the CTA of `mbar` (§9.7.10.28.5.3). Each copy reads the source
  itself, which over-approximates the single read of the hardware by allowing a separate read per
  destination. Launch.tensorMaps is launch data justified by host descriptor creation and
  publication (EXT-LAUNCH); it is not an arbitrary predicate guaranteeing the copy's result.
-/
/-- Sub-step `t.sub` of a `.multicast::cluster` load whose CTA-relative copy is `s`: the copy to
the `t.sub`-th destination CTA of the ctaMask (`width` bits) in rank order, with its data and
its mbarrier signal at the same CTA-relative offsets (cta_group::2: the mbarrier of the pair CTA
with the parity of `s.mbar`'s CTA), then the next destination or the next instruction. -/
def tensorMulticast (L : Launch) (g : Nat) (t : TState) (mapAddress : Nat) (s : TensorCopy.Spec)
    (width : Nat) (mask : Opnd) : Exec Tmpl := do
  let m ← readBits L g t width mask
  let n := L.clusterSizeOf (g / L.block)
  unless m.toNat < 2 ^ n do throw .badValue
  let targets := (List.range n).filter fun r => m.toNat.testBit r
  let some r := targets[t.sub]? | throw .badValue
  let some peer := L.peerCta (g / L.block) r | throw .badValue
  let mbarRank := r / s.group.size * s.group.size + L.rankOfCta s.mbar.cta % s.group.size
  let some mbarPeer := L.peerCta (g / L.block) mbarRank | throw .badValue
  let copy := { s with sharedBase := { s.sharedBase with cta := peer },
                       mbar := { s.mbar with cta := mbarPeer } }
  unless TensorRoute L (g / L.block) true s.group copy.sharedBase copy.mbar do throw .badValue
  pure (.tensorIssue mapAddress copy
    (if t.sub + 1 < targets.length then { t with sub := t.sub + 1 } else { next t with sub := 0 }))

/-- The CTA-relative copy of a tensor load and its map address: the actual descriptor (gather4:
with four rows), signed 32-bit origin and row coordinates, shared destination and mbarrier. -/
def tensorLoadCopy (L : Launch) (g : Nat) (t : TState) (cluster groupTwo : Bool) (dst : Nat)
    (off : Int) (map : Opnd) (cs : List Opnd) (mb : Nat) (moff : Int) (mode : TensorMode) :
    Exec (Nat × TensorCopy.Spec) := do
  let (mapAddress, ⟨outer, descriptor⟩) ← tensorMap L g t map cs mode
  let dst ← sharedEffAddr L g t cluster dst off
  unless dst.addr % 128 = 0 do throw .misaligned
  let mbar ← if cluster then mbarClusterLoc L g t mb moff else mbarLoc L g t mb moff
  let vs ← cs.mapM (readBits L g t 32)
  let origin := fun axis : Fin (outer + 1) => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt
  let group := if groupTwo then CtaGroup.two else CtaGroup.one
  let ys := fun j : Fin 4 => (BitVec.ofNat 32 (vs.getD (j.val + 1) 0).toNat).toInt
  requireBoxAligned (mode.transfer descriptor) origin
  pure (mapAddress,
    ⟨⟨outer, mode.transfer descriptor, origin, dst, mode.rowCoordinates ys⟩, mbar, cluster, group⟩)

/-- Per-form lemma: the copy of a tensor load that the thread rule returns has an aligned box. The
statement `BoxAligned s.descriptor s.origin` for every `TensorIssue` is the form of the former
fourth disjunct of `TensorUnsafe`. -/
theorem tensorLoadCopy_boxAligned (L : Launch) (g : Nat) (t : TState) (cluster groupTwo : Bool)
    (dst : Nat) (off : Int) (map : Opnd) (cs : List Opnd) (mb : Nat) (moff : Int)
    (mode : TensorMode) {mapAddress : Nat} {s : TensorCopy.Spec}
    (h : tensorLoadCopy L g t cluster groupTwo dst off map cs mb moff mode = .ok (mapAddress, s)) :
    TensorDescriptor.BoxAligned s.descriptor s.origin := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       have hr := ‹requireBoxAligned _ _ = Except.ok _›
       exact (requireBoxAligned_eq_ok _ _).1 (by simpa using hr))

/-- The optional `.L2::cache_hint` operand: a defined 64-bit value, otherwise unused. -/
def cachePolicyRead (L : Launch) (g : Nat) (t : TState) : Option Opnd → Exec Unit
  | some p => do let _ ← readBits L g t 64 p; pure ()
  | none => pure ()

/-- The event of a tensor load: one issue, or for a multicast load one issue per destination CTA. -/
def tensorTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .cpTensor cluster groupTwo dst off map cs mb moff mc mode policy => ofExec do
    cachePolicyRead L g t policy
    let (mapAddress, s) ← tensorLoadCopy L g t cluster groupTwo dst off map cs mb moff mode
    match mc with
    | none =>
      unless TensorRoute L (g / L.block) s.clusterAddress s.group s.sharedBase s.mbar do
        throw .badValue
      pure (.tensorIssue mapAddress s (next t))
    | some (width, mk) =>
      unless s.clusterAddress ∧ TensorRoute L (g / L.block) true s.group s.sharedBase s.mbar do
        throw .badValue
      tensorMulticast L g t mapAddress s width mk
  | _ => .ub .noRule

/-! ## THREAD-TENSOR-PREFETCH — issuing a tensor-data or linear prefetch
Statement: A tensor prefetch produces one event that records the map and the elements it selects,
  and a linear prefetch one event that records its global range; the thread continues with its
  registers unchanged. The event is a pending weak read, through the async proxy, of each in-bounds
  selected global byte or of the range (EXT-PREFETCH-PENDING). A box start that is not 16-byte
  aligned, and a linear range whose address is not 16-byte aligned or whose size is not a multiple
  of 16, produce an undefined-behaviour event.

Defs: tensorPrefetchTmpl

Source:
- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is a non-blocking instruction which may initiate an
    asynchronous prefetch of tensor data from the location in .src statespace to the L2 cache."
- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.10.28.5.5 (`.tile` or `.tile::gather4`)
- §8.6: "Operations using methods of access distinct from the generic method include: … async-proxy
    and tensormap-proxy accesses by .async.bulk operations"
- §9.7.10.28.1: "This section describes two asynchronous copy operation completion mechanisms
    supported in PTX: Async-group mechanism and mbarrier-based mechanism."
- EXT-PREFETCH-PENDING (always initiated, never complete)
- §5.5.3.1: "The address of the bounding Box must also be aligned to 16 bytes."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is a non-blocking instruction which may initiate an
    asynchronous prefetch of data from the location specified by source address operand srcMem , in
    .src statespace, to the L2 cache."
- §9.7.10.28.4.3: "size must be a multiple of 16. If the value is not a multiple of 16, then the
    behavior is undefined. The address srcMem must be aligned to 16 bytes."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.10.28.4.3: "Qualifier .level::eviction_priority specifies the eviction priority to be applied
    for the prefetched cache line."
- §5.5.3.3: "If a TMA operation performs an out-of-boundary access and the tensor-map object’s
    allocation class (see tensormap.replace ) is large, but the memory range [global_addr,
    global_addr + CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE) is not accessible, the
    behavior is undefined."

Direction: stricter

Applies: cp.async.bulk.prefetch.tensor.{1..5}d.L2.global{.tile, .tile::gather4}{.L2::cache_hint,
  .L2::evict_last} with an immutable host-published map; cp.async.bulk.prefetch.L2.global
  {.L2::cache_hint, .L2::evict_last}

Premises: The map passes the checks of a tensor load of the same mode (64-byte alignment, a
  published valid descriptor of the instruction's rank, gather4's 2D map with box dimension 1 one),
  the coordinates and cache policy are defined 32- and 64-bit values, and the box start is 16-byte
  aligned (`BoxAligned`). A linear prefetch's address is 16-byte aligned and its size a multiple of
  16.

Effect: Thread event construction. The read is the pending read of EXT-PREFETCH-PENDING: it is never
  present and never completes, returns no value (so no read-from or value constraint applies), and
  is checked against overlapping writes (ERR-DATA-RACE, ERR-MIXED-SIZE; a write is exempt only if
  `modelCausality` orders it before the read, MEM-MODEL-CAUSALITY, and a generic-proxy write
  of a global byte never is, since that rule has no global proxy fence) and for allocation
  (ERR-UNALLOCATED-ACCESS). The event has no mbarrier or bulk-group action and no completion to wait
  for. The eviction priority `.L2::evict_last` is a cache hint without effect. im2col modes,
  overrides and device-updated descriptors are outside this rule. The tensor-map read through the
  tensormap proxy is not represented: maps are immutable launch data. The event records the elements
  as a tensor load of the same mode records them: the transfer descriptor (for gather4 the map's
  descriptor with four rows), the signed 32-bit origin and the row coordinates. The read has the
  footprint of a tensor load's source read of the same selection (`.read (.prefetch ..)`,
  MEM-FOOTPRINT). Whether a large-class map with an out-of-bounds element has its backing range
  is decided on the execution (ERR-TENSOR-LARGE-OOB), where launch memory is visible.

### EXT-PREFETCH-PENDING — a prefetch is an initiated read that stays pending

Statement: The model treats every tensor or linear prefetch as an initiated read, through the
  async proxy, of the selected in-bounds global bytes or of the range. The read returns no value
  and never completes.

Source:
- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is a non-blocking instruction which may initiate an
    asynchronous prefetch of tensor data from the location in .src statespace to the L2 cache."
- §9.7.10.28.5.5: "cp.async.bulk.prefetch.tensor is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is a non-blocking instruction which may initiate an
    asynchronous prefetch of data from the location specified by source address operand srcMem , in
    .src statespace, to the L2 cache."
- §9.7.10.28.4.3: "cp.async.bulk.prefetch is treated as a weak memory operation in the Memory
    Consistency Model ."
- §8.6: "Operations using methods of access distinct from the generic method include: … async-proxy
    and tensormap-proxy accesses by .async.bulk operations"

Why it is not spec text: The text says the instruction "may initiate" a prefetch; it does not say
  whether the access happens or when it ends, and it gives the access no completion mechanism.
  The model's choice is that the access is always initiated and never complete.

Direction: stricter

Effect: This is a conservative abstraction for safety checking. It does not claim that the hardware
  access never ends. It makes every write that may overlap the access unordered be reported
  (ERR-DATA-RACE, ERR-MIXED-SIZE) and requires the in-bounds bytes to be allocated
  (ERR-UNALLOCATED-ACCESS). It may reject a program whose prefetch the hardware drops or has already
  completed. It adds no Lean axiom and no Assumption, and `Complete` does not require the read to
  complete. Disclosed by every kernel whose statement names `Op.prefetchTensor` or
  `Op.prefetchBulk`: none.
-/
/-- The event of a tensor-data prefetch (its map address and selected elements) or of a linear
prefetch (its global range). -/
def tensorPrefetchTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .prefetchTensor map cs mode policy => ofExec do
    let (mapAddress, ⟨outer, descriptor⟩) ← tensorMap L g t map cs mode
    let vs ← cs.mapM (readBits L g t 32)
    cachePolicyRead L g t policy
    let origin := fun axis : Fin (outer + 1) => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt
    let ys := fun j : Fin 4 => (BitVec.ofNat 32 (vs.getD (j.val + 1) 0).toNat).toInt
    requireBoxAligned (mode.transfer descriptor) origin
    pure (.tensorPrefetch mapAddress
      ⟨outer, mode.transfer descriptor, origin, mode.rowCoordinates ys⟩ (next t))
  | .prefetchBulk sb soff n policy => ofExec do
    let s ← effAddr L g t .global sb soff
    let size ← readBits L g t 32 n
    bulkPolicy L g t policy
    unless size.toNat % 16 = 0 ∧ s.addr % 16 = 0 do throw .misaligned
    pure (.bulkPrefetch { loc := s, size := size.toNat } (next t))
  | _ => .ub .noRule

/-! ## THREAD-TENSOR-STORE — output tensor issue and bulk-group instructions
Statement: A tensor store, a tensor reduction, `cp.async.bulk.commit_group` and
  `cp.async.bulk.wait_group` each produce one event. A store or reduction records the descriptor,
  the nonnegative signed origin and the shared source in the issuing CTA, and a reduction also
  records its operation, which must support the map's element type. An operand that fails the
  alignment, sign or operation checks, or whose box start is not 16-byte aligned
  (`requireBoxAligned`, DEP-TENSOR-LOAD-EFFECTS), produces an undefined-behaviour event.

Defs: tensorStoreSpec, tensorStoreSpec_boxAligned, tensorStoreTmpl

Source:
- §9.7.10.28.5.3
- §9.7.10.28.6.1–2
- CUDA Programming Guide §4.13.4 (output coordinates)
- EXT-TMA-GEOMETRY (64-byte map and 128-byte shared alignment)

Direction: scope

Applies: Non-interleaved 1D–5D tiled and 2D `.tile::scatter4` shared::cta-to-global stores, 1D–5D
  tiled `cp.reduce.async.bulk.tensor` reductions, commit_group and wait_group

Premises: Host-published map (scatter4: 2D with box dimension 1 one, EXT-TMA-SCATTER4), descriptor
  validity, local shared source, 128-byte alignment and nonnegative signed coordinates (scatter4:
  all five). Optional cache-policy operand is a defined 64-bit value. The box start is 16-byte
  aligned (`requireBoxAligned`).

Effect: Thread event construction only; operation effects, grouping, blocking and visibility are
  checked separately. A scatter4 store records the map's descriptor with four rows, the origin
  `(x, y0)` and the row coordinates. A reduction is a tile-mode operation, and its event records
  its operation. The read, full and async-only modes of `cp.async.bulk.wait_group` are recorded as
  distinct modes.
-/
/-- The specification of a tensor store and its map address: the actual descriptor (scatter4:
with four rows), nonnegative signed origin and row coordinates, and local shared source. -/
def tensorStoreSpec (L : Launch) (g : Nat) (t : TState) (map : Opnd) (cs : List Opnd)
    (src : Nat) (off : Int) (policy : Option Opnd) (mode : TensorMode)
    (reduce : Option AtomOp) : Exec (Nat × TensorStore.Spec) := do
  let (mapAddress, ⟨outer, descriptor⟩) ← tensorMap L g t map cs mode
  unless reduce.all (fun op => decide (mode = .tile) &&
      TensorStore.ReduceSupported op descriptor.format) do
    throw .badValue
  let src ← sharedEffAddr L g t false src off
  unless src.addr % 128 = 0 do throw .misaligned
  let vs ← cs.mapM (readBits L g t 32)
  let origin := fun axis : Fin (outer + 1) => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt
  unless ∀ axis, 0 ≤ origin axis do throw .badValue
  cachePolicyRead L g t policy
  let ys := fun j : Fin 4 => (BitVec.ofNat 32 (vs.getD (j.val + 1) 0).toNat).toInt
  unless mode = .tile ∨ ∀ j, 0 ≤ ys j do throw .badValue
  requireBoxAligned (mode.transfer descriptor) origin
  pure (mapAddress,
    ⟨⟨outer, mode.transfer descriptor, origin, src, mode.rowCoordinates ys⟩, reduce⟩)

/-- Per-form lemma: the specification of a tensor store or reduction that the thread rule returns
has an aligned box. The statement `BoxAligned s.descriptor s.origin` for every `TensorStoreIssue` is
the form of the former first disjunct of `TensorStoreUnsafe`. -/
theorem tensorStoreSpec_boxAligned (L : Launch) (g : Nat) (t : TState) (map : Opnd)
    (cs : List Opnd) (src : Nat) (off : Int) (policy : Option Opnd) (mode : TensorMode)
    (reduce : Option AtomOp) {mapAddress : Nat} {s : TensorStore.Spec}
    (h : tensorStoreSpec L g t map cs src off policy mode reduce = .ok (mapAddress, s)) :
    TensorDescriptor.BoxAligned s.descriptor s.origin := by
  unfold tensorStoreSpec at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       have hr := ‹requireBoxAligned _ _ = Except.ok _›
       exact (requireBoxAligned_eq_ok _ _).1 (by simpa using hr))

/-- The event of a tensor store, a tensor reduction, `cp.async.bulk.commit_group` or
`cp.async.bulk.wait_group`. -/
def tensorStoreTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .cpTensorStore map cs src off policy mode reduce => ofExec do
    let (mapAddress, s) ← tensorStoreSpec L g t map cs src off policy mode reduce
    pure (.tensorStore mapAddress s (next t))
  | .bulkCommit => .bulkCommit (next t)
  | .bulkWait mode n => .bulkWait mode n (next t)
  | _ => .ub .noRule

end
end PTX

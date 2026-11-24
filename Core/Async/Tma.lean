-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access
public import Core.MBarrier.AsyncMBarrier
public import Core.MBarrier.MBarrierObject

@[expose] public section

/-!
# Thread semantics: mbarrier and bulk-copy instructions

The events these instructions perform. When a phase completes, what a `try_wait` returns,
and how a bulk copy is ordered are decided by the execution rules (DEP-ASYNC-ORIGIN).
-/

namespace PTX

noncomputable section

/-! ## THREAD-TMA — mbarrier and bulk-copy instructions
Statement: Each mbarrier instruction of a thread produces one event: `mbarrier.init`,
  `mbarrier.inval`, `mbarrier.arrive` with or without `expect_tx`, and `mbarrier.try_wait.parity`
  each produce one event, and a `cp.async.bulk` copy or `cp.reduce.async.bulk` reduction produces
  only its issue event, one for each destination CTA of a multicast copy. A `.cp_mask` copy writes
  only the bytes its mask selects, and a reduction writes each element with an atomic
  read-modify-write at the scope of its `.sem.scope`. A misaligned address, an arrival count
  outside [1, 2^20), an invalid bulk-copy size, a source or destination range that overflows its
  memory space, or a destination or mbarrier in a CTA the direction does not allow produces an
  undefined-behaviour event instead.

Defs: ofExec, mbarLoc, mbarClusterLoc, genericSharedLoc, mbarStateDest, bulkSizeOk, bulkSpaceEnd,
  bulkRangeOk, bulkPolicy, bulkIgnoreOob, bulkSpec, bulkMulticast, bulkReduceOk, bulkWrites,
  bulkCopyTmpl, tmaTmpl, tmaTmpl_cpBulk_cta

Source:
- §9.7.15.16.12 (mbarrier.init)
- §9.7.15.16.13 (mbarrier.inval): "mbarrier.inval invalidates the mbarrier object at the location
    specified by the address operand addr"
- §9.7.15.16.14–16 (mbarrier.arrive.expect_tx): "mbarrier.arrive operation on an mbarrier object
    located in .shared::cta returns an opaque 64-bit register capturing the phase of the mbarrier
    object prior to the arrive-on operation in the destination operand state. Contents of the state
    operand are implementation specific."
- §5.1.7: "If no sub-qualifier is specified with the .shared state space, then it defaults to ::cta
    ."
- §9.7.15.16.19 (mbarrier.try_wait)
- §9.7.10.28.4.1 (cp.async.bulk): "size must be a multiple of 16. If the value is not a multiple of
    16, then the behavior is undefined."
- §9.7.10.28.4.1 (cp.async.bulk): "The memory range [dstMem, dstMem + size - 1] must not overflow
    the destination memory space and the memory range [srcMem, srcMem + size - 1] must not overflow
    the source memory space. Otherwise, the behavior is undefined."
- §9.7.10.28.4.1 (cp.async.bulk): "The addresses dstMem and srcMem must be aligned to 16 bytes."
- §9.7.10.28.4.1 (cp.async.bulk): "When the destination of the copy is .shared::cta the destination
    address has to be in the shared memory of the executing CTA within the cluster, otherwise the
    behavior is undefined."
- §9.7.10.28.4.1 (cp.async.bulk): "When the source of the copy is .shared::cta and the destination
    is .shared::cluster , the destination has to be in the shared memory of a different CTA within
    the cluster."
- §9.7.10.28.4.1 (cp.async.bulk): "The source data is multicast to the same CTA-relative offset as
    dstMem in the shared memory of each destination CTA. The mbarrier signal is also multicast to
    the same CTA-relative offset as mbar in the shared memory of the destination CTA."
- §9.7.10.28.4.1 (cp.async.bulk): "The only valid values for ignoreBytesLeft and ignoreBytesRight
    are [0..15] , and any other value may result in undefined behavior."
- §9.7.10.28.4.1 (cp.async.bulk): "When .sem is .relaxed , the data copy accesses memory with
    naturally-aligned strong memory operations with element-wise atomic size specified by .type and
    thread scope specified by .scope ."
- §9.7.10.28.4.1 (cp.async.bulk): "It is treated as a performance hint only, and does not change the
    memory consistency behavior of the program."
- §9.7.10.28.4.1 (cp.async.bulk): "When the optional qualifier .cp_mask is specified, the argument
    byteMask is required."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The size of the source and the destination array must be
    the same and is specified by the operand size ."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "size must be a multiple of 16. If the value is not a
    multiple of 16, then the behavior is undefined."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The memory range [dstMem, dstMem + size - 1] must not
    overflow the destination memory space and the memory range [srcMem, srcMem + size - 1] must not
    overflow the source memory space. Otherwise, the behavior is undefined."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The addresses dstMem and srcMem must be aligned to 16
    bytes."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "When .sem.scope is not specified, it defaults to
    .relaxed.sys ."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "Source location accesses are .weak , that is, not atomic."
- §9.7.10.28.4.2 (cp.reduce.async.bulk): "The cp.reduce.async.bulk.add.f16 and
    cp.reduce.async.bulk.add.bf16 operations require .noftz qualifier."
- §9.7.15.4 (mbarrier-init fence)

Direction: stricter

Applies: Mbarrier instructions and `cp.async.bulk` in every direction of the instruction table
  (`.shared::cta.global` with an optional `.ignore_oob`, `.shared::cluster.global` with an optional
  `.multicast::cluster{::16b, ::32b}`, `.shared::cluster.shared::cta`,
  `.global.shared::cta.bulk_group` with an optional `.cp_mask`), `.weak` or `.relaxed`, with an
  optional `.L2::cache_hint`; `cp.reduce.async.bulk` in both directions with every operation and
  type of the table

Premises: Addresses, alignment, sizes, counts and CTAs pass the checks below.

Effect: Event production and local faults. An mbarrier object is an 8-byte aligned shared location;
  its arrival count must lie in `[1, 2^20)` and an unsigned 32-bit transaction operand (the object
  checks the resulting signed counter). `mbarrier.init`, `mbarrier.inval` and
  `mbarrier.arrive.expect_tx` are one event each; `fence.mbarrier_init` is an event. A bulk copy
  needs a positive size that is a multiple of 16 and 16-byte aligned addresses (`bulkSizeOk`), and
  its source and destination ranges must not overflow their memory spaces (`bulkRangeOk`), whatever
  its `.cp_mask` selects: a global range ends at most at `2^64` and a shared range at most at
  `2^32`, the address ranges of the model's locations (EXT-ADDR-WRAP). A range that stays below
  these bounds but reaches past the bytes of its space allocated at launch is rejected by the
  allocation checks: the footprint of the source and of an unmasked destination by
  ERR-UNALLOCATED-ACCESS, and the whole destination range of a `.cp_mask` copy by
  ERR-BULK-MASK-RANGE. Only its issue is in the thread trace (`Kind.copy`). Its read, write and
  notification are separate asynchronous effects (DEP-LINEAR-COPY-EFFECTS). The source and
  destination of a copy have the copy's size; the completion is the complete-tx on the instruction's
  mbarrier, or the issuing thread's bulk async-group for `.bulk_group`. The CTAs a copy may name: a
  `.shared::cta` destination and its mbarrier are in the executing CTA. A `.shared::cluster`
  destination of a copy from global memory and its mbarrier are in one CTA of the cluster, which may
  be the executing one; the text does not say where the mbarrier of a non-multicast copy may lie,
  and requiring the destination's CTA is stricter. A copy from `.shared::cta` to `.shared::cluster`
  reads the executing CTA's shared memory and writes another CTA's ("has to be in the shared memory
  of a different CTA"), with the mbarrier in that CTA (stricter, as above). A multicast copy issues
  one copy per destination CTA of its mask, in rank order through sub-steps, each to the
  CTA-relative offsets of `dstMem` and `mbar` in that CTA; each copy reads the source itself, which
  over-approximates the single read of the hardware, as for tensor multicast (THREAD-TENSOR-ISSUE).
  A mask with a rank outside the cluster, or with no rank, is undefined (stricter for the empty
  mask). `.ignore_oob` with both `ignoreBytesLeft` and `ignoreBytesRight` zero is the plain copy.
  Any other value leaves destination bytes indeterminate, which the linear copy effect does not
  represent, so it is an undefined-behaviour event (stricter). `.relaxed` copies are treated as
  weak: their accesses are weak async-proxy accesses (stricter: a race with them is reported
  although strong accesses of including scopes would not race). The `.L2::cache_hint` operand must
  be a defined 64-bit value and has no other effect. `try_wait.parity` is one event whose result is
  open; the thread sets its predicate from it. `mbarrier.arrive` on a `.shared` (that is
  `.shared::cta`) object with a destination register instead of the sink `_` is the same arrival
  event; the register's prior value is discarded and it holds no value afterwards (`mbarStateDest`),
  so a later read of it is an `uninitialized` fault. The text gives the state no meaning a thread
  can use ("Contents of the state operand are implementation specific."), so any use of it is
  rejected (stricter). A `.cp_mask` copy (only from `.shared::cta` to global memory, as the syntax
  states) writes byte `k` of its destination when bit `k % 16` of the 16-bit `byteMask` is set, with
  its source byte, and leaves the other bytes unwritten (`WriteMode.masked`,
  DEP-LINEAR-COPY-EFFECTS). A `cp.reduce.async.bulk` reads its `.shared::cta` source with weak
  accesses and reduces each element of its type into the destination with one atomic
  read-modify-write (`WriteMode.reduce`), strong at the scope of its `.sem.scope`, `.sys` when
  absent, in the async proxy (ERR-DATA-RACE, MEM-ATOMICITY, DEP-REDUCTION-VALUES); the operation and
  type must be a combination of the table for its destination (`bulkReduceOk`). The bit operations
  `.and`, `.or` and `.xor` also accept `.u` and `.s` types of the listed widths, as the
  instruction's own example `xor.s32` does. The `.noftz` qualifier is not recorded: the floating
  values come from an assumption. Its directions and checks are those of the copy with the same
  state spaces. Anything else in these instructions is undefined.
-/

/-- A rule's result as a template: its undefined behaviour becomes a `ub` event. -/
def ofExec : Exec Tmpl → Tmpl
  | .ok m => m
  | .error f => .ub f

/-- The mbarrier object at `[base + offset]`. -/
def mbarLoc (L : Launch) (g : Nat) (t : TState) (base : Nat) (off : Int) : Exec Loc := do
  let m ← effAddr L g t .shared base off
  if m.addr % 8 = 0 then pure m else throw .misaligned

/-- Shared::cluster permits a peer object, but does not enlarge memory synchronization scope. -/
def mbarClusterLoc (L : Launch) (g : Nat) (t : TState) (base : Nat) (off : Int) : Exec Loc := do
  let m ← sharedEffAddr L g t true base off
  if m.addr % 8 = 0 then pure m else throw .misaligned

/-- The shared location at the generic address `[base + offset]`: a generic shared pointer of the
thread's CTA (`cluster` false) or of a CTA of its cluster (`cluster` true), resolved in the shared
window and required to stay in it. Any other generic address has no rule. -/
def genericSharedLoc (L : Launch) (g : Nat) (t : TState) (cluster : Bool) (base : Nat)
    (off : Int) : Exec Loc := do
  let loc ← readSharedAddress L g t 64 true cluster (.reg base)
  let x := (loc.addr : Int) + off
  unless 0 ≤ x ∧ x < 2 ^ 32 do throw .noRule
  pure ⟨.shared, loc.cta, x.toNat⟩

/-- The destination register of `mbarrier.arrive`'s opaque state, if any, holds no value
afterwards. -/
def mbarStateDest (t : TState) : Option Nat → TState
  | none => t
  | some d => { t with regs := Function.update t.regs d none }

/-- A bulk copy of `size` bytes between `d` and `s` is well formed: a positive multiple of 16 bytes
between 16-byte aligned addresses. -/
def bulkSizeOk (size : Nat) (d s : Loc) : Prop :=
  0 < size ∧ size % 16 = 0 ∧ d.addr % 16 = 0 ∧ s.addr % 16 = 0

instance (size : Nat) (d s : Loc) : Decidable (bulkSizeOk size d s) := by
  unfold bulkSizeOk; infer_instance

/-- The end of the address range of a location space: `2^64` for global memory and `2^32` for the
shared window and the other spaces (EXT-ADDR-WRAP). -/
def bulkSpaceEnd : Space → Nat
  | .global => 2 ^ 64
  | _ => 2 ^ 32

/-- The ranges `[d, d + size - 1]` and `[s, s + size - 1]` of a bulk copy or reduction do not
overflow their memory spaces (§9.7.10.28.4.1, §9.7.10.28.4.2), whatever bytes the copy writes. -/
def bulkRangeOk (size : Nat) (d s : Loc) : Prop :=
  d.addr + size ≤ bulkSpaceEnd d.space ∧ s.addr + size ≤ bulkSpaceEnd s.space

instance (size : Nat) (d s : Loc) : Decidable (bulkRangeOk size d s) := by
  unfold bulkRangeOk; infer_instance

/-- The optional `.L2::cache_hint` operand: a policy of `createpolicy` (THREAD-CACHE-POLICY) or
a defined 64-bit value, otherwise unused. -/
def bulkPolicy (L : Launch) (g : Nat) (t : TState) : Option Opnd → Exec Unit
  | some p => do
    match ← readValue L g t 64 p with
    | .policy => pure ()
    | _ => do let _ ← readBits L g t 64 p; pure ()
  | none => pure ()

/-- The optional `ignoreBytesLeft` and `ignoreBytesRight` operands of `.ignore_oob`: both must be
zero, which is the plain copy; any other value is undefined here (stricter). -/
def bulkIgnoreOob (L : Launch) (g : Nat) (t : TState) : Option (Opnd × Opnd) → Exec Unit
  | some (l, r) => do
    let lv ← readBits L g t 32 l
    let rv ← readBits L g t 32 r
    unless lv.toNat = 0 ∧ rv.toNat = 0 do throw .badValue
  | none => pure ()

/-- The linear operation of a bulk copy or reduction from `s` to `d` with completion `c`, write
mode `mode` and strong scope `sc`, in the async proxy. -/
def bulkSpec (s d : Acc) (c : AsyncCopy.Completion) (mode : AsyncCopy.WriteMode)
    (sc : Option MbarScope) : AsyncCopy.Spec :=
  { src := s, dst := d, completion := c, writes := mode, scope := sc }

/-- Sub-step `t.sub` of a `.multicast::cluster` copy of `size` bytes from global `s` whose
destination and mbarrier have the CTA-relative offsets of `d` and `m`: the copy to the `t.sub`-th
destination CTA of the `width`-bit mask in rank order, then the next destination or the next
instruction. -/
def bulkMulticast (L : Launch) (g : Nat) (t : TState) (s d m : Loc) (size width : Nat)
    (mask : Opnd) : Exec Tmpl := do
  let k ← readBits L g t width mask
  let n := L.clusterSizeOf (g / L.block)
  unless k.toNat < 2 ^ n do throw .badValue
  let targets := (List.range n).filter fun r => k.toNat.testBit r
  let some r := targets[t.sub]? | throw .badValue
  let some peer := L.peerCta (g / L.block) r | throw .badValue
  pure (.copy (bulkSpec { loc := s, size := size } { loc := { d with cta := peer }, size := size }
      (.mbarrier { m with cta := peer }) .whole none)
    (if t.sub + 1 < targets.length then { t with sub := t.sub + 1 } else { next t with sub := 0 }))

/-- The element types of a linear reduction (§9.7.10.28.4.2, the table of `.redOp` and element type
for each destination): `cluster` for a `.shared::cluster` destination. The bit operations also
accept the `.u` and `.s` integer types of the listed widths, whose bits they operate on alike. -/
def bulkReduceOk (cluster : Bool) : AtomOp → DType → Bool
  | .add, .int k w => if cluster then (k, w) ∈ [(.u, 32), (.s, 32), (.u, 64)]
    else (k, w) ∈ [(.u, 32), (.s, 32), (.u, 64)]
  | .add, .float f => !cluster && f ∈ [.f32, .f64, .f16, .bf16]
  | .min, .int k w | .max, .int k w => if cluster then (k, w) ∈ [(.u, 32), (.s, 32)]
    else (k, w) ∈ [(.u, 32), (.s, 32), (.u, 64), (.s, 64)]
  | .min, .float f | .max, .float f => !cluster && f ∈ [.f16, .bf16]
  | .inc, .int k w | .dec, .int k w => k == .u && w == 32
  | .and, .int _ w | .or, .int _ w | .xor, .int _ w => w == 32 || (!cluster && w == 64)
  | _, _ => false

/-- How a `cp.async.bulk` or `cp.reduce.async.bulk` writes its destination, and the scope of its
strong destination accesses: whole; byte by byte under the 16-bit mask of `.cp_mask` (only to
global memory); or element by element for a reduction (only from `.shared::cta` to
`.shared::cluster` or global memory, with a combination of the table), at the scope of its
`.sem.scope`, `.sys` when absent. -/
def bulkWrites (L : Launch) (g : Nat) (t : TState) (c : BulkCopy) :
    Exec (AsyncCopy.WriteMode × Option MbarScope) :=
  match c.mask, c.reduce with
  | none, none => pure (.whole, none)
  | some m, none => do
    unless c.dir = .ctaToGlobal do throw .noRule
    let v ← readBits L g t 16 m
    pure (.masked (v.toNat % 2 ^ 16), none)
  | none, some (op, ty) => do
    unless (c.dir = .ctaToCluster ∨ c.dir = .ctaToGlobal) ∧ c.ignoreOob = none ∧
      c.multicast = none ∧ bulkReduceOk (c.dir == .ctaToCluster) op ty do throw .noRule
    pure (.reduce ⟨op, ty⟩, some (c.scope.getD .sys))
  | some _, some _ => throw .noRule

/-- The event of a `cp.async.bulk` copy or `cp.reduce.async.bulk` reduction (THREAD-TMA): the
checks of its direction, and its issue event, or for a multicast copy one issue per destination
CTA. -/
def bulkCopyTmpl (L : Launch) (g : Nat) (t : TState) (c : BulkCopy) : Exec Tmpl := do
  bulkPolicy L g t c.cachePolicy
  bulkIgnoreOob L g t c.ignoreOob
  let (mode, sc) ← bulkWrites L g t c
  match c.dir, c.mbar, c.multicast with
  | .globalToCta, some (mb, moff), none => do
    let d ← effAddr L g t .shared c.dst c.dstOff
    let s ← effAddr L g t .global c.src c.srcOff
    let size ← readBits L g t 32 c.size
    let m ← mbarLoc L g t mb moff
    unless 0 < size.toNat ∧ size.toNat % 16 = 0 ∧ d.addr % 16 = 0 ∧ s.addr % 16 = 0 do
      throw .misaligned
    unless bulkRangeOk size.toNat d s do throw .badValue
    pure (.copy (bulkSpec { loc := s, size := size.toNat } { loc := d, size := size.toNat }
      (.mbarrier m) mode sc) (next t))
  | .globalToCluster, some (mb, moff), mc => do
    let d ← sharedEffAddr L g t true c.dst c.dstOff
    let s ← effAddr L g t .global c.src c.srcOff
    let size ← readBits L g t 32 c.size
    let m ← mbarClusterLoc L g t mb moff
    unless bulkSizeOk size.toNat d s do throw .misaligned
    unless bulkRangeOk size.toNat d s do throw .badValue
    match mc with
    | none =>
      unless m.cta = d.cta do throw .badValue
      pure (.copy (bulkSpec { loc := s, size := size.toNat } { loc := d, size := size.toNat }
        (.mbarrier m) mode sc) (next t))
    | some (width, mask) => bulkMulticast L g t s d m size.toNat width mask
  | .ctaToCluster, some (mb, moff), none => do
    let d ← sharedEffAddr L g t true c.dst c.dstOff
    let s ← sharedEffAddr L g t false c.src c.srcOff
    let size ← readBits L g t 32 c.size
    let m ← mbarClusterLoc L g t mb moff
    unless bulkSizeOk size.toNat d s do throw .misaligned
    unless bulkRangeOk size.toNat d s do throw .badValue
    unless d.cta ≠ g / L.block ∧ m.cta = d.cta do throw .badValue
    pure (.copy (bulkSpec { loc := s, size := size.toNat } { loc := d, size := size.toNat }
      (.mbarrier m) mode sc) (next t))
  | .ctaToGlobal, none, none => do
    let d ← effAddr L g t .global c.dst c.dstOff
    let s ← sharedEffAddr L g t false c.src c.srcOff
    let size ← readBits L g t 32 c.size
    unless bulkSizeOk size.toNat d s do throw .misaligned
    unless bulkRangeOk size.toNat d s do throw .badValue
    pure (.copy (bulkSpec { loc := s, size := size.toNat } { loc := d, size := size.toNat }
      .bulkGroup mode sc) (next t))
  | _, _, _ => throw .noRule

/-- The event of an mbarrier or bulk-copy instruction. -/
def tmaTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .mbarInit base off c => ofExec do
    let m ← mbarLoc L g t base off
    let n ← readBits L g t 32 c
    if 0 < n.toNat ∧ n.toNat < 2 ^ 20 then pure (.mbInit m n.toNat (next t))
    else throw .badValue
  | .mbarInval base off => ofExec do pure (.mbInval (← mbarLoc L g t base off) (next t))
  | .fenceMbarInit => .fenceMbarInit (next t)
  | .mbarArrive base off tx count cluster release scope state => ofExec do
    let m ← if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off
    let bytes ← readBits L g t 32 tx
    let n ← readBits L g t 32 count
    pure (.arrive m bytes.toNat (next (mbarStateDest t state)) n.toNat release scope)
  | .mbarWait p base off par acquire scope => ofExec do
    let m ← mbarLoc L g t base off
    let q ← readBits L g t 32 par
    pure (.wait m (q.toNat % 2) (fun ok => next (setReg t p (.pred ok))) acquire scope)
  | .cpBulk c => ofExec (bulkCopyTmpl L g t c)
  | _ => .ub .noRule

/-- The event of the earlier `cp.async.bulk.shared::cta.global.mbarrier::complete_tx::bytes` form,
without qualifiers: the copy of `size` bytes from global to the executing CTA's shared memory,
completed on the mbarrier, after the checks of size, alignment and range. -/
theorem tmaTmpl_cpBulk_cta (L : Launch) (g : Nat) (t : TState) (db : Nat) (doff : Int) (sb : Nat)
    (soff : Int) (n : Opnd) (mb : Nat) (moff : Int) :
    tmaTmpl L g t
        (.cpBulk (BulkCopy.mk .globalToCta db doff sb soff n (some (mb, moff)) none none none none
          none none)) =
      ofExec (do
        let d ← effAddr L g t .shared db doff
        let s ← effAddr L g t .global sb soff
        let size ← readBits L g t 32 n
        let m ← mbarLoc L g t mb moff
        unless 0 < size.toNat ∧ size.toNat % 16 = 0 ∧ d.addr % 16 = 0 ∧ s.addr % 16 = 0 do
          throw .misaligned
        unless bulkRangeOk size.toNat d s do throw .badValue
        pure (.copy (bulkSpec { loc := s, size := size.toNat } { loc := d, size := size.toNat }
          (.mbarrier m) .whole none) (next t))) := rfl

section
variable (L : Launch)

/-! ## DEP-ASYNC-ORIGIN — independent asynchronous effects and object histories
Statement: Every recorded effect of a linear copy or an MMA belongs to an actual issuing
  instruction. A copy writes the bytes it read, and a completion notification or arrive-on requires
  the completion of the operations it tracks. The history of every mbarrier object consists of valid
  steps, and an object fault is still an execution, which the safety check rejects.

Defs: TmaOk

Source:
- §9.7.15.16 (object transitions)
- §9.7.10.28.4.1 (bulk effects and notification)
- §9.7.18.12.1 (commit completion)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)

Direction: reading

Applies: Decoded linear copies, MMA completion, `cp.async.mbarrier.arrive` arrive-on operations and
  mbarrier operations across arbitrary phases

Premises: Each effect has an actual issuing instruction and each object record has an actual source.

Effect: Execution constraints in Consistent.tma. Faults remain possible executions and are
  rejected by safety.
-/

/-- Every recorded linear copy, MMA completion, `cp.async.mbarrier.arrive` arrive-on and mbarrier
history of the execution `X` is valid: effects belong to actual issues, and each object record
follows from the object operations. -/
def TmaOk (X : Execution) : Prop :=
  AsyncCopy.WellFormed (AsyncCopy.issuedBy X) X.async ∧
  AsyncCopy.TcEffectsOk X ∧ AsyncCopy.ObjectsOk X ∧ AsyncCopy.ArriveOk X

end

end

end PTX

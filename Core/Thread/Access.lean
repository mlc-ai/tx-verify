-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Memory.AtomicOp

@[expose] public section

/-!
# Thread semantics: memory instructions

The event a load or store performs: its footprint and, for a load, how the returned bytes become
register values.
-/

namespace PTX

noncomputable section

/-! ## THREAD-ADDR — effective addresses
Statement: The effective address of a load or store is its base plus the offset. A global address
  lies in CTA 0, a shared window address in the issuing thread's CTA or, through a symbolic pointer,
  in a CTA of its cluster, a local address in the issuing thread's own local memory and a constant
  address in the constant memory. A generic address is a symbolic shared pointer, resolved in the
  shared window, a generic local pointer of the issuing thread or a generic constant pointer,
  resolved in their windows, or a number, which is a global address. An invalid base register, a
  generic number of 32 bits, a generic parameter pointer, a generic local pointer of another thread
  and a generic address that leaves its window have no rule, and a store at a generic constant
  pointer is a fault.

Defs: sharedEffAddr, effAddr, wrapAddr, absLoc, accessLoc

Source:
- §9.7.10.8 (ld): "If no state space is given, perform the load using Generic Addressing ."
- §9.7.10.11 (st)
- §6.4.1.1: "A generic address maps to global memory unless it falls within the window for const ,
    local , or shared memory."
- §6.4.1.1: "Within each window, a generic address maps to an address in the underlying state space
    by subtracting the window base from the generic address."
- §5.1.4 (global)
- §5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own data."
- §5.1.3: "The constant ( .const ) state space is a read-only memory initialized by the host."
- §9.7.10.11: "Stores to const memory are illegal."
- §5.1.7 (shared): "Variables declared in .shared state space refer to the memory addresses in the
    current CTA."
- choice: shared layout
- EXT-ADDR-WRAP
- EXT-CVTA
- EXT-LAUNCH (local memories and constant memory at launch)
- EXT-LOCAL-CONST-LAYOUT

Direction: reading

Applies: Global, shared, local, constant and generic effective addresses of loads and stores

Premises: The base register supplies an address of the space: a 64-bit global number, a shared
  number below `2 ^ 32` or a symbolic shared pointer, a local or constant number of the register's
  width, or a generic symbolic shared pointer, generic local or constant pointer or 64-bit number.

Effect: Local address evaluation. THREAD-SHARED-POINTER resolves a symbolic shared pointer, which
  only a thread of its producing CTA can use.
  A global address is a 64-bit register plus offset. A `.shared` address is a 32-bit address in the
  issuing thread's CTA; `.shared` variables live at `sharedBase + offset` (the decoder's layout,
  EXT-SHARED); `.local` and `.const` variables live at `localBase + offset` and `constBase + offset`
  (EXT-LOCAL-CONST-LAYOUT). `accessLoc` locates every access that `memTmpl` does not locate directly
  (`MemAccess.locSpace?`): a `.shared::cluster` address is a cluster pointer (THREAD-SHARED-POINTER)
  or a number of the thread's own `.shared::cta` window, which the `.shared::cluster` window
  contains (§5.1.7). A `.local` address is location `⟨.local, g, x⟩` of thread `g`: each thread has
  its own local memory, and no other thread can name it (EXT-LAUNCH). A `.const` address is location
  `⟨.const, 0, x⟩`; no instruction with a rule writes the constant space (§9.7.10.11: "Stores to
  const memory are illegal."), so a constant read returns the launch memory. A generic symbolic
  shared pointer resolves in the shared window of its target CTA and must stay in `[0, 2 ^ 32)`
  after the offset. A generic local pointer (THREAD-CVTA) resolves in the local memory of
  the issuing thread when that thread owns it, and a generic constant pointer in the constant
  memory, both required to stay in `[0, 2 ^ 32)` after the offset; a generic local pointer of
  another thread has no rule, since local memory is private to each thread (§5.1.5), and a store at
  a generic constant pointer is a fault (`badValue`). A generic number is a global address
  (EXT-CVTA), and a generic parameter pointer has no rule as an access address. A 32-bit generic
  number has no rule.

### EXT-ADDR-WRAP — an address sum wraps at the address width

Statement: The effective address of `[reg+immOff]` is the register's address plus the offset, modulo
  `2^64` for a global address, `2^32` for a shared address and `2^w` for a local or constant address
  in a `w`-bit register (`effAddr`, `sharedEffAddr`, `wrapAddr`). An absolute address
  `[immAddr+immOff]` does not wrap: a negative sum has no rule (`absLoc`). The PTX ISA calls the
  address a sum and does not say what happens when the sum leaves the address range.

Source:
- §6.4.1: "[reg+immOff] a sum of register reg containing a byte address plus a constant integer byte
    offset (signed, 32-bit)."

Why it is not spec text: the text calls the address a sum and says nothing about a sum that
  leaves the address range.

Direction: reading

Effect: If it does not hold, an access whose sum leaves the address range is performed elsewhere on
  hardware or faults, and the model neither reports it nor accesses the same bytes. A kernel whose
  address sums never leave the range does not depend on it. Disclosed by every kernel whose
  statement names `Op.mem`, `Op.mbarInit`, `Op.mbarInval`, `Op.mbarArrive`, `Op.mbarWait`,
  `Op.cpBulk`, `Op.cpTensor`, `Op.cpTensorStore`, `Op.tcAlloc`, `Op.tcCommit` or `Op.clcTryCancel`:
  AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192,
  InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.
-/

/-- Shared effective address with explicit CTA/cluster accessibility. A symbolic pointer's
target is never discarded by reading its logical offset as an integer. -/
def sharedEffAddr (L : Launch) (g : Nat) (t : TState) (cluster : Bool)
    (base : Nat) (off : Int) : Exec Loc := do
  let v ← readReg t base
  match v with
  | .ptr w _ (.shared ..) _ =>
    let loc ← readSharedAddress L g t w false cluster (.reg base)
    pure { loc with addr := (truncBits 32 (BitVec.ofNat 64 loc.addr + BitVec.ofInt 64 off)).toNat }
  | _ =>
    let b ← readBits L g t 32 (.reg base)
    pure ⟨.shared, g / L.block, (truncBits 32 (b + BitVec.ofInt 64 off)).toNat⟩

/-- Effective address of a global or shared access (THREAD-ADDR). -/
def effAddr (L : Launch) (g : Nat) (t : TState) (space : Space) (base : Nat) (off : Int) :
    Exec Loc := do
  match space with
  | .global =>
    let b ← readBits L g t 64 (.reg base)
    pure ⟨.global, 0, (b + BitVec.ofInt 64 off).toNat⟩
  | .shared => sharedEffAddr L g t false base off
  | .local | .const => throw .noRule

/-- The address `x + off` modulo `2 ^ w` (EXT-ADDR-WRAP). -/
def wrapAddr (w : Nat) (x : BitVec 64) (off : Int) : Nat :=
  (truncBits w (x + BitVec.ofInt 64 off)).toNat

/-- An absolute address `x + off` of space `sp` owned by `owner`; a negative sum has no rule. -/
def absLoc (sp : Space) (owner : Nat) (x off : Int) : Exec Loc :=
  if 0 ≤ x + off then pure ⟨sp, owner, (x + off).toNat⟩ else throw .noRule

/-- The location of byte 0 of a load or store whose rule is THREAD-ACCESS, from its state space and
address. A global address is a 64-bit register or an absolute address. A shared window address is
a `.shared` variable of the thread's CTA, a symbolic pointer (THREAD-SHARED-POINTER) or a number
below `2 ^ 32` in the thread's CTA. A local address names thread `g`'s own local memory and a
constant address the constant memory; a `.local` or `.const` variable is at its decoder offset from
`Launch.localBase` or `Launch.constBase` (EXT-LOCAL-CONST-LAYOUT). A generic address is a symbolic
generic shared pointer, resolved in the shared window and required to stay in it, a generic local
pointer of the thread or a generic constant pointer, resolved in its window (a store at a constant
one is `badValue`), or a 64-bit number or absolute address, which is a global address (EXT-CVTA).
Every other address has no rule. -/
def accessLoc (L : Launch) (g : Nat) (t : TState) (a : MemAccess) : Exec Loc := do
  let off := a.addr.off
  match a.space, a.addr.base with
  | some .global, .reg r 64 => effAddr L g t .global r off
  | some .global, .imm x | none, .imm x => absLoc .global 0 x off
  | some .local, .imm x => absLoc .local g x off
  | some .const, .imm x => absLoc .const 0 x off
  | some .local, .localSym o => absLoc .local g (L.localBase + o) off
  | some .const, .constSym o => absLoc .const 0 (L.constBase + o) off
  | some (.shared _), .sharedSym o =>
    pure ⟨.shared, g / L.block, wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + o)) off⟩
  | some (.shared win), .reg r w =>
    match ← readReg t r with
    | .ptr _ _ (.shared ..) _ => sharedEffAddr L g t (win == .cluster) r off
    | _ => do
      let x ← readBits L g t w (.reg r)
      unless x.toNat < 2 ^ 32 do throw .noRule
      pure ⟨.shared, g / L.block, wrapAddr 32 x off⟩
  | some .local, .reg r w => do
    pure ⟨.local, g, wrapAddr w (← readBits L g t w (.reg r)) off⟩
  | some .const, .reg r w => do
    pure ⟨.const, 0, wrapAddr w (← readBits L g t w (.reg r)) off⟩
  | none, .reg r w =>
    match ← readReg t r with
    | .ptr _ true (.shared ..) _ => do
      let loc ← readSharedAddress L g t w true true (.reg r)
      let x := (loc.addr : Int) + off
      unless 0 ≤ x ∧ x < 2 ^ 32 do throw .noRule
      pure ⟨.shared, loc.cta, x.toNat⟩
    | .ptr pw true (.local owner) o => do
      unless pw = w ∧ owner = g do throw .noRule
      let x := (o.toNat : Int) + off
      unless 0 ≤ x ∧ x < 2 ^ 32 do throw .noRule
      pure ⟨.local, g, x.toNat⟩
    | .ptr pw true .const o => do
      unless pw = w do throw .noRule
      if a.kind = .store then throw .badValue
      let x := (o.toNat : Int) + off
      unless 0 ≤ x ∧ x < 2 ^ 32 do throw .noRule
      pure ⟨.const, 0, x.toNat⟩
    | _ => do
      unless w = 64 do throw .noRule
      pure ⟨.global, 0, wrapAddr 64 (← readBits L g t 64 (.reg r)) off⟩
  | _, _ => throw .noRule

/-! ## THREAD-BYTES — the value of read bytes
Statement: A load rebuilds a value from the bytes it read. The bits of the value are the bits of the
  bytes, little-endian, and the bytes of one whole stored value give that value back. An absent byte
  is an `uninitialized` fault, and bytes that have no bit pattern and are not one whole stored value
  have no rule.

Defs: byteBits, intByte, littleEndianBits, rebuildBits, rebuild, rebuild.halves, memFloat

Source:
- §8.2 (memory is bytes)
- §5.2.5 (packed data types)
- §5.2.1: "The bit-size type is compatible with any fundamental type having the same size."
- EXT-ENDIAN

Direction: stricter

Applies: Reconstructing loaded scalar or packed values

Premises: The bytes are present and each is a byte of a value with a bit pattern, or they are the
  bytes of one whole stored value.

Effect: Local consumption of read bytes. A byte's bits are byte `k` of the stored value's bit
  pattern (THREAD-BITS), independently of which store supplied it and of its type. The bytes of one
  whole stored value give that value back, so a floating payload keeps its number. Integer bytes of
  1, 2, 4 or 8 bytes give the corresponding bit vector; a 16-byte load uses two 64-bit halves. Other
  bytes are split into halves, which keeps whole floating payloads (a packed pair); a piece that
  cannot be split further is the bit vector of its bytes. Partial reads of opaque payloads
  (pointers, CLC responses), which have no bit pattern, are model coverage gaps (Direction:
  stricter). `memFloat` is the number a load of a `fmt` element followed by a `fmt` instruction
  reads from memory: the rebuilt value read as a `fmt` operand (THREAD-NUM).
-/

/-- Bits of byte `k` of a stored value: byte `k` of its bit pattern. -/
def byteBits : Byte → Option Nat
  | (v, k) => do
    let n ← v.bitPattern
    if k < v.bytes then pure (n / 256 ^ k % 256) else none

/-- A byte of a stored integer. -/
def intByte : Option Byte → Bool
  | some (.bits .., _) => true
  | _ => false

/-- Assemble the bits of read bytes; the source writes, their widths and types may differ. -/
def littleEndianBits : List (Option Byte) → Option Nat
  | [] => some 0
  | none :: _ => none
  | some b :: bs => do
    let x ← byteBits b
    let xs ← littleEndianBits bs
    pure (x + 256 * xs)

/-- A 128-bit data value is represented losslessly by two 64-bit halves. -/
def rebuildBits (bs : List (Option Byte)) : Option Value := do
  let x ← littleEndianBits bs
  if bs.length = 1 ∨ bs.length = 2 ∨ bs.length = 4 ∨ bs.length = 8 then
    pure (.bits (8 * bs.length) (BitVec.ofNat 64 x))
  else if bs.length = 16 then
    pure (.pair (.bits 64 (BitVec.ofNat 64 x)) (.bits 64 (BitVec.ofNat 64 (x / 2 ^ 64))))
  else none

/-- The value of read bytes (BYTES). -/
def rebuild : Nat → List (Option Byte) → Exec Value
  | 0, _ => throw .noRule
  | fuel + 1, bs =>
    match bs with
    | some (v, 0) :: _ =>
      if v.bytes = bs.length ∧ bs = v.toBytes.map some then pure v else halves fuel bs
    | _ => halves fuel bs
where
  halves (fuel : Nat) (bs : List (Option Byte)) : Exec Value :=
    if none ∈ bs then throw .uninitialized
    else if bs.all intByte ∨ fuel = 0 ∨ ¬ (2 ≤ bs.length ∧ bs.length % 2 = 0) then
      match rebuildBits bs with
      | some v => pure v
      | none => throw .noRule
    else do
      let lo ← rebuild fuel (bs.take (bs.length / 2))
      let hi ← rebuild fuel (bs.drop (bs.length / 2))
      pure (.pair lo hi)

/-- The `fmt` number of the `fmt.bytes` bytes at `l` of memory `m`, read as a load and a `fmt`
instruction read them: the loaded value (`rebuild`) as a `fmt` operand (`valFloat`). Absent
and unknown bytes are `uninitialized`. -/
def memFloat (fmt : FloatFmt) (m : Loc → Option (Option Byte)) (l : Loc) : Exec ℝ := do
  valFloat fmt (← rebuild 3 ((List.range fmt.bytes).map fun k => (m (l.at k)).join))

/-! ## THREAD-ACCESS — footprints of loads and stores
Statement: A load or store performs one read or write event per element at the location its address
  names, carrying the access's memory semantics and scope; `.volatile` accesses are
  `.relaxed` at `.sys`, and `.mmio` accesses keep their `.relaxed`, `.acquire` or `.release` at
  `.sys`. A scalar access must be aligned to its size and a vector access to its whole size,
  otherwise the behaviour is undefined. A narrow load is sign- or zero-extended into a wider
  destination register, a store writes the bytes of its source value or the low bits of a wider
  source register, and a source that is too narrow is a fault. `st.bulk` writes zero bytes to a
  region of the thread's `.shared::cta` window whose address is aligned to the region's size, the
  access size of §6.4.1. Cache hints have no effect, and `ld.global.nc` has a
  rule only under a kernel assumption that allows its site.

Defs: elemAcc, setRegs, afterLoad, loadTmpl, afterStore, storeTmpl, acquireLoadTmpl,
  releaseStoreTmpl, MemAccess.strongLocOk, MemAccess.strongLocOk_of_not_mmio, MemAccess.semAcc,
  MemAccess.semAcc_mmio_relaxed, accessAcc, accessAcc_of_weak, extendLoaded, afterAccessLoad,
  bulkInitTmpl, accessTmpl, memTmpl, memTmpl_direct_weakLoad, memTmpl_direct_weakStore, storeValue,
  storeValue_of_bytes

Source:
- §9.7.10.8 (ld): "A destination register wider than the specified type may be used. The value
    loaded is sign-extended to the destination register width for signed integers, and is
    zero-extended to the destination register width for unsigned and bit-size types."
- §9.7.10.8 (ld): "The .level::prefetch_size qualifier is a hint to fetch additional data of the
    specified size into the respective cache level."
- §9.7.10.8 (ld): "If the generic address does not fall within the address window of the global
    memory, then the prefetching behavior is undefined."
- §9.7.10.8 (ld): "The qualifiers .unified and .level::cache_hint are only supported for .global
    state space and for generic addressing where the address points to the .global state space."
- §9.7.10.8 (ld): "The .v8 ( .vec ) qualifier is supported if: .type is .b32 or .s32 or .u32 or .f32
    AND State space is .global or with generic addressing where address points to .global state
    space"
- §9.7.10.1: "Cache operators on load or store instructions are treated as performance hints only.
    The use of a cache operator on an ld or st instruction does not change the memory consistency
    behavior of the program."
- §9.7.10.1: "When ld.cs is applied to a Local window address, it performs the ld.lu operation."
- §9.7.10.1: "The compiler/programmer may use ld.lu when restoring spilled registers and popping
    function stack frames to avoid needless write-backs of lines that will not be used again."
- §9.7.10.2: "Cache eviction priority on load or store instructions is treated as a performance
    hint. It is supported for .global state space and generic addresses where the address points to
    .global state space."
- §9.7.10.9 (ld.global.nc)
- §9.7.10.11 (st): "A source register wider than the specified type may be used. The lower n bits
    corresponding to the instruction-type width are stored to memory."
- §9.7.10.14 (st.bulk): "size must be a multiple of 8. If the value is not a multiple of 8, then the
    behavior is undefined."
- §9.7.10.14 (st.bulk): "The maximum value of size operand can be 16777216."
- §9.7.10.14 (st.bulk): "If the address specified by a does not fall within the address window of
    .shared state space then the behavior is undefined."
- §6.4.1 (st.bulk alignment): "The access size of a memory instruction is the total number of bytes
    accessed in memory."
- §6.4.1 (st.bulk alignment): "The address must be naturally aligned to a multiple of the access
    size. If an address is not properly aligned, the resulting behavior is undefined."
- §8.2.4: "Memory operations with a vector data type are modeled as a set of equivalent memory
    operations with a scalar data type, executed in an unspecified order on the elements in the
    vector."
- §5.4.5 (alignment)
- §8.4.2: "The semantics of volatile operations are equivalent to a relaxed memory operation with
    system-scope but with the following extra implementation-specific constraints:"
- §8.4.1: "For formal specification of semantics of mmio operation from Memory Consistency Model
    perspective, it is equivalent to the semantics of a strong operation."
- §8.4.1: "As an exception, in some implementations, the surrounding locations may also be loaded."
- §8.2 (Table 20): "acquire operation A memory operation with .acquire or .acq_rel qualifier."
- §8.2 (Table 20): "release operation A memory operation with .release or .acq_rel qualifier."
- §9.7.10.8: ".relaxed and .acquire : May be used with .global , .shared spaces, or with generic
    addressing where the address points to .global or .shared space."
- §9.7.10.8: ".volatile : May be used with .global , .shared , .local spaces, or with generic
    addressing where the address points to .global , .shared , or .local space."
- §9.7.10.8: ".mmio : May be used only with .global space or with generic addressing where the
    address points to .global space."
- §9.7.10.8: "Only .sys thread scope is valid for ld.mmio operation."
- EXT-VECTOR-ELEM

Direction: reading

Applies: The loads, stores and `st.bulk` whose rule is THREAD-ACCESS (`MemAccess.rule`,
  PROG-ISA-MEM); every other memory access is `noRule` (`memTmpl`)

Premises: Address, alignment, widths and operands pass the checks below; nc requires an assumption
  that enables its site.

Effect: Event production and local faults. A scalar access is aligned to its size, a vector access
  to its whole size; otherwise it is undefined. A vector access is a set of scalar memory
  operations, one event per element; the trace lists them in element order, and MEM-PROGRAM-ORDER
  orders no two elements of one access (§8.2.4: the element operations are "executed in an
  unspecified order"). Which bytes and which register each element has is EXT-VECTOR-ELEM. A store
  writes the bytes of its source value; a wider source register (decoded for the `.b`, `.u` and `.s`
  types) gives the low bits of its bit pattern (`storeValue`); a wider source without a bit pattern
  (a pointer) is a `typeMismatch` fault (stricter). A narrower source is a `typeMismatch` fault
  (Table 27 makes it invalid). A `st.bulk` of `size` bytes accesses `size` bytes, so its address
  must be a multiple of `size` (§6.4.1; §9.7.10.14 states no alignment of its own); otherwise it is
  `misaligned`. A `st.bulk` of size 0 accesses no byte and has no alignment condition.
  `ld.global.nc` is outside the memory model (§8.1) and has no core
  rule; it is a read only under a kernel assumption that allows it.
  A strong access (`strongOk`, PROG-ISA-MEM) has the same events with its semantics in the
  footprint (`semAcc`): `.relaxed`, `.acquire` or `.release` at the instruction's scope, and
  `.volatile` as `.relaxed` at `.sys`. An `.mmio` access (`MemAccess.mmio`) is a strong operation
  (§8.4.1) with its own `.sem` at `.sys`: an `ld.mmio.acquire.sys` is an acquire load and an
  `st.mmio.release.sys` a release store, so they form release and acquire patterns
  (MEM-RELEASE-ACQUIRE) like the same accesses without `.mmio`. The extra implementation-specific
  constraints of `.volatile` (instruction counts preserved, no reordering among volatile
  instructions) and the properties of `.mmio` (never combined, never cached) only restrict the
  hardware, so leaving them out admits more executions. An `.mmio` load may also load surrounding
  locations; those loads return nothing to the thread and write nothing, and the model's memory has
  no I/O device whose state they could change. A strong access at a location the text does not allow
  for its semantics (for example a generic address of a local location for `.relaxed`) has no rule
  (`strongLocOk`). `memTmpl` performs a weak scalar or vector access, a scalar acquire load and a
  scalar release store directly when it is a global access through a 64-bit register or a
  `.shared::cta` access through a 32-bit register without extension or cache hints
  (`MemAccess.locSpace?`); every other access is located by `accessLoc` (THREAD-ADDR) and performed
  by `accessTmpl`, with the same events. A loaded value is extended into its register
  (`extendLoaded`, `MemExt.extendBits`); a value without a bit pattern cannot be extended
  (`typeMismatch`). The cache operators, eviction priorities, the prefetch size and the cache policy
  are recorded in `CacheHints` and change nothing. The manual supports the eviction priorities, the
  prefetch size and the cache policy only for global addresses and states undefined prefetching for
  a generic address outside the global window, so such an access at another location has no rule;
  `.v8` and `.v4` of 64-bit elements likewise need a global location. `ld.lu`, and `ld.cs` on a
  local address, may drop the line without writing it back, which the text describes for spilled
  registers; a local load with either has no rule (stricter). `st.bulk` is one weak write of `size`
  zero bytes at a location of the thread's own `.shared::cta` window; a size that is not a multiple
  of 8 or above `16777216` is undefined, and so is an address outside that window, which includes
  every generic number (EXT-CVTA) and a pointer of another CTA.

### EXT-VECTOR-ELEM — which address and register an element has

Statement: Element `j` of a vector load, store, `atom` or `red` of `n`-byte elements at `base` is
  the scalar access to bytes `base + j n` to `base + (j + 1) n - 1`, and it uses register `j` of
  each vector operand. The PTX ISA names the elements and gives neither their addresses nor their
  registers.

Source:
- §8.2.4: "Memory operations with a vector data type are modeled as a set of equivalent memory
    operations with a scalar data type, executed in an unspecified order on the elements in the
    vector"
- §5.4.2 and §5.4.5 (a vector access is aligned to its whole size)

Why it is not spec text: §8.2.4 names the elements and says nothing about their addresses or
  registers; it does not state that the elements lie at consecutive addresses in register order.
  This is the ascending-address, register-order layout of a vector in memory. The order in which
  the elements execute is not part of this reading: §8.2.4 leaves it unspecified and the model
  keeps it unspecified (MEM-PROGRAM-ORDER).

Effect: The layout is one the toolchain is assumed to follow. Disclosed by every kernel whose
  statement names `MemAccess.mk (vec ≠ 1)`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192,
  InklingRelDecode, RmsNorm, TcGemm.
-/

/-- Footprint of element `j` of an access of `count` elements of `n` bytes at `base`
(ACCESS). -/
def elemAcc (base : Loc) (n count j : Nat) : Exec Acc :=
  if n = 0 ∨ base.addr % (n * count) ≠ 0 then throw .misaligned else pure
    { loc := base.at (n * j), size := n, elem := j }

/-- Set the registers `ds` to the values `vs`, pairwise. -/
def setRegs (t : TState) : List Nat → List Value → TState
  | d :: ds, v :: vs => setRegs (setReg t d v) ds vs
  | _, _ => t

/-- The state after element `t.sub` of a load into `ds` returned bytes `bs`. -/
def afterLoad (t : TState) (ds : List Nat) (bs : List (Option Byte)) : TState :=
  match rebuild 3 bs with
  | .error f => { t with fault := some f }
  | .ok v =>
    if t.sub + 1 < ds.length then { t with sub := t.sub + 1, acc := t.acc ++ [v] }
    else { setRegs t ds (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }

/-- Element `t.sub` of a load into `ds`. -/
def loadTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (sp : Space) (nc : Bool)
    (w : Nat) (ds : List Nat) (base : Nat) (off : Int) : Tmpl :=
  match effAddr L g t sp base off >>= fun loc => elemAcc loc (w / 8) ds.length t.sub with
  | .error f => .ub f
  | .ok a =>
    if nc then
      if sp = .global ∧ A.any (·.ncLoads t.pc) then .readNC a (afterLoad t ds) else .ub .noRule
    else .read a (afterLoad t ds)

/-- The state after element `t.sub` of a store of `srcs`. -/
def afterStore (t : TState) (srcs : List Opnd) : TState :=
  if t.sub + 1 < srcs.length then { t with sub := t.sub + 1 } else { t with pc := t.pc + 1, sub :=
    0 }

/-- The value a `w`-bit store writes from source value `v` (§9.7.10.11): `v` itself when it has
`w / 8` bytes, and the low `w` bits of its bit pattern when it is wider. A narrower source, and a
wider one without a bit pattern, are `typeMismatch`. -/
def storeValue (w : Nat) (v : Value) : Exec Value :=
  if v.bytes = w / 8 then pure v
  else if w / 8 < v.bytes then match v.bitPattern with
    | some n => pure (.bits w (truncBits w (BitVec.ofNat 64 n)))
    | none => throw .typeMismatch
  else throw .typeMismatch

/-- A source of the store's own size is written unchanged, as before wider sources had a rule. -/
theorem storeValue_of_bytes {w : Nat} {v : Value} (h : v.bytes = w / 8) :
    storeValue w v = .ok v := by simp [storeValue, h]; rfl

/-- Element `t.sub` of a store of `srcs`. -/
def storeTmpl (L : Launch) (g : Nat) (t : TState) (sp : Space) (w : Nat) (base : Nat)
    (off : Int) (srcs : List Opnd) : Tmpl :=
  match effAddr L g t sp base off >>= fun loc => elemAcc loc (w / 8) srcs.length t.sub with
  | .error f => .ub f
  | .ok a =>
    match srcs[t.sub]? with
    | none => .ub .typeMismatch
    | some o =>
      match readValue L g t w o >>= storeValue w with
      | .error f => .ub f
      | .ok v => .write a v.toBytes (afterStore t srcs)

/-- Preserve the load footprint and raw-byte result while retaining acquire scope. -/
def acquireLoadTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState)
    (scope : MbarScope) (sp : Space) (w : Nat) (d base : Nat) (off : Int) : Tmpl :=
  match loadTmpl A L g t sp false w [d] base off with
  | .read a k => .read { a with acquire := true, scope := scope } k
  | other => other

/-- Release stores retain scope for matching read-from synchronization. -/
def releaseStoreTmpl (L : Launch) (g : Nat) (t : TState)
    (scope : MbarScope) (sp : Space) (w : Nat) (base : Nat) (off : Int) (v : Opnd) : Tmpl :=
  match storeTmpl L g t sp w base off [v] with
  | .write a bs t' => .write { a with release := true, scope := scope } bs t'
  | other => other

/-- The location spaces a strong access may name (§9.7.10.8, §9.7.10.11): global for `.mmio`,
global and shared for `.relaxed`, `.acquire` and `.release`, also local for `.volatile`; every
space for a weak access. -/
def MemAccess.strongLocOk (a : MemAccess) (sp : Space) : Bool :=
  match a.sem with
  | .relaxed | .acquire | .release | .acqRel =>
    if a.mmio then sp == .global else sp == .global || sp == .shared
  | .volatile => sp == .global || sp == .shared || sp == .local
  | .weak => true

/-- Without `.mmio`, `strongLocOk` is the check by memory semantics it was before `.mmio` became a
flag of the access. -/
theorem MemAccess.strongLocOk_of_not_mmio {a : MemAccess} (h : a.mmio = false) (sp : Space) :
    a.strongLocOk sp = match a.sem with
      | .relaxed | .acquire | .release | .acqRel => sp == .global || sp == .shared
      | .volatile => sp == .global || sp == .shared || sp == .local
      | .weak => true := by
  cases hs : a.sem <;> simp [MemAccess.strongLocOk, hs, h]

/-- The footprint `acc` with the memory semantics and scope of a load or store (§8.4): `.relaxed`,
`.acquire` or `.release` at the instruction's scope, also for an `.mmio` access, whose scope is
`.sys`, and `.volatile` as `.relaxed` at `.sys`; a weak footprint is unchanged. -/
def MemAccess.semAcc (a : MemAccess) (acc : Acc) : Acc :=
  match a.sem with
  | .weak => acc
  | .relaxed => { acc with relaxed := true, scope := a.scope.getD .cta }
  | .acquire => { acc with acquire := true, scope := a.scope.getD .cta }
  | .release => { acc with release := true, scope := a.scope.getD .cta }
  | .acqRel => { acc with acquire := true, release := true, scope := a.scope.getD .cta }
  | .volatile => { acc with relaxed := true, scope := .sys }

/-- An `.mmio.relaxed.sys` access has the footprint it had when `.mmio` was a memory semantics of
its own: `.relaxed` at `.sys`. -/
theorem MemAccess.semAcc_mmio_relaxed {a : MemAccess} (acc : Acc) (hs : a.sem = .relaxed)
    (hsc : a.scope = some .sys) : a.semAcc acc = { acc with relaxed := true, scope := .sys } := by
  simp [MemAccess.semAcc, hs, hsc]

/-- The footprint of element `t.sub` of a load or store located by `accessLoc`, with the access's
memory semantics (`semAcc`). `.nc`, the cache hints `globalOnly`, `.v8` and `.v4` of 64-bit
elements need a global location, and a strong access a location of `strongLocOk`; they have no rule
at another one. -/
def accessAcc (L : Launch) (g : Nat) (t : TState) (a : MemAccess) : Exec Acc := do
  let loc ← accessLoc L g t a
  let w := a.elem.width
  if (a.nc || a.hints.globalOnly || a.vec == 8 || (a.vec == 4 && w == 64)) && loc.space != .global
  then throw .noRule
  unless a.strongLocOk loc.space do throw .noRule
  a.semAcc <$> elemAcc loc (w / 8) a.vec t.sub

/-- For a weak access, `accessAcc` is the footprint it was before strong accesses had a rule. -/
theorem accessAcc_of_weak {L : Launch} {g : Nat} {t : TState} {a : MemAccess}
    (h : a.sem = .weak) : accessAcc L g t a = (do
      let loc ← accessLoc L g t a
      let w := a.elem.width
      if (a.nc || a.hints.globalOnly || a.vec == 8 || (a.vec == 4 && w == 64)) &&
        loc.space != .global then throw .noRule
      elemAcc loc (w / 8) a.vec t.sub) := by
  have hs : a.semAcc = id := by funext acc; simp [MemAccess.semAcc, h]
  simp [accessAcc, MemAccess.strongLocOk, h, hs]

/-- A loaded `w`-bit value in its destination register: unchanged, zero-extended or
sign-extended (§9.7.10.8); a value without a bit pattern cannot be extended. -/
def extendLoaded (ext : MemExt) (w : Nat) (v : Value) : Exec Value :=
  match ext with
  | .same => pure v
  | .zero _ | .sign _ => match v.bitPattern with
    | some n => pure (ext.extendBits w (BitVec.ofNat 64 n))
    | none => throw .typeMismatch

/-- The state after element `t.sub` of a `w`-bit load with extension `ext` into `ds` returned
bytes `bs`. -/
def afterAccessLoad (t : TState) (ext : MemExt) (w : Nat) (ds : List Nat)
    (bs : List (Option Byte)) : TState :=
  match rebuild 3 bs >>= extendLoaded ext w with
  | .error f => { t with fault := some f }
  | .ok v =>
    if t.sub + 1 < ds.length then { t with sub := t.sub + 1, acc := t.acc ++ [v] }
    else { setRegs t ds (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] }

/-- `st.bulk`: one write of `size` zero bytes at a location of the thread's own `.shared::cta`
window. A size that is not a multiple of 8 or exceeds `16777216`, an address outside that window,
and an address that is not a multiple of a nonzero size (§6.4.1), are undefined. -/
def bulkInitTmpl (L : Launch) (g : Nat) (t : TState) (a : MemAccess) : Tmpl :=
  let r : Exec (Loc × Nat) := do
    let loc ← accessLoc L g t a
    unless loc.space = .shared ∧ loc.cta = g / L.block do throw .badValue
    let n ← match a.srcs with
      | .reg r :: _ => do
        let .bits _ x ← readReg t r | throw .typeMismatch
        pure x.toNat
      | .imm v :: _ => if 0 ≤ v then pure v.toNat else throw .badValue
      | _ => throw .noRule
    unless n % 8 = 0 ∧ n ≤ 16777216 do throw .badValue
    unless n = 0 ∨ loc.addr % n = 0 do throw .misaligned
    pure (loc, n)
  match r with
  | .error f => .ub f
  | .ok (loc, n) => .write { loc := loc, size := n } (List.replicate n (.bits 8 0, 0)) (next t)

/-- Element `t.sub` of a load or store, or the `st.bulk`, that `accessLoc` locates. -/
def accessTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (a : MemAccess) :
    Tmpl :=
  let w := a.elem.width
  match a.kind with
  | .bulkInit => bulkInitTmpl L g t a
  | .load =>
    match accessAcc L g t a with
    | .error f => .ub f
    | .ok acc =>
      let k := afterAccessLoad t a.ext w a.regs
      if a.nc then (if A.any (·.ncLoads t.pc) then .readNC acc k else .ub .noRule)
      else .read acc k
  | .store =>
    match accessAcc L g t a with
    | .error f => .ub f
    | .ok acc =>
      match a.srcs[t.sub]? with
      | none => .ub .typeMismatch
      | some o =>
        match readValue L g t w o >>= storeValue w with
        | .error f => .ub f
        | .ok v => .write acc v.toBytes (afterStore t a.srcs)
  | _ => .ub .noRule

/-! ## THREAD-ATOMIC — atomic read-modify-write instructions
Statement: An `atom` or `red` with a rule performs one atomic read-modify-write event per scalar
  element, each vector element and each half of a packed type being its own: it reads the
  element's old bytes and writes the value of its operation on them, at the location its address
  names in the global or shared space, the global space for a vector. `atom` writes the old values
  to its destination registers unless the destination is the sink `_`, and `red` has no
  destination. The access is strong, with the memory semantics and scope of the instruction,
  `.relaxed` and `.gpu` when they are absent.

Defs: MemAccess.atomElems, atomAcc, MemAccess.elemSrcs, MemAccess.elemSrcs_of_vec_one, pairUp,
  afterAtom, afterAtom_of_length_le_one, atomTmpl, atomTmpl_of_vec_one, memTmpl_atomic

Source:
- §9.7.15.5 (atom): "Atomically loads the original value at location a into destination register d ,
    performs a reduction operation with operand b and the value in location a , and stores the
    result of the specified operation at location a , overwriting the original value."
- §9.7.15.5 (atom): "atom with scalar type may be used only with .global and .shared spaces and with
    generic addressing, where the address points to .global or .shared space."
- §9.7.15.5 (atom): "atom with vector type may be used only with .global space and with generic
    addressing where the address points to .global space."
- §9.7.15.5 (atom): "For atom with vector type, operands d and b are brace-enclosed vector
    expressions, size of which is equal to the size of vector qualifier."
- §9.7.15.5 (atom): "If the .sem qualifier is absent, .relaxed is assumed by default."
- §9.7.15.5 (atom): "If the .scope qualifier is absent, .gpu scope is assumed by default."
- §9.7.15.5 (atom): "atom instruction on packed type or vector type, accesses adjacent scalar
    elements in memory. In such cases, the atomicity is guaranteed separately for each of the
    individual scalar elements; the entire atom is not guaranteed to be atomic as a single access."
- §9.7.15.5 (atom): "Simple reductions may be specified by using the bit bucket destination operand
    _ ."
- §9.7.15.5 (atom): "The qualifier .level::cache_hint is only supported for .global state space and
    for generic addressing where the address points to the .global state space."
- §9.7.15.5 (atom): "It is treated as a performance hint only, and does not change the memory
    consistency behavior of the program."
- §9.7.15.5 (atom), Table 41 rows: ".u32 .add , .inc , .dec , .min , .max Not supported Not
    supported .s32 .add , .min , .max Not supported Not supported .u64 .add , .min , .max Not
    supported Not supported .s64 .min , .max Not supported Not supported .f32 Not supported
    .add{.noftz} Not supported .f64 Not supported .add (noftz by default) Not supported .f16 Not
    supported .add (requires .noftz ) Not supported"
- §9.7.15.5 (atom), Table 41 rows: ".b16 Not supported Not supported .cas .b32 Not supported Not
    supported .and , .or , .xor , .exch , .cas .b64 Not supported Not supported .and , .or , .xor ,
    .exch , .cas .b128 Not supported Not supported .exch , .cas"
- §9.7.15.5 (atom): "atom{.sem}{.scope}{.global}.add{.noftz}{.level::cache_hint}.vec_32_bit.f32 d,
    [a], b{, cache_policy};"
- §9.7.15.5 (atom): ".half_word_type = { .f16, .bf16 }; .packed_type = { .f16x2, .bf16x2 };
    .vec_16_bit = { .v2, .v4, .v8 } .vec_32_bit = { .v2, .v4 };"
- §9.7.15.5 (atom), vector table: "Vector qualifier Types .f16 / bf16 .f16x2 / bf16x2 .f32 .v2 .add
    , .min , .max (all require .noftz ) .add , .min , .max (all require .noftz ) .add .v4 .add ,
    .min , .max (all require .noftz ) .add , .min , .max (all require .noftz ) .add .v8 .add , .min
    , .max (all require .noftz ) Not supported Not Supported"
- §9.7.15.6 (red): "Performs a reduction operation with operand b and the value in location a , and
    stores the result of the specified operation at location a , overwriting the original value."
- §9.7.15.6 (red): ".sem = { .relaxed, .release }"
- §9.7.15.6 (red): "red with scalar type may be used only with .global and .shared spaces and with
    generic addressing, where the address points to .global or .shared space."
- §9.7.15.6 (red): "red with vector type may be used only with .global space and with generic
    addressing where the address points to .global space."
- §9.7.15.6 (red): "For red with vector type, operand b is brace-enclosed vector expressions, size
    of which is equal to the size of vector qualifier."
- §9.7.15.6 (red): "red instruction on packed type or vector type, accesses adjacent scalar elements
    in memory. In such case, the atomicity is guaranteed separately for each of the individual
    scalar elements; the entire red is not guaranteed to be atomic as a single access."
- §8.2 (Table 20): "read operation All variants of ld instruction and atom instruction (but not red
    instruction)."
- §5.4.5: "Note that all PTX instructions that access memory require that the address be aligned to
    a multiple of the access size. The access size of a memory instruction is the total number of
    bytes accessed in memory."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- THREAD-ADDR
- THREAD-ATOMIC-OP
- THREAD-BYTES
- EXT-VECTOR-ELEM

Direction: stricter

Applies: The scalar and vector `atom` and `red` forms whose rule is THREAD-ATOMIC
  (`MemAccess.atomicOk`, PROG-ISA-MEM)

Premises: The operation and type are a combination of Table 41 (`atom`) or Table 42 (`red`), or
  for a vector form of the vector table; the address names a global or shared location, a global
  one for a vector form, aligned to the access size; each source has the size of the type.

Effect: Event production (`.rmw`) and local faults; the event's read and write enter the memory
  model as one operation (MEM-FOOTPRINT, ERR-DATA-RACE, MEM-ATOMICITY, MEM-RELEASE-ACQUIRE). A
  scalar element is the whole value for a scalar type and each half for `.f16x2` and `.bf16x2`, and
  a vector form (`.v2`, `.v4`, `.v8`) has the scalar elements of each of its vector elements in
  turn. The manual guarantees atomicity only for each scalar element of a packed or vector type, so
  each scalar element is its own atomic operation, and the scalar elements of one instruction are
  unordered among themselves as the elements of a vector access are (MEM-PROGRAM-ORDER). Scalar
  element `j` of `m`-byte scalar elements lies at bytes `base + j m` to `base + (j + 1) m - 1`:
  vector element `e` at `base + e s` for `s`-byte vector elements (EXT-VECTOR-ELEM), and half `h` of
  a packed value at its bytes `2 h` and `2 h + 1` (EXT-ENDIAN, THREAD-BYTES). Vector element `e`
  takes register `e` of each vector operand (`elemSrcs`, EXT-VECTOR-ELEM). The address is located as
  a load's (`accessLoc`, THREAD-ADDR); a location outside the global and shared spaces has no rule,
  and so have a vector form and a cache hint at a location outside the global space (a generic
  address of a shared location included). An access is aligned to its whole size (a scalar's size,
  both halves of a packed value, all elements of a vector), otherwise it is `misaligned`. The
  event's footprint carries the semantics: every `atom` and `red` is strong (`relaxed`, `acquire`,
  `release`), its scope is the instruction's, `.gpu` when absent, and only an `atom` has an
  acquiring read, because Table 20 does not count `red` as a read operation. The bytes written are
  the value of THREAD-ATOMIC-OP on the rebuilt old value and the operands; when that has no value
  (`noRule`, `typeMismatch`) the event writes nothing and the thread's next event is `ub`. The old
  values, rebuilt from the bytes read (THREAD-BYTES), are written to the destination registers after
  the last scalar element, register `e` receiving vector element `e`, one packed value for a packed
  type (`afterAtom`, `pairUp`). A `cas` compares bit patterns. The `min` and `max` of the
  half-precision vector forms are floating operations and take their value from an assumption as
  every floating operation does (THREAD-ATOMIC-OP).
  The following forms have no rule: the combinations that Table 41, Table 42 and the vector table do
  not list, `atom` and `red` of a local or constant location, a vector form at a shared location, an
  `atom` whose destination vector mixes registers and the sink `_`, `red` with `.acquire` or
  `.acq_rel`, and `.f64` floating forms under the ideal-real assumption, which gives no `.f64`
  value.
-/

/-- The element type and the number of elements of an `atom` or `red`: two halves for a packed
type, the type itself otherwise. -/
def MemAccess.atomElems (a : MemAccess) : DType × Nat :=
  match a.elem with
  | .packed e n => (e, n)
  | e => (e, 1)

/-- The footprint `acc` of an `atom` or `red` element with the instruction's memory semantics and
scope (`.gpu` when absent). Only an `atom` acquires (§8.2 Table 20). -/
def atomAcc (a : MemAccess) (acc : Acc) : Acc :=
  let isRmw : Bool := match a.kind with | .rmw _ => true | _ => false
  { acc with
    relaxed := a.sem == .relaxed
    acquire := isRmw && (a.sem == .acquire || a.sem == .acqRel)
    release := a.sem == .release || a.sem == .acqRel
    scope := a.scope.getD .gpu }

/-- The operands of vector element `e` of an access of `a.vec` elements: each operand of the
instruction is a vector of `a.vec` registers, and element `e` uses register `e` of each
(EXT-VECTOR-ELEM). A scalar access uses its operands themselves (`elemSrcs_of_vec_one`). -/
def MemAccess.elemSrcs (a : MemAccess) (e : Nat) : List Opnd :=
  (List.range (a.srcs.length / a.vec)).filterMap fun i => a.srcs[i * a.vec + e]?

/-- The operands of a scalar access are its sources. -/
theorem MemAccess.elemSrcs_of_vec_one {a : MemAccess} (h : a.vec = 1) : a.elemSrcs 0 = a.srcs := by
  simp only [MemAccess.elemSrcs, h, Nat.div_one, Nat.mul_one, Nat.add_zero]
  generalize a.srcs = l
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    have : ((fun i => (x :: l)[i]?) ∘ Nat.succ) = fun i => l[i]? := rfl
    rw [this, ih]; rfl

/-- Packed pairs of consecutive values: `[lo, hi, …]` gives `[.pair lo hi, …]`. -/
def pairUp : List Value → List Value
  | lo :: hi :: vs => .pair lo hi :: pairUp vs
  | vs => vs

/-- The state after element `t.sub` of `n` of an atomic access read the old bytes `old`: the
rebuilt old values are collected, and after the last element the destination registers `ds`
receive them, one value per register, a packed pair for `k = 2` scalar elements per register.
The sink `_` (`[none]`) and no destination (`[]`) receive nothing. Destination registers whose
number does not match the values are a `typeMismatch` fault, and so is a value that cannot be
rebuilt. -/
def afterAtom (t : TState) (ds : List (Option Nat)) (k n : Nat) (old : List (Option Byte)) :
    TState :=
  match rebuild 3 old with
  | .error f => { t with fault := some f }
  | .ok v =>
    if t.sub + 1 < n then { t with sub := t.sub + 1, acc := t.acc ++ [v] }
    else
      let vs := t.acc ++ [v]
      let t' : TState := { t with pc := t.pc + 1, sub := 0, acc := [] }
      match ds with
      | [] | [none] => t'
      | ds =>
        let rs := ds.filterMap id
        if rs.length = ds.length ∧ vs.length = k * rs.length then
          setRegs t' rs (if k = 2 then pairUp vs else vs)
        else { t' with fault := some .typeMismatch }

/-- A scalar access (at most one destination, `n = k` scalar elements, one or a packed pair) at
an element whose earlier elements are collected (`t.acc.length = t.sub < n`) continues as before
the vector forms had a rule: the old value goes to destination `ds.head?.join`. -/
theorem afterAtom_of_length_le_one {t : TState} {ds : List (Option Nat)} {n : Nat}
    {old : List (Option Byte)} (hds : ds.length ≤ 1) (hn : n = 1 ∨ n = 2)
    (hacc : t.acc.length = t.sub) (hs : t.sub < n) :
    afterAtom t ds n n old =
      match rebuild 3 old with
      | .error f => { t with fault := some f }
      | .ok v =>
        if t.sub + 1 < n then { t with sub := t.sub + 1, acc := t.acc ++ [v] }
        else
          let vs := t.acc ++ [v]
          let t' : TState := { t with pc := t.pc + 1, sub := 0, acc := [] }
          match ds.head?.join, vs with
          | some r, [x] => setReg t' r x
          | some r, [lo, hi] => setReg t' r (.pair lo hi)
          | some _, _ => { t' with fault := some .typeMismatch }
          | none, _ => t' := by
  unfold afterAtom
  cases rebuild 3 old with
  | error f => rfl
  | ok v =>
    simp only
    split
    · rfl
    · have hl : t.sub + 1 = n := by omega
      match ds, hds with
      | [], _ => rfl
      | [none], _ => rfl
      | [some r], _ =>
        rcases hn with rfl | rfl
        · match hA : t.acc with
          | [] => simp [setRegs]
          | _ :: _ => simp [hA] at hacc; omega
        · match hA : t.acc with
          | [lo] => simp [setRegs, pairUp]
          | [] => simp [hA] at hacc; omega
          | _ :: _ :: _ => simp [hA] at hacc; omega

/-- Element `t.sub` of an `atom` or `red` (THREAD-ATOMIC): an atomic read-modify-write at the
scalar element's global or shared location, writing the value of THREAD-ATOMIC-OP for the
element's operation on the old value and the element of each operand. Scalar element `t.sub` is
half `t.sub % 2` of vector element `t.sub / 2` for a packed type, and vector element `t.sub`
otherwise; a vector access needs a global location. -/
def atomTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (a : MemAccess) : Tmpl :=
  let (ty, k) := a.atomElems
  let n := a.vec * k
  let elemOf (v : Value) : Value := if k = 2 then
      (if t.sub % 2 = 0 then (splitValue a.elem.width v).1 else (splitValue a.elem.width v).2)
    else v
  let r : Exec (AtomOp × Acc × List Value) := do
    let some op := a.kind.atomOp? | throw .noRule
    let loc ← accessLoc L g t a
    unless loc.space = .global ∨ loc.space = .shared do throw .noRule
    if (a.hints.policy.isSome || a.vec != 1) && loc.space != .global then throw .noRule
    let acc ← elemAcc loc (ty.width / 8) n t.sub
    let vs ← (a.elemSrcs (t.sub / k)).mapM fun o => do
      let v ← readValue L g t a.elem.width o
      unless 8 * v.bytes = a.elem.width do throw .typeMismatch
      pure (elemOf v)
    pure (op, acc, vs)
  match r with
  | .error f => .ub f
  | .ok (op, acc, vs) =>
    .rmw (atomAcc a acc)
      (fun old => do
        let v ← rmwValue A op ty (← rebuild 3 old) vs
        unless 8 * v.bytes = ty.width do throw .typeMismatch
        pure v.toBytes)
      (afterAtom t a.dsts k n)

/-- A scalar `atom` or `red` (`vec = 1`) at a scalar element below its count performs the template
it had before the vector forms had a rule: its operands are the sources themselves and a packed
type splits them at element 0 and 1. -/
theorem atomTmpl_of_vec_one {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} (h : a.vec = 1) (hs : t.sub < a.atomElems.2) :
    atomTmpl A L g t a =
      let (ty, n) := a.atomElems
      let elemOf (v : Value) : Value := if n = 2 then
          (if t.sub = 0 then (splitValue a.elem.width v).1 else (splitValue a.elem.width v).2)
        else v
      let r : Exec (AtomOp × Acc × List Value) := do
        let some op := a.kind.atomOp? | throw .noRule
        let loc ← accessLoc L g t a
        unless loc.space = .global ∨ loc.space = .shared do throw .noRule
        if a.hints.policy.isSome && loc.space != .global then throw .noRule
        let acc ← elemAcc loc (ty.width / 8) n t.sub
        let vs ← a.srcs.mapM fun o => do
          let v ← readValue L g t a.elem.width o
          unless 8 * v.bytes = a.elem.width do throw .typeMismatch
          pure (elemOf v)
        pure (op, acc, vs)
      match r with
      | .error f => .ub f
      | .ok (op, acc, vs) =>
        .rmw (atomAcc a acc)
          (fun old => do
            let v ← rmwValue A op ty (← rebuild 3 old) vs
            unless 8 * v.bytes = ty.width do throw .typeMismatch
            pure v.toBytes)
          (afterAtom t a.dsts n n) := by
  unfold atomTmpl
  generalize a.atomElems = p at hs ⊢
  obtain ⟨ty, k⟩ := p
  simp only at hs ⊢
  have hd : t.sub / k = 0 := Nat.div_eq_of_lt hs
  simp only [h, Nat.one_mul, hd, MemAccess.elemSrcs_of_vec_one h, bne_self_eq_false,
    Bool.or_false]
  by_cases hk : k = 2
  · subst hk
    have hz : (t.sub % 2 = 0) = (t.sub = 0) := propext (by omega)
    simp only [hz]
  · simp only [hk, ite_false]

/-- The event of a memory access with THREAD-ACCESS as its rule (`MemAccess.rule`). An access
located directly (`locSpace?`) is a weak load or store, an acquire load or a release store at its
location space and element width; every other one is `accessTmpl`. An access with THREAD-ATOMIC
as its rule is `atomTmpl`. Every other access has no rule. -/
def memTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (a : MemAccess) : Tmpl :=
  match a.rule, a.locSpace?, a.addr.base with
  | some .threadAccess, some sp, .reg base _ =>
    let w := a.elem.width
    let off := a.addr.off
    match a.kind, a.sem, a.regs, a.srcs with
    | .load, .acquire, [d], _ => acquireLoadTmpl A L g t (a.scope.getD .cta) sp w d base off
    | .load, .weak, ds, _ => loadTmpl A L g t sp a.nc w ds base off
    | .store, .release, _, [v] => releaseStoreTmpl L g t (a.scope.getD .cta) sp w base off v
    | .store, .weak, _, vs => storeTmpl L g t sp w base off vs
    | _, _, _, _ => accessTmpl A L g t a
  | some .threadAtomic, _, _ => atomTmpl A L g t a
  | r, _, _ => if r = some .threadAccess then accessTmpl A L g t a else .ub .noRule

/-- A weak load located directly is `loadTmpl`, as before strong accesses had a rule. -/
theorem memTmpl_direct_weakLoad {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {sp : Space} {base w : Nat} (hr : a.rule = some .threadAccess)
    (hl : a.locSpace? = some sp) (hb : a.addr.base = .reg base w) (hk : a.kind = .load)
    (hs : a.sem = .weak) :
    memTmpl A L g t a = loadTmpl A L g t sp a.nc a.elem.width a.regs base a.addr.off := by
  simp only [memTmpl, hr, hl, hb, hk, hs]

/-- A weak store located directly is `storeTmpl`, as before strong accesses had a rule. -/
theorem memTmpl_direct_weakStore {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {sp : Space} {base w : Nat} (hr : a.rule = some .threadAccess)
    (hl : a.locSpace? = some sp) (hb : a.addr.base = .reg base w) (hk : a.kind = .store)
    (hs : a.sem = .weak) :
    memTmpl A L g t a = storeTmpl L g t sp a.elem.width base a.addr.off a.srcs := by
  simp only [memTmpl, hr, hl, hb, hk, hs]

/-- An access with THREAD-ATOMIC as its rule performs `atomTmpl`. -/
theorem memTmpl_atomic {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {a : MemAccess}
    (h : a.rule = some .threadAtomic) : memTmpl A L g t a = atomTmpl A L g t a := by
  simp only [memTmpl, h]

end

end PTX

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Async.AsyncStore
public import Core.Async.CpAsync
public import Core.Async.AsyncCopy
public import Core.Async.Tensor.TensorReduce
public import Core.Assembly.Safety

/-! Decoding, thread events and effect validity of the remaining asynchronous forms: the linear
reduction `cp.reduce.async.bulk`, the masked copy `.cp_mask`, `st.async`, `red.async`, the
`.mbarrier::report::disabled` mechanism, the generic `cp.async.mbarrier.arrive`, and the
same-group overlap of `cp.async` destinations. Each accepted form has its exact result, next to
the rejected neighbours. -/
namespace PTX.Tests.AsyncReduceStore
noncomputable section
open PTX.Syntax

/-! ## Decoding -/

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 8, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%p".toList, 1, 1⟩,
      ⟨"%h".toList, 2, 16⟩], labels := [], params := [] }
private def at' (n : String) : Operand := .address [.register n]
private def unmodeled : Except String Op → Bool
  | .ok (.unmodeled _) => true
  | _ => false
private def isOk : Except String Op → Bool
  | .ok _ => true
  | .error _ => false

-- Registers: `%r0`-`%r7` are 0-7, `%rd0` and `%rd1` are 8 and 9, `%p0` is 10, `%h0` is 11.
private def red2c := "cp.reduce.async.bulk.shared::cluster.shared::cta.mbarrier::complete_tx::bytes"
example : Decode.op env (red2c ++ ".add.u32") [at' "%r0", at' "%r1", .register "%r2", at' "%r3"] =
    .ok (.cpBulk (BulkCopy.mk .ctaToCluster 0 0 1 0 (.reg 2) (some (3, 0)) none none none none
      (some (.add, .int .u 32)) none)) := rfl
example : Decode.op env "cp.reduce.async.bulk.global.shared::cta.bulk_group.add.noftz.f16"
    [at' "%rd0", at' "%r0", .register "%r1"] =
    .ok (.cpBulk (BulkCopy.mk .ctaToGlobal 8 0 0 0 (.reg 1) none none none none none
      (some (.add, .float .f16)) none)) := rfl
-- `.relaxed.scope` records the scope of the element reductions.
example : Decode.op env "cp.reduce.async.bulk.relaxed.cta.global.shared::cta.bulk_group.add.u64"
    [at' "%rd0", at' "%r0", .register "%r1"] =
    .ok (.cpBulk (BulkCopy.mk .ctaToGlobal 8 0 0 0 (.reg 1) none none none none none
      (some (.add, .int .u 64)) (some .cta))) := rfl
-- A completion mechanism that does not belong to the direction has no instruction entry.
example : isOk (Decode.op env
    "cp.reduce.async.bulk.global.shared::cta.mbarrier::complete_tx::bytes.add.u32"
    [at' "%rd0", at' "%r0", .register "%r1", at' "%r2"]) = false := rfl
-- `st.async` and `red.async` with an mbarrier, and their `.release` forms.
example : Decode.op env "st.async.shared::cluster.mbarrier::complete_tx::bytes.u32"
    [at' "%r0", .register "%r1", at' "%r2"] =
    .ok (.asyncStore (AsyncStore.mk none (.int .u 32) 1 (some (.shared .cluster)) ⟨.reg 0 32, 0⟩
      [.reg 1] (some ⟨.reg 2 32, 0⟩) none)) := rfl
example : Decode.op env "st.async.shared::cluster.mbarrier::complete_tx::bytes.v2.u32"
    [at' "%r0", .vector [.register "%r1", .register "%r2"], at' "%r3"] =
    .ok (.asyncStore (AsyncStore.mk none (.int .u 32) 2 (some (.shared .cluster)) ⟨.reg 0 32, 0⟩
      [.reg 1, .reg 2] (some ⟨.reg 3 32, 0⟩) none)) := rfl
example : Decode.op env "st.async.release.gpu.global.u64" [at' "%rd0", .register "%rd1"] =
    .ok (.asyncStore (AsyncStore.mk none (.int .u 64) 1 (some .global) ⟨.reg 8 64, 0⟩ [.reg 9]
      none (some .gpu))) := rfl
example : Decode.op env
    "red.async.relaxed.cluster.shared::cluster.mbarrier::complete_tx::bytes.min.u32"
    [at' "%r0", .register "%r1", at' "%r2"] =
    .ok (.asyncStore (AsyncStore.mk (some .min) (.int .u 32) 1 (some (.shared .cluster))
      ⟨.reg 0 32, 0⟩ [.reg 1] (some ⟨.reg 2 32, 0⟩) none)) := rfl
example : Decode.op env "red.async.release.sys.global.add.s64" [at' "%rd0", .register "%rd1"] =
    .ok (.asyncStore (AsyncStore.mk (some .add) (.int .s 64) 1 (some .global) ⟨.reg 8 64, 0⟩
      [.reg 9] none (some .sys))) := rfl
-- The `.mmio` forms are not modeled.
example : unmodeled (Decode.op env "st.async.mmio.release.sys.global.u32"
    [at' "%rd0", .register "%r1"]) = true := rfl
example : unmodeled (Decode.op env "red.async.mmio.release.sys.global.add.u32"
    [at' "%rd0", .register "%r1"]) = true := rfl
-- `.mbarrier::report::disabled` is the plain copy; a validity report is not modeled.
example : Decode.op env
    "cp.async.bulk.shared::cta.global.mbarrier::complete_tx::bytes.mbarrier::report::disabled"
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"] =
    Decode.op env "cp.async.bulk.shared::cta.global.mbarrier::complete_tx::bytes"
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"] := rfl
set_option maxRecDepth 8000 in
example : unmodeled (Decode.op env
    "cp.async.bulk.shared::cta.global.mbarrier::complete_tx::bytes.mbarrier::report::\
      validity::per_16bytes::8000"
    [at' "%r0", at' "%rd0", .register "%r1", at' "%r2"]) = true := rfl
-- A generic `cp.async.mbarrier.arrive` takes a 64-bit address.
example : Decode.op env "cp.async.mbarrier.arrive.b64" [at' "%rd0"] =
    .ok (.cpAsyncArrive false 8 0 true) := rfl
example : Decode.op env "cp.async.mbarrier.arrive.noinc.shared.b64" [at' "%r0"] =
    .ok (.cpAsyncArrive true 0 0) := rfl

/-! ## Thread events -/

private def L : Launch := { grid := 2, block := 32, params := fun _ => none, clusterSize := 2 }
private def L1 : Launch := { grid := 2, block := 32, params := fun _ => none, clusterSize := 1 }
-- Thread 0 is in CTA 0 of the cluster of CTAs 0 and 1.
private def t : TState := { regs := fun
  | 0 => some (.bits 32 64)
  | 1 => some (.bits 64 4096)
  | 2 => some (.bits 32 64)
  | 3 => some (.bits 32 128)
  | 4 => some (.ptr 32 false (.shared 0 1) 64)
  | 5 => some (.ptr 32 false (.shared 0 1) 128)
  | 6 => some (.bits 16 0x00FF)
  | 7 => some (.bits 32 5)
  | 8 => some (.bits 64 7)
  | 9 => some (.bits 64 4100)
  | 10 => some (.ptr 64 true (.shared 0 0) 128)
  | 11 => some (.ptr 64 true (.shared 0 1) 128)
  | 14 => some (.bits 32 256)
  | 12 => some (.bits 64 0xfffffffffffffff0)
  | 13 => some (.bits 32 32)
  | 15 => some (.bits 16 0)
  | 16 => some (.bits 64 0xffffffffffffffe0)
  | 17 => some (.bits 32 0xfffffff0)
  | _ => none }

private def acc (l : Loc) (n : Nat) : Acc := { loc := l, size := n }
private def sh (c a : Nat) : Loc := ⟨.shared, c, a⟩
private def gl (a : Nat) : Loc := ⟨.global, 0, a⟩

/-- The copy spec and next pc of an issue event. -/
private def issued : Tmpl → Option (AsyncCopy.Spec × Nat)
  | .copy s u => some (s, u.pc)
  | _ => none
private def fault : Tmpl → Option Fault
  | .ub f => some f
  | _ => none
private def rd (dir : BulkDir) (d s : Nat) (mbar : Option (Nat × Int)) (op : AtomOp) (ty : DType)
    (scope : Option MbarScope := none) : Op :=
  .cpBulk (BulkCopy.mk dir d 0 s 0 (.reg 2) mbar none none none none (some (op, ty)) scope)

-- A shared-to-cluster reduction: 64 bytes of `.u32` elements reduced into CTA 1, `.relaxed.sys`.
example : issued (tmaTmpl L 0 t (rd .ctaToCluster 4 14 (some (5, 0)) .add (.int .u 32))) =
    some (.mk (acc (sh 0 256) 64) (acc (sh 1 64) 64) (.mbarrier (sh 1 128))
      (.reduce ⟨.add, .int .u 32⟩) none false (some .sys), 1) := rfl
-- A shared-to-global reduction with `.relaxed.gpu`, completed through the bulk group.
example : issued (tmaTmpl L 0 t (rd .ctaToGlobal 1 14 none .max (.int .s 64) (some .gpu))) =
    some (.mk (acc (sh 0 256) 64) (acc (gl 4096) 64) .bulkGroup (.reduce ⟨.max, .int .s 64⟩) none
      false (some .gpu), 1) := rfl
example : issued (tmaTmpl L 0 t (rd .ctaToGlobal 1 14 none .add (.float .bf16))) =
    some (.mk (acc (sh 0 256) 64) (acc (gl 4096) 64) .bulkGroup (.reduce ⟨.add, .float .bf16⟩) none
      false (some .sys), 1) := rfl
-- Combinations outside the table of the destination have no rule.
example : fault (tmaTmpl L 0 t (rd .ctaToCluster 4 14 (some (5, 0)) .add (.int .s 64))) =
    some .noRule := rfl
example : fault (tmaTmpl L 0 t (rd .ctaToCluster 4 14 (some (5, 0)) .xor (.int .b 64))) =
    some .noRule := rfl
example : fault (tmaTmpl L 0 t (rd .ctaToGlobal 1 14 none .inc (.int .s 32))) = some .noRule :=
  rfl
example : fault (tmaTmpl L 0 t (rd .ctaToGlobal 1 14 none .exch (.int .b 32))) = some .noRule :=
  rfl
-- A reduction from global memory has no rule; the size and alignment checks are the copy's.
example : fault (tmaTmpl L 0 t (rd .globalToCta 0 1 (some (3, 0)) .add (.int .u 32))) =
    some .noRule := rfl
example : fault (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 1 0 14 0 (.imm 8) none none
    none none none (some (.add, .int .u 32)) none))) = some .misaligned := rfl
-- `.cp_mask`: bit `k % 16` of the mask selects byte `k`; only shared-to-global.
example : issued (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 1 0 14 0 (.reg 2) none none
    none none (some (.reg 6)) none none))) =
    some (.mk (acc (sh 0 256) 64) (acc (gl 4096) 64) .bulkGroup (.masked 255) none false none, 1)
    := rfl
example : fault (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .globalToCta 0 0 1 0 (.reg 2) (some (3, 0))
    none none none (some (.reg 6)) none none))) = some .noRule := rfl
example : fault (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 1 0 14 0 (.reg 2) none none
    none none (some (.reg 20)) none none))) = some .uninitialized := rfl
-- The range check holds whatever the mask selects (§9.7.10.28.4.1: "The memory range [dstMem,
-- dstMem + size - 1] must not overflow the destination memory space"). A zero mask with
-- `dstMem = 0xfffffffffffffff0` and `size = 32` overflows the 64-bit global space: undefined.
example : fault (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 12 0 14 0 (.reg 13) none none
    none none (some (.reg 15)) none none))) = some .badValue := rfl
-- The same without `.cp_mask`, and a reduction: undefined as well.
example : fault (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 12 0 14 0 (.reg 13) none none
    none none none none none))) = some .badValue := rfl
example : fault (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 12 0 14 0 (.reg 13) none none
    none none none (some (.add, .int .u 32)) none))) = some .badValue := rfl
-- A range that ends exactly at the end of the space is a copy.
example : issued (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 16 0 14 0 (.reg 13) none none
    none none (some (.reg 15)) none none))) =
    some (.mk (acc (sh 0 256) 32) (acc (gl 0xffffffffffffffe0) 32) .bulkGroup (.masked 0) none
      false none, 1) := rfl
-- A shared source range past `2^32`: undefined.
example : fault (tmaTmpl L 0 t (.cpBulk (BulkCopy.mk .ctaToGlobal 1 0 17 0 (.reg 13) none none
    none none (some (.reg 15)) none none))) = some .badValue := rfl

private def st (red : Option AtomOp) (ty : DType) (vec : Nat) (sp : Option StateSpace) (a : Nat)
    (aw : Nat) (srcs : List Opnd) (mbar : Option Nat) (rel : Option MbarScope) : AsyncStore :=
  AsyncStore.mk red ty vec sp ⟨.reg a aw, 0⟩ srcs (mbar.map fun m => ⟨.reg m aw, 0⟩) rel
private def data : Tmpl → Option (List Byte)
  | .copy s _ => s.data
  | _ => none
private def shape : Tmpl → Option (Acc × AsyncCopy.Completion × AsyncCopy.WriteMode ×
    Option MbarScope × Bool)
  | .copy s _ => some (s.dst, s.completion, s.writes, s.scope, s.generic)
  | _ => none

-- `st.async` into CTA 1 of the cluster, completed on the mbarrier there.
example : shape (asyncStoreTmpl L 0 t
    (st none (.int .u 32) 1 (some (.shared .cluster)) 4 32 [.reg 7] (some 5) none)) =
    some (acc (sh 1 64) 4, .mbarrier (sh 1 128), .whole, none, true) := rfl
example : data (asyncStoreTmpl L 0 t
    (st none (.int .u 32) 1 (some (.shared .cluster)) 4 32 [.reg 7] (some 5) none)) =
    some (Value.bits 32 5).toBytes := rfl
-- Into the executing CTA, by EXT-ST-ASYNC-CTA.
example : shape (asyncStoreTmpl L 0 t
    (st none (.int .b 32) 1 (some (.shared .cluster)) 0 32 [.reg 7] (some 3) none)) =
    some (acc (sh 0 64) 4, .mbarrier (sh 0 128), .whole, none, true) := rfl
-- A cluster of one CTA, an mbarrier in another CTA and a misaligned address are undefined.
example : fault (asyncStoreTmpl L1 0 t
    (st none (.int .u 32) 1 (some (.shared .cluster)) 0 32 [.reg 7] (some 3) none)) =
    some .badValue := rfl
example : fault (asyncStoreTmpl L 0 t
    (st none (.int .u 32) 1 (some (.shared .cluster)) 4 32 [.reg 7] (some 3) none)) =
    some .badValue := rfl
example : fault (asyncStoreTmpl L 0 t
    (st none (.int .u 64) 1 (some (.global)) 9 64 [.reg 8] none (some .gpu))) =
    some .misaligned := rfl
-- A value of the wrong size and a vector not of the syntax are rejected.
example : fault (asyncStoreTmpl L 0 t
    (st none (.int .u 64) 1 (some (.shared .cluster)) 4 32 [.reg 7] (some 5) none)) =
    some .typeMismatch := rfl
example : fault (asyncStoreTmpl L 0 t
    (st none (.int .u 64) 4 (some (.shared .cluster)) 4 32 [.reg 8, .reg 8, .reg 8, .reg 8]
      (some 5) none)) = some .noRule := rfl
-- The release form writes global memory with a strong access and no observable completion.
example : shape (asyncStoreTmpl L 0 t
    (st none (.int .u 64) 1 (some .global) 1 64 [.reg 8] none (some .gpu))) =
    some (acc (gl 4096) 8, .unobserved, .whole, some .gpu, true) := rfl
example : fault (asyncStoreTmpl L 0 t
    (st none (.int .u 32) 1 (some (.shared .cluster)) 4 32 [.reg 7] none (some .gpu))) =
    some .badValue := rfl
-- `red.async` reduces one element of a CTA other than the executing one, at `.cluster` scope.
example : shape (asyncStoreTmpl L 0 t
    (st (some .min) (.int .u 32) 1 (some (.shared .cluster)) 4 32 [.reg 7] (some 5) none)) =
    some (acc (sh 1 64) 4, .mbarrier (sh 1 128), .reduce ⟨.min, .int .u 32⟩, some .cluster,
      true) := rfl
example : fault (asyncStoreTmpl L 0 t
    (st (some .min) (.int .u 32) 1 (some (.shared .cluster)) 0 32 [.reg 7] (some 3) none)) =
    some .badValue := rfl
example : fault (asyncStoreTmpl L 0 t
    (st (some .add) (.int .s 64) 1 (some (.shared .cluster)) 4 32 [.reg 8] (some 5) none)) =
    some .noRule := rfl
example : shape (asyncStoreTmpl L 0 t
    (st (some .add) (.int .s 64) 1 (some .global) 1 64 [.reg 8] none (some .sys))) =
    some (acc (gl 4096) 8, .unobserved, .reduce ⟨.add, .int .s 64⟩, some .sys, true) := rfl
example : fault (asyncStoreTmpl L 0 t
    (st (some .inc) (.int .u 32) 1 (some .global) 1 64 [.reg 7] none (some .sys))) =
    some .noRule := rfl
-- A generic address of a shared pointer of another CTA resolves in the cluster window.
example : shape (asyncStoreTmpl L 0 t
    (st none (.int .u 32) 1 none 11 64 [.reg 7] (some 11) none)) =
    some (acc (sh 1 128) 4, .mbarrier (sh 1 128), .whole, none, true) := rfl
-- A generic global address is outside the shared window.
example : fault (asyncStoreTmpl L 0 t
    (st none (.int .u 32) 1 none 1 64 [.reg 7] (some 11) none)) = some .badValue := rfl

-- A generic `cp.async.mbarrier.arrive` names an mbarrier of the executing CTA.
private def arrived : Tmpl → Option (Loc × Bool)
  | .asyncArrive m noinc _ => some (m, noinc)
  | _ => none
example : arrived (cpAsyncTmpl L 0 t (.cpAsyncArrive false 10 0 true)) = some (sh 0 128, false) :=
  rfl
example : fault (cpAsyncTmpl L 0 t (.cpAsyncArrive false 11 0 true)) = some .badValue := rfl
example : fault (cpAsyncTmpl L 0 t (.cpAsyncArrive false 1 0 true)) = some .noRule := rfl

/-! ## Effects of element-wise operations -/

private def b0 : Byte := (Value.bits 8 1, 0)
private def b1 : Byte := (Value.bits 8 2, 0)
private def masked : AsyncCopy.Spec :=
  { src := acc (sh 0 0) 2, dst := acc (gl 0) 2, completion := .bulkGroup, writes := .masked 1 }
private def redSpec : AsyncCopy.Spec :=
  { src := acc (sh 0 0) 4, dst := acc (sh 1 0) 4, completion := .mbarrier (sh 1 8),
    writes := .reduce ⟨.add, .int .u 32⟩, scope := some .sys }

-- A masked copy has one element per selected byte; a reduction one per element of its type.
example : masked.elems = [{ loc := gl 0, size := 1 }] := by decide
example : redSpec.elems = [{ loc := sh 1 0, size := 4 }] := by decide
-- The write stage of a masked copy needs every element written.
example : ¬ AsyncCopy.CopyOk masked { readBytes := some [b0, b1], writeBytes := some [] } := by
  intro h
  have hw := h.2.2.1 _ rfl
  simp [masked, AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets] at hw
  exact absurd (hw 0) (by decide)
-- A masked byte is its source byte.
example : ¬ AsyncCopy.CopyOk masked
    { readBytes := some [b0, b1], elemWrites := fun j => if j = 0 then some [b1] else none } := by
  intro h
  obtain ⟨-, -, ⟨src, hs, hm⟩, -⟩ := h.2.2.2.2.1 0 [b1] rfl
  simp [AsyncCopy.sourceBytes, masked] at hs
  obtain ⟨k, hk, hb⟩ := hm 1 rfl
  subst hs
  have hk0 : k = 0 := by
    have : masked.elemOffsets[0]? = some 0 := by decide
    rw [this] at hk
    exact (Option.some.inj hk).symm
  subst hk0
  simp [b0, b1] at hb
-- A reduction element writes only together with its old-value read.
example : ¬ AsyncCopy.CopyOk redSpec
    { readBytes := some [b0, b0, b0, b0],
      elemWrites := fun j => if j = 0 then some [b0, b0, b0, b0] else none } := by
  intro h
  obtain ⟨-, -, -, hold⟩ := h.2.2.2.2.1 0 _ rfl
  obtain ⟨old, ho⟩ := hold _ rfl
  simp at ho
-- A register source is never read.
example : ¬ AsyncCopy.CopyOk { redSpec with data := some [b0, b0, b0, b0] }
    { readBytes := some [b0, b0, b0, b0] } := by
  intro h
  simpa using (h.2.1 _ rfl).1

-- The value a linear reduction element writes is THREAD-ATOMIC-OP's: 5 + 7 = 12.
private def five : List Byte := (Value.bits 32 5).toBytes
private def seven : List Byte := (Value.bits 32 7).toBytes
/-- A whole 4-byte value read back is that value (THREAD-BYTES). -/
private theorem rebuild4 (v : Value) (h4 : v.bytes = 4) (hb : ∀ k, v.byteAt k = (v, k)) :
    rebuild 3 (v.toBytes.map some) = .ok v := by
  simp [rebuild, Value.toBytes, h4, List.range_succ, hb]; rfl
private theorem reduceValue (ty : DType) :
    TensorStore.copyReduceValue [] { redSpec with data := some seven } ⟨.add, ty⟩
      { elemOld := fun _ => some five } 0 = some (do
        let a ← rebuild 3 (five.map some)
        let b ← rebuild 3 (seven.map some)
        rmwValue [] .add ty a [b]) := rfl
example : TensorStore.copyReduceValue [] { redSpec with data := some seven } ⟨.add, .int .u 32⟩
    { elemOld := fun _ => some five } 0 = some (.ok (Value.bits 32 12)) := by
  rw [reduceValue, five, seven, rebuild4 _ rfl fun _ => rfl, rebuild4 _ rfl fun _ => rfl]; rfl
-- A floating element without an assumption has no rule.
example : TensorStore.copyReduceValue [] { redSpec with data := some seven } ⟨.add, .float .f32⟩
    { elemOld := fun _ => some five } 0 = some (.error .noRule) := by
  rw [reduceValue, five, seven, rebuild4 _ rfl fun _ => rfl, rebuild4 _ rfl fun _ => rfl]; rfl

/-! ## The destination range of a masked copy (ERR-BULK-MASK-RANGE) -/

private def zeroMask : AsyncCopy.Spec :=
  { src := acc (sh 0 0) 32, dst := acc (gl 4096) 32, completion := .bulkGroup,
    writes := .masked 0 }
private def maskedExec : Execution :=
  { tr := fun g => if g = 0 then [⟨0, .copy zeroMask⟩] else [], rf := fun _ _ => none }
-- The launch memory: the source and the first 16 destination bytes are allocated.
private def mem16 : Mem0 := fun l =>
  if l.space = .shared ∨ (l.space = .global ∧ 4096 ≤ l.addr ∧ l.addr < 4112) then some none
  else none
private def mem32 : Mem0 := fun l =>
  if l.space = .shared ∨ (l.space = .global ∧ 4096 ≤ l.addr ∧ l.addr < 4128) then some none
  else none

-- A zero-mask copy writes no byte, but its range reaches an unallocated byte: unsafe.
example : MaskedRangeUnalloc mem16 maskedExec :=
  ⟨(0, 0), zeroMask, 0, gl 4112, ⟨0, rfl⟩, rfl,
    by simp [zeroMask, acc, gl, Acc.Covers, Loc.InRange], by simp [mem16, gl]⟩
example : TmaUnsafe L mem16 maskedExec :=
  .inr (.inr (.inr (.inr
    ⟨(0, 0), zeroMask, 0, gl 4112, ⟨0, rfl⟩, rfl,
      by simp [zeroMask, acc, gl, Acc.Covers, Loc.InRange], by simp [mem16, gl]⟩)))
-- With the whole range allocated the check passes.
example : ¬ MaskedRangeUnalloc mem32 maskedExec := by
  rintro ⟨⟨g, k⟩, s, m, l, ⟨pc, h⟩, -, hc, hn⟩
  by_cases hg : g = 0
  · subst hg
    rcases k with _ | k <;> simp [Execution.get, maskedExec] at h
    obtain ⟨-, rfl⟩ := h
    simp [zeroMask, acc, gl, Acc.Covers, Loc.InRange] at hc
    obtain ⟨hs, -, hlo, hhi⟩ := hc
    simp [mem32, hs] at hn
    omega
  · simp [Execution.get, maskedExec, hg] at h

/-! ## Two `cp.async` of one group copying to one location -/

private def cpSpec (a : Nat) : AsyncCopy.Spec :=
  .mk (acc (gl 4096) 4) (acc (sh 0 a) 4) .asyncGroup .whole none true none
private def ev (k : Kind) : Event := ⟨0, k⟩
private def exec (tr : List Event) : Execution :=
  { tr := fun g => if g = 0 then tr else [], rf := fun _ _ => none }

-- Identical copies in one group: undefined, although they write the same bytes.
example : CpAsyncOverlap (exec [ev (.copy (cpSpec 64)), ev (.copy (cpSpec 64))]) :=
  ⟨(0, 0), (0, 1), cpSpec 64, cpSpec 64,
    ⟨⟨_, ⟨0, rfl⟩, rfl⟩, ⟨_, ⟨0, rfl⟩, rfl⟩, rfl, by decide, fun k pc h1 h2 => by omega⟩,
    ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨sh 0 64, by simp [acc, cpSpec, Acc.Covers, Loc.InRange]⟩⟩
-- Disjoint destinations in one group are allowed.
example : ¬ CpAsyncOverlap (exec [ev (.copy (cpSpec 64)), ev (.copy (cpSpec 68))]) := by
  rintro ⟨⟨g, a⟩, ⟨g', b⟩, s, s', ⟨-, -, hij, hlt, -⟩, ⟨pc, hi⟩, ⟨pc', hj⟩, l, hl, hl'⟩
  simp only at hij hlt
  subst hij
  by_cases hg : g = 0
  · subst hg
    rcases a with _ | _ | a <;> rcases b with _ | _ | b <;>
      simp [Execution.get, exec, ev] at hi hj <;> try omega
    obtain ⟨-, rfl⟩ := hi
    obtain ⟨-, rfl⟩ := hj
    simp [cpSpec, acc, sh, Acc.Covers, Loc.InRange] at hl hl'
    omega
  · simp [Execution.get, exec, hg] at hi
-- Overlapping copies separated by a commit belong to different groups.
example : ¬ CpAsyncOverlap
    (exec [ev (.copy (cpSpec 64)), ev .asyncCommit, ev (.copy (cpSpec 64))]) := by
  rintro ⟨⟨g, a⟩, ⟨g', b⟩, s, s', ⟨⟨_, ⟨pc, hi⟩, -⟩, ⟨_, ⟨pc', hj⟩, -⟩, hij, hlt, hno⟩, -, -, -⟩
  simp only at hij hlt hno
  subst hij
  by_cases hg : g = 0
  · subst hg
    rcases a with _ | _ | _ | a <;> rcases b with _ | _ | _ | b <;>
      simp [Execution.get, exec, ev] at hi hj <;> try omega
    exact hno 1 0 (by omega) (by omega) rfl
  · simp [Execution.get, exec, hg] at hi

end

end PTX.Tests.AsyncReduceStore

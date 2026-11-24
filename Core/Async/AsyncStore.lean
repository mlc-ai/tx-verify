-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tma

@[expose] public section

/-!
# Thread semantics: asynchronous stores and reductions from registers

The events of `st.async` and `red.async`. When their writes are performed and who observes them
are decided by the execution rules (DEP-LINEAR-COPY-EFFECTS, MEM-OBSERVED-COMPLETION,
MEM-MODEL-CAUSALITY).
-/

namespace PTX

noncomputable section

/-! ## THREAD-ASYNC-STORE — st.async and red.async
Statement: An `st.async` or `red.async` produces one issue event: a linear operation in the
  generic proxy whose source is the bytes of its register operands and whose destination is the
  location its address names. The `.mbarrier::complete_tx::bytes` forms write remote shared
  memory and complete with a complete-tx on their mbarrier; the `.release` forms write global
  memory with a strong access at their scope and have no completion the thread can observe. A
  `red.async` reduces its destination element with an atomic read-modify-write. An address
  outside the required state space or CTA, a misaligned address or an operand of the wrong size
  produces an undefined-behaviour event.

Defs: asyncStoreTypeOk, asyncReduceOk, asyncStoreLoc, asyncStoreData, asyncStoreTmpl

Source:
- §9.7.10.12 (st.async): "st.async is a non-blocking instruction which initiates an asynchronous
    store operation that stores the value specified by source operand b to the destination memory
    location specified by operand a ."
- §9.7.10.12 (st.async): "st.async is performed in the generic proxy."
- §9.7.10.12 (st.async): "If .ss is not specified, Generic Addressing is used."
- §9.7.10.12 (st.async): "This is a weak store to shared memory, which signals its completion
    through an mbarrier object."
- §9.7.10.12 (st.async): "The shared memory addresses of destination operand a and the mbarrier
    object mbar belong to the same CTA within the same cluster as the executing thread."
- §9.7.10.12 (st.async): "The number of CTAs within the cluster is strictly greater than one;
    %cluster_nctarank > 1 is true."
- §9.7.10.12 (st.async): "If the generic addresses specified do not fall within the address window
    of .shared::cluster state space, the behavior is undefined."
- §9.7.10.12 (st.async): "This is a release store to global memory."
- §9.7.10.12 (st.async): "If the generic address specified does not fall within the address window
    of .global state space, the behavior is undefined."
- §9.7.10.12 (st.async): "For .vec qualifier: .v2 is supported with .b32 , .b64 , .s32 , .s64 , .u32
    , .u64 , .f32 and .f64 types. .v4 qualifier is supported with .b32 , .s32 , .u32 and .f32
    types."
- §9.7.15.7 (red.async): "red.async is a non-blocking instruction which initiates an asynchronous
    reduction operation specified by .op , with the operand b and the value at the destination
    memory location specified by operand a ."
- §9.7.15.7 (red.async): "The complete-tx operation on the mbarrier has .release semantics at
    .cluster scope."
- §9.7.15.7 (red.async): "They belong to the same CTA."
- §9.7.15.7 (red.async): "The CTA to which they belong is different from the CTA of the executing
    thread, but must be within the same cluster."
- §9.7.15.7 (red.async): "When .completion_mechanism is not specified: the completion of the store
    synchronizes with the end of the CTA."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- EXT-ST-ASYNC-CTA

Direction: stricter

Applies: `st.async{.weak}{.shared::cluster}.mbarrier::complete_tx::bytes{.v2, .v4}.type` and
  `st.async.release.{gpu,sys}{.global}.type`; `red.async.relaxed.cluster{.shared::cluster}
  .mbarrier::complete_tx::bytes.op.type` and `red.async.release.{gpu,sys}{.global}.add.type`, each
  with the operations and types of its syntax; none with `.mmio`

Premises: The address and the mbarrier are in the state spaces and CTAs below, the address is
  aligned to the access size and each value operand has the type's size.

Effect: Thread event construction (`Kind.copy`); the write, the reduction, the notification and
  their order are the execution rules of linear operations. The issue event is a linear operation
  (`AsyncCopy.Spec`) with an empty source footprint, the concatenated bytes of the value operands
  as its register source (`data`), the destination of the access size (the type's size times the
  vector length), and the generic proxy. A `red.async` writes its one element as a reduction
  (`WriteMode.reduce`, DEP-REDUCTION-VALUES, MEM-ATOMICITY); an `st.async` writes its destination
  whole. The address is located as a store's (`accessLoc`, THREAD-ADDR) with the instruction's
  state space, `.shared::cluster` or `.global`, or as a generic address without one, and must fall
  in the shared or global window the form requires. The `.mbarrier::complete_tx::bytes` forms: the
  destination and the mbarrier (8-byte aligned) are in one CTA of the executing thread's cluster;
  for `red.async` that CTA is not the executing one, and for `st.async` the cluster has more than
  one CTA (EXT-ST-ASYNC-CTA). The completion is the complete-tx on the mbarrier with the
  destination's byte count (DEP-LINEAR-COPY-EFFECTS). An `st.async` is weak; a `red.async` is a
  relaxed reduction at `.cluster` scope (`scope`). The `.release` forms: the destination is global;
  the access is strong at the instruction's scope (`scope`), and it has no completion mechanism
  (`Completion.unobserved`), so no wait of the model observes it and only the end of the kernel
  orders it before later accesses (CORRECT-COMPLETE). Their release semantics are not represented:
  the operation creates no release pattern of MEM-RELEASE-ACQUIRE, which gives fewer synchronization
  edges than the text and is stricter. The issuer's earlier accesses are ordered before it
  (§8.9.1.1, MEM-MODEL-CAUSALITY).

### EXT-ST-ASYNC-CTA — the destination CTA of st.async

Statement: The destination and the mbarrier of an `st.async` with mbarrier completion lie in one
  CTA, which may be any CTA of the executing thread's cluster, including its own.

Source:
- §9.7.10.12: "The shared memory addresses of destination operand a and the mbarrier object mbar
    belong to the same CTA within the same cluster as the executing thread."

Why it is not spec text: The sentence can be read as requiring the CTA of the executing thread, or
  as requiring one CTA of the executing thread's cluster. The model takes the second reading: the
  destination and the mbarrier share a CTA of the cluster. The requirement "%cluster_nctarank > 1"
  and the use of `st.async` for distributed shared memory support it.

Direction: reading

Effect: Wider than the first reading: a store into another CTA of the cluster is accepted. If the
  first reading holds, such a store is undefined on hardware and the model does not report it.
  Disclosed by every kernel whose statement names `Op.asyncStore`: none.
-/

/-- The types of `st.async` (§9.7.10.12 syntax): with an mbarrier, `.b32`, `.b64`, `.b128`, `.u32`,
`.u64`, `.s32`, `.s64`, `.f32`, `.f64`, `.v2` of the 32- and 64-bit ones and `.v4` of the 32-bit
ones; with `.release`, the scalar 8- to 64-bit integer types, `.f32` and `.f64`. -/
def asyncStoreTypeOk (mbar : Bool) (ty : DType) (vec : Nat) : Bool :=
  let w := ty.width
  let scalar := match ty with
    | .int k w => w == 32 || w == 64 || (mbar && k == .b && w == 128) || (!mbar && w ≤ 16)
    | .float f => f == .f32 || f == .f64
    | _ => false
  scalar && (match vec with
    | 1 => true
    | 2 => mbar && (w == 32 || w == 64)
    | 4 => mbar && w == 32
    | _ => false)

/-- The operations and types of `red.async` (§9.7.15.7 syntax): with an mbarrier, `.inc` and
`.dec` of `.u32`, `.min` and `.max` of `.u32` and `.s32`, `.and`, `.or` and `.xor` of `.b32`, and
`.add` of `.u32`, `.s32` and `.u64`; with `.release`, `.add` of `.u32`, `.s32`, `.u64` and
`.s64`. -/
def asyncReduceOk (mbar : Bool) : AtomOp → DType → Bool
  | .inc, .int k w | .dec, .int k w => mbar && k == .u && w == 32
  | .min, .int k w | .max, .int k w => mbar && (k == .u || k == .s) && w == 32
  | .and, .int k w | .or, .int k w | .xor, .int k w => mbar && k == .b && w == 32
  | .add, .int k w =>
    (k == .u && (w == 32 || w == 64)) || (k == .s && (w == 32 || (!mbar && w == 64)))
  | _, _ => false

/-- The location of an `st.async` or `red.async` address: located as a store's (`accessLoc`) with
the instruction's state space or as a generic address, and required to be shared (`shared`) or
global. -/
def asyncStoreLoc (L : Launch) (g : Nat) (t : TState) (space : Option StateSpace) (shared : Bool)
    (a : Addr) : Exec Loc := do
  let access : MemAccess :=
    { kind := .store, space := space, sem := .weak, elem := .int .b 8, addr := a }
  let loc ← accessLoc L g t access
  unless loc.space = (if shared then .shared else .global) do throw .badValue
  pure loc

/-- The bytes of the value operands of an `st.async` or `red.async` of type `ty`, each of the
type's size, in operand order. -/
def asyncStoreData (L : Launch) (g : Nat) (t : TState) (ty : DType) (srcs : List Opnd) :
    Exec (List Byte) := do
  let vs ← srcs.mapM fun o => do
    let v ← readValue L g t ty.width o
    unless 8 * v.bytes = ty.width do throw .typeMismatch
    pure v
  pure (vs.flatMap Value.toBytes)

/-- The event of `st.async` or `red.async` (THREAD-ASYNC-STORE). -/
def asyncStoreTmpl (L : Launch) (g : Nat) (t : TState) (s : AsyncStore) : Tmpl := ofExec do
  let mbar := s.mbar.isSome
  match s.reduce with
  | none => unless asyncStoreTypeOk mbar s.elem s.vec do throw .noRule
  | some op => unless s.vec = 1 ∧ asyncReduceOk mbar op s.elem do throw .noRule
  unless s.srcs.length = s.vec do throw .typeMismatch
  let size := s.vec * (s.elem.width / 8)
  let d ← asyncStoreLoc L g t s.space mbar s.addr
  unless 0 < size ∧ d.addr % size = 0 do throw .misaligned
  let data ← asyncStoreData L g t s.elem s.srcs
  let writes : AsyncCopy.WriteMode := match s.reduce with
    | none => .whole
    | some op => .reduce ⟨op, s.elem⟩
  let (completion, scope) ← match s.mbar, s.release with
    | some ma, none => do
      let m ← asyncStoreLoc L g t s.space true ma
      unless m.addr % 8 = 0 do throw .misaligned
      unless m.cta = d.cta do throw .badValue
      match s.reduce with
      | none =>
        unless 1 < L.clusterSizeOf (g / L.block) do throw .badValue
        pure (AsyncCopy.Completion.mbarrier m, none)
      | some _ =>
        unless d.cta ≠ g / L.block do throw .badValue
        pure (.mbarrier m, some MbarScope.cluster)
    | none, some sc => pure (.unobserved, some sc)
    | _, _ => throw .noRule
  pure (.copy (AsyncCopy.Spec.mk { loc := d, size := 0 } { loc := d, size := size } completion
    writes (some data) true scope) (next t))

end

end PTX

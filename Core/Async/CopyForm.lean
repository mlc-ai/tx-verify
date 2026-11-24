-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Mem

@[expose] public section

/-!
# Instruction forms of linear copies

The decoded qualifiers and operands of `cp.async.bulk` and `cp.async`. The rules are THREAD-TMA
(`Core/Async/Tma.lean`) and THREAD-CP-ASYNC (`Core/Async/CpAsync.lean`).
-/

namespace PTX

/-! ## PROG-ISA-COPY — the decoded forms of linear copies
Statement: A `cp.async.bulk` or `cp.reduce.async.bulk` instruction decodes to its direction, its
  addresses, its size, the mbarrier of its mbarrier completion (none for `.bulk_group`), its
  multicast mask, its `.ignore_oob` operands, its cache policy, its `.cp_mask` byte mask, and for a
  reduction its operation, type and scope. A `cp.async` decodes to its addresses, its `cp-size`
  and its source operand form. An `st.async` or `red.async` decodes to its operation, type, state
  space, address, value operands, and its mbarrier or release scope.

Defs: BulkDir, BulkCopy, AsyncStore, CpAsyncSource

Source:
- §9.7.10.28.4.1 (cp.async.bulk syntax and completion mechanisms)
- §9.7.10.28.4.2 (cp.reduce.async.bulk syntax)
- §9.7.10.28.3.1 (cp.async syntax)
- §9.7.10.12 (st.async syntax)
- §9.7.15.7 (red.async syntax)

Direction: representation

Applies: The `cp.async.bulk`, `cp.reduce.async.bulk`, `cp.async`, `st.async` and `red.async` forms
  PROG-ISA-SYNC-FORMS lists

Premises: None.

Effect: The operands of `Op.cpBulk`, `Op.cpAsync` and `Op.asyncStore`; the rules are THREAD-TMA,
  THREAD-CP-ASYNC and THREAD-ASYNC-STORE.
-/

/-- The direction of a `cp.async.bulk` copy (§9.7.10.28.4.1): `.shared::cta.global`,
`.shared::cluster.global`, `.shared::cluster.shared::cta` or `.global.shared::cta`. -/
inductive BulkDir where
  | globalToCta | globalToCluster | ctaToCluster | ctaToGlobal
  deriving DecidableEq, Repr

/-- A decoded `cp.async.bulk{.sem.scope}.dst.src.completion{...}` (§9.7.10.28.4.1): the direction,
the destination and source addresses (register plus offset), the size operand, the mbarrier of an
`.mbarrier::complete_tx::bytes` copy (`none` for `.bulk_group`), the `.multicast::cluster` mask with
its width in bits, the `ignoreBytesLeft` and `ignoreBytesRight` operands of `.ignore_oob`, and the
64-bit operand of `.L2::cache_hint`. The `.weak` and `.relaxed` semantics are not recorded: the
rule treats both as weak (THREAD-TMA). -/
structure BulkCopy where
  dir : BulkDir
  dst : Nat
  dstOff : Int
  src : Nat
  srcOff : Int
  size : Opnd
  mbar : Option (Nat × Int)
  multicast : Option (Nat × Opnd) := none
  ignoreOob : Option (Opnd × Opnd) := none
  cachePolicy : Option Opnd := none
  /-- The 16-bit `byteMask` operand of `.cp_mask`. -/
  mask : Option Opnd := none
  /-- `cp.reduce.async.bulk`: the reduction operation and the element type. -/
  reduce : Option (AtomOp × DType) := none
  /-- The `.scope` of `cp.reduce.async.bulk.relaxed.scope`; `none` when `.sem.scope` is absent
  (`.relaxed.sys`). -/
  scope : Option MbarScope := none
  deriving Repr

/-- A decoded `st.async` or `red.async` (§9.7.10.12, §9.7.15.7): the reduction operation of
`red.async` (`none` for `st.async`), the type, the vector length, the state space written (`none`
for a generic address), the address, the value operands, and either the mbarrier of the
`.mbarrier::complete_tx::bytes` form or the scope of the `.release` form. -/
structure AsyncStore where
  reduce : Option AtomOp
  elem : DType
  vec : Nat := 1
  space : Option StateSpace
  addr : Addr
  srcs : List Opnd
  mbar : Option Addr
  release : Option MbarScope
  deriving Repr

/-- The source operand of a `cp.async` (§9.7.10.28.3.1): the whole `cp-size` bytes, the first
`src-size` bytes (a 32-bit operand), or the `ignore-src` predicate. -/
inductive CpAsyncSource where
  | full
  | size (n : Opnd)
  | ignore (p : Opnd)
  deriving Repr

end PTX

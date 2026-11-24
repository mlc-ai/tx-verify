-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Instr

@[expose] public section

/-!
# Kept instruction forms

The construction of the barrier, mbarrier, fence, asynchronous copy, `tcgen05`, cluster
launch control and `setmaxnreg` constructors of `Op` from a recognized instruction (`Isa.Raw`).
A recognized instruction of these families with a qualifier combination outside the forms listed
below decodes to `Op.unmodeled`.
-/

namespace PTX

/-! ## PROG-ISA-SYNC-FORMS — synchronization, copy and tcgen05 forms
Statement: A recognized instruction of the `barrier`, `mbarrier`, `fence`, `async`, `tc`, `clc`
  and `misc` families decodes to its own constructor of `Op` when its qualifiers form one of
  the forms listed below, and to `Op.unmodeled` otherwise. The operands of a listed form are
  resolved at the widths of their types, and an operand that cannot be resolved is an error.

Defs: *

Source:
- §9.7.15.1 (bar, barrier)
- §9.7.15.3 (barrier.cluster)
- §9.7.15.4 (fence)
- §9.7.15.16 (mbarrier)
- §9.7.10.16 (prefetch)
- §9.7.10.28 (cp.async, cp.async.bulk, cp.async.bulk.prefetch, cp.async.bulk.tensor,
    cp.reduce.async.bulk.tensor, cp.async.bulk.prefetch.tensor, commit_group, wait_group)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.15.18 and §9.7.15.19 (clusterlaunchcontrol)
- §9.7.21.5 (setmaxnreg)
- §9.7.18 (tcgen05)

Direction: representation

Effect: The listed forms are as follows:
  - `bar.sync` and `bar.arrive` without `.cta` (aligned), `barrier.sync{.aligned}` and
    `barrier.arrive{.aligned}` without `.cta`, and every `barrier.cluster.arrive` and
    `barrier.cluster.wait` form.
  - `mbarrier.init` and `mbarrier.inval` with `.shared` or `.shared::cta` written and no layout;
    `mbarrier.arrive{.expect_tx}{.sem.scope}.space.b64` with `.space` written and `.sem` and
    `.scope` both written or both omitted, where a destination register `state` requires a CTA
    address; `mbarrier.try_wait.parity{.sem.scope}.space.b64` likewise, without `.phase_type`.
  - `fence.mbarrier_init.release.cluster`, and every other `fence` and `membar` entry
    (PROG-ISA-FENCE).
  - `cp.async.bulk` in each direction of the table, `.weak` or `.relaxed`, with `.ignore_oob`,
    `.multicast::cluster{::16b, ::32b}`, `.L2::cache_hint` and `.cp_mask`, and with
    `.mbarrier::report::disabled` as the only report mechanism; `cp.reduce.async.bulk` in both
    directions with its operation, type and optional `.relaxed.scope`; `cp.async.{ca,cg}` with every
    operand form; `cp.async.commit_group`, `cp.async.wait_group` with a non-negative integer
    constant, `cp.async.wait_all`; `cp.async.mbarrier.arrive{.noinc}` with `.shared` or
    `.shared::cta` written or a generic address; `st.async` and `red.async` in every form without
    `.mmio`; `cp.async.bulk.prefetch.L2.global` with `.L2::cache_hint` or `.L2::evict_last`; the
    tensor loads to `.shared::cta` and `.shared::cluster` (`.multicast::cluster` and its `::16b`
    form take a 16-bit mask, `::32b` a 32-bit mask), with `.mbarrier::report::disabled` as the only
    report mechanism, the tensor stores, the tensor reductions and the tensor prefetch (also with
    `.L2::evict_last`), each with `.tile` or the default mode, or the four-row mode on a `.2d` map;
    `cp.async.bulk.commit_group`; `cp.async.bulk.wait_group{.read, .sync_restrict::proxy::async}`
    with a non-negative integer constant; `prefetch{.param}.tensormap` of `[a]`.
  - `clusterlaunchcontrol.try_cancel` with `.shared::cta` written, `query_cancel.is_canceled` and
    `query_cancel.get_first_ctaid::{x,y,z}`.
  - `setmaxnreg.{inc,dec}.sync.aligned.u32` with a count from 24 to 256 that is a multiple of 8.
    `createpolicy`, `nanosleep` and `pmevent` decode to `Op.misc` (PROG-ISA-MISC).
  - `tcgen05.alloc` with `.shared::cta` written, `dealloc`, `relinquish_alloc_permit`, both fences,
    `wait::ld`, `wait::st`, `commit` with `.shared::cluster` written (multicast with a 16-bit mask
    only), `ld` and `st` without packing, `ld.red` (PROG-ISA-TC-LD-RED), and `cp` without
    decompression in the shapes of PROG-ISA-TC-CP. Every `tcgen05.mma` entry decodes to `Op.tcMma`
    (PROG-ISA-TC-MMA).
-/

namespace Decode
open PTX.Syntax

/-- The width of the `ctaMask` operand of a `.multicast::cluster` qualifier: 32 bits for `::32b`,
16 bits otherwise; `none` without the qualifier. -/
def multicastWidth? : Option Isa.Token → Option Nat
  | some .multicast_cluster_32b => some 32
  | some _ => some 16
  | none => none

/-- The rank of a tensor instruction's `.<n>d` qualifier, 1 to 5. -/
def tensorRank? : Option Isa.Token → Option Nat
  | some .x1d => some 1 | some .x2d => some 2 | some .x3d => some 3
  | some .x4d => some 4 | some .x5d => some 5
  | _ => none

/-- The load mode of a tensor instruction: `.tile` or the default, or the four-row mode
(`.tile::gather4` of a load or prefetch, `.tile::scatter4` of a store). -/
def loadMode? : Option Isa.Token → Option TensorMode
  | none | some .tile => some .tile
  | some .tile_gather4 | some .tile_scatter4 => some .fourRows
  | some _ => none

/-- The rank and load mode of a tensor instruction; the four-row mode needs a `.2d` map. -/
def tensorShape? (r : Isa.Raw) : Option (Nat × TensorMode) :=
  match tensorRank? (r.get .dim), loadMode? (r.get .load_mode) with
  | some rank, some mode =>
    if mode = .fourRows ∧ rank ≠ 2 then none else some (rank, mode)
  | _, _ => none

/-- The coordinates must number the mode's count for a `.<rank>d` map. -/
def tensorCoords (rank : Nat) (mode : TensorMode) (cs : List Operand) : M Unit :=
  unless cs.length = mode.coordinates (rank - 1) do
    throw s!"tensor instruction mode and {cs.length} coordinates for a {rank}d map"

/-- The 64-bit `cache_policy` operand of `.L2::cache_hint`, when the qualifier is written. -/
def cachePolicy (env : Env) (r : Isa.Raw) : M (Option Opnd) := do
  if flag r .cache then return some (← src env 64 (← arg r "cache_policy")) else return none

/-- The `.shape1` qualifier of `tcgen05.ld` / `tcgen05.st` (§9.7.18.8.3). -/
def tcShape1? : Option Isa.Token → Option TcShape
  | some .x32x32b => some .s32x32b
  | some .x16x64b => some .s16x64b
  | some .x16x128b => some .s16x128b
  | some .x16x256b => some .s16x256b
  | _ => none

/-- The `.num` qualifier `x<num>` of `tcgen05.ld` / `tcgen05.st`. -/
def tcNum? : Option Isa.Token → Option Nat
  | some .x1 => some 1 | some .x2 => some 2 | some .x4 => some 4 | some .x8 => some 8
  | some .x16 => some 16 | some .x32 => some 32 | some .x64 => some 64 | some .x128 => some 128
  | _ => none

/-- The vector of `tcgen05.ld` / `tcgen05.st` has `num` repetitions of the shape's registers
(Tables 59 and 61). -/
def tcVector (shape : TcShape) (num n : Nat) : M Unit := do
  unless n = shape.regs * num ∧ shape.countOk n do throw "tcgen05.ld/st vector length"

/-- The `immHalfSplitoff` of `.16x32bx2`: an integer constant, non-negative and below `2 ^ 32`. -/
def halfSplit : Operand → M Nat
  | .literal t => do
    let .imm v ← literal t | throw s!"tcgen05 immHalfSplitoff {t}"
    unless 0 ≤ v ∧ v < 2 ^ 32 do throw s!"tcgen05 immHalfSplitoff {t}"
    pure v.toNat
  | _ => throw "tcgen05 immHalfSplitoff"

/-- The access shape of `tcgen05.ld` / `tcgen05.st`: `.16x32bx2` with its `immHalfSplitoff`
operand, or a `.shape1` qualifier. -/
def tcShape? (r : Isa.Raw) : Option (M TcShape) :=
  match r.entry with
  | .tcgen05_ld_split | .tcgen05_st_split | .tcgen05_ld_red_split =>
    some do return .s16x32bx2 (← halfSplit (← arg r "imm_half_splitoff"))
  | _ => pure <$> tcShape1? (r.get .shape)

/-- The shape with `.pack::16b` / `.unpack::16b` when `packed`: `packed16` of a single-access
shape; `none` (not represented) for `.16x32bx2`, whose half-split offset the text does not place
in packed or physical columns (THREAD-TC-PACK16). -/
def tcPack16? (packed : Bool) (shape : TcShape) : Option TcShape :=
  if !packed then some shape
  else if shape.singleAccess then some (.packed16 shape) else none

/-- The Tensor Memory address of `tcgen05.ld` / `tcgen05.st`: `[taddr]`, or `[taddr+0]`, the
same address. Another offset is not decoded. -/
def tmemDataAddress (env : Env) (o : Operand) : M Nat := do
  let (r, off) ← address env 32 o
  unless off = 0 do throw "unsupported tcgen05.ld/st address offset"
  pure r

/-- The `.sem.scope` qualifier pair of an mbarrier operation, where `strong` is its release or
acquire semantics: both written, or both omitted for the PTX defaults (`strong`, `.cta`). -/
def mbarSem? (strong : Isa.Token) (r : Isa.Raw) : Option (Bool × MbarScope) :=
  match r.get .sem, r.get .scope with
  | none, none => some (true, .cta)
  | some s, some .cta => if s == strong || s == .relaxed then some (s == strong, .cta) else none
  | some s, some .cluster =>
    if s == strong || s == .relaxed then some (s == strong, .cluster) else none
  | _, _ => none

/-- The `barrier` family: `bar` and `barrier` without `.cta`, and `barrier.cluster`. -/
def barrierOp (env : Env) (r : Isa.Raw) : M Op := do
  let s32 (n : String) : M Opnd := do src env 32 (← arg r n)
  let aligned := flag r .aligned
  match r.entry with
  | .bar_sync | .barrier_sync =>
    if flag r .cta then return .unmodeled r
    let aligned := match r.entry with | .bar_sync => true | _ => aligned
    return .barSync (← s32 "a") aligned
  | .bar_sync_count | .barrier_sync_count =>
    if flag r .cta then return .unmodeled r
    let aligned := match r.entry with | .bar_sync_count => true | _ => aligned
    return .barSyncN (← s32 "a") (← s32 "b") aligned
  | .bar_arrive | .barrier_arrive =>
    if flag r .cta then return .unmodeled r
    let aligned := match r.entry with | .bar_arrive => true | _ => aligned
    return .barArrive (← s32 "a") (← s32 "b") aligned
  | .barrier_cluster_arrive => return .cluster (.arrive (r.get .sem != some .relaxed) aligned)
  | .barrier_cluster_wait => return .cluster (.wait aligned)
  | _ => return .unmodeled r

/-- The `mbarrier` family: `init`, `inval`, `arrive{.expect_tx}` and `try_wait.parity`. -/
def mbarrierOp (env : Env) (r : Isa.Raw) : M Op := do
  let space := r.get .space
  let cta := space == some .shared || space == some .shared_cta
  match r.entry with
  | .mbarrier_init =>
    if flag r .layout || !cta then return .unmodeled r
    let (base, off) ← address env 32 (← arg r "addr")
    return .mbarInit base off (← src env 32 (← arg r "count"))
  | .mbarrier_inval =>
    if !cta then return .unmodeled r
    let (base, off) ← address env 32 (← arg r "addr")
    return .mbarInval base off
  | .mbarrier_arrive_nocount | .mbarrier_arrive | .mbarrier_arrive_expect_tx
  | .mbarrier_arrive_state | .mbarrier_arrive_count_state | .mbarrier_arrive_expect_tx_state =>
    let some (release, scope) := mbarSem? .release r | return .unmodeled r
    let cluster := space == some .shared_cluster
    if !cta && !cluster then return .unmodeled r
    let st :: addr :: extra := r.opnds.map (·.op) | throw "mbarrier.arrive operands"
    let state ← match st with
      | .sink => pure none
      | d =>
        if cluster then throw "mbarrier.arrive.shared::cluster needs the sink _"
        else some <$> reg env 64 d
    let (base, off) ← address env 32 addr
    let (tx, count) ← match flag r .expect_tx, extra with
      | true, [tx] => do pure (← src env 32 tx, Opnd.imm 1)
      | false, [] => pure (Opnd.imm 0, Opnd.imm 1)
      | false, [c] => do pure (Opnd.imm 0, ← src env 32 c)
      | _, _ => throw "unsupported mbarrier.arrive operands"
    return .mbarArrive base off tx count cluster release scope state
  -- The optional suspend-time hint only bounds how long a failing wait blocks; a wait may
  -- fail regardless, so the hint is checked and dropped.
  | .mbarrier_try_wait_parity | .mbarrier_try_wait_parity_no_hint =>
    let some (acquire, scope) := mbarSem? .acquire r | return .unmodeled r
    if flag r .phase_type || !cta then return .unmodeled r
    if let some h := opnd? r "time_hint" then discard <| src env 32 h.op
    let (base, off) ← address env 32 (← arg r "addr")
    return .mbarWait (← reg env 1 (← arg r "wait_complete")) base off
      (← src env 32 (← arg r "phase")) acquire scope
  | _ => return .unmodeled r

/-- The `fence` family: the mbarrier-initialization fence, and every other fence and `membar`
(PROG-ISA-FENCE). -/
def fenceOp (env : Env) (r : Isa.Raw) : M Op := do
  match r.entry with
  | .fence_mbarrier_init => pure .fenceMbarInit
  | _ => match ← FenceInstr.ofRaw env r with
    | some f => pure (.fence f)
    | none => pure (.unmodeled r)

/-- The `async` family: the bulk copies, `cp.async` with its group commit and wait and
`cp.async.mbarrier.arrive`, the linear prefetch, the tensor loads, stores, reductions and
prefetch, bulk-group commit and wait, and the tensormap prefetch. -/
def asyncOp (env : Env) (r : Isa.Raw) : M Op := do
  match r.entry with
  | .cp_async_bulk_g2s_cta | .cp_async_bulk_g2s_cluster | .cp_async_bulk_g2s_cluster_multicast16
  | .cp_async_bulk_g2s_cluster_multicast32 | .cp_async_bulk_s2c | .cp_async_bulk_s2g
  | .cp_async_bulk_g2s_cta_report | .cp_async_bulk_g2s_cluster_report
  | .cp_reduce_async_bulk_s2c | .cp_reduce_async_bulk_s2g | .cp_reduce_async_bulk_s2g_f32_noftz =>
    if flag r .report && r.get .report != some .mbarrier_report_disabled then return .unmodeled r
    let (dir, width?) : BulkDir × Option Nat := match r.entry with
      | .cp_async_bulk_g2s_cta | .cp_async_bulk_g2s_cta_report => (.globalToCta, none)
      | .cp_async_bulk_g2s_cluster =>
        (.globalToCluster, if flag r .multicast then some 16 else none)
      | .cp_async_bulk_g2s_cluster_report => (.globalToCluster, multicastWidth? (r.get .multicast))
      | .cp_async_bulk_g2s_cluster_multicast16 => (.globalToCluster, some 16)
      | .cp_async_bulk_g2s_cluster_multicast32 => (.globalToCluster, some 32)
      | .cp_async_bulk_s2c | .cp_reduce_async_bulk_s2c => (.ctaToCluster, none)
      | _ => (.ctaToGlobal, none)
    let reduce? : Bool := match r.entry with
      | .cp_reduce_async_bulk_s2c | .cp_reduce_async_bulk_s2g
      | .cp_reduce_async_bulk_s2g_f32_noftz => true
      | _ => false
    let reduce ← if reduce? then do
        pure (some (← MemAccess.atomOp? (r.get .redop), ← dtype (r.get .type)))
      else pure none
    let scope ← if reduce? then MemAccess.scope? (r.get .scope) else pure none
    let mask ← if flag r .cp_mask then do pure (some (← src env 16 (← arg r "byte_mask")))
      else pure none
    let global := dir == .globalToCta || dir == .globalToCluster
    let (db, doff) ← address env (if dir == .ctaToGlobal then 64 else 32) (← arg r "dst_mem")
    let (sb, soff) ← address env (if global then 64 else 32) (← arg r "src_mem")
    let size ← src env 32 (← arg r "size")
    let mbar ← if dir == .ctaToGlobal then pure none
      else do pure (some (← address env 32 (← arg r "mbar")))
    let multicast ← match width? with
      | none => pure none
      | some w => do pure (some (w, ← src env w (← arg r "cta_mask")))
    let ignoreOob ← if flag r .ignore_oob then do
        pure (some (← src env 32 (← arg r "ignore_bytes_left"),
          ← src env 32 (← arg r "ignore_bytes_right")))
      else pure none
    let policy ← cachePolicy env r
    return .cpBulk (BulkCopy.mk dir db doff sb soff size mbar multicast ignoreOob policy mask reduce
      scope)
  | .cp_async_ca | .cp_async_ca_src_size | .cp_async_ca_ignore_src | .cp_async_cg
  | .cp_async_cg_src_size | .cp_async_cg_ignore_src =>
    let .literal n ← arg r "cp_size" | throw "cp.async needs an integer cp-size"
    let .imm v ← literal n | throw "cp.async needs an integer cp-size"
    unless v = 4 ∨ v = 8 ∨ v = 16 do throw "cp.async cp-size must be 4, 8 or 16"
    let (db, doff) ← address env 32 (← arg r "dst_mem")
    let (sb, soff) ← address env 64 (← arg r "src_mem")
    let source ← match r.entry with
      | .cp_async_ca_src_size | .cp_async_cg_src_size => do
        pure (CpAsyncSource.size (← src env 32 (← arg r "src_size")))
      | .cp_async_ca_ignore_src | .cp_async_cg_ignore_src => do
        pure (CpAsyncSource.ignore (← src env 1 (← arg r "ignore_src")))
      | _ => pure .full
    return .cpAsync db doff sb soff v.toNat source (← cachePolicy env r)
  | .cp_async_commit_group => return .cpAsyncCommit
  | .cp_async_wait_group =>
    let .literal n ← arg r "group" | throw "cp.async wait needs an integer constant"
    let .imm v ← literal n | throw "cp.async wait needs an integer constant"
    unless 0 ≤ v do throw "negative cp.async wait count"
    return .cpAsyncWait false v.toNat
  | .cp_async_wait_all => return .cpAsyncWait true 0
  | .cp_async_mbarrier_arrive =>
    let space := r.get .space
    if space == none then
      let (base, off) ← address env 64 (← arg r "addr")
      return .cpAsyncArrive (flag r .noinc) base off true
    unless space == some .shared || space == some .shared_cta do return .unmodeled r
    let (base, off) ← address env 32 (← arg r "addr")
    return .cpAsyncArrive (flag r .noinc) base off
  | .cp_async_bulk_prefetch | .cp_async_bulk_prefetch_evict_last =>
    let (sb, soff) ← address env 64 (← arg r "src_mem")
    return .prefetchBulk sb soff (← src env 32 (← arg r "size")) (← cachePolicy env r)
  | .cp_async_bulk_tensor_g2s_cta | .cp_async_bulk_tensor_g2s_cluster
  | .cp_async_bulk_tensor_g2s_cluster_multicast16
  | .cp_async_bulk_tensor_g2s_cluster_multicast32
  | .cp_async_bulk_tensor_g2s_cta_report | .cp_async_bulk_tensor_g2s_cluster_report =>
    if flag r .report && r.get .report != some .mbarrier_report_disabled then return .unmodeled r
    let some (rank, mode) := tensorShape? r | return .unmodeled r
    let (cluster, width) := match r.entry with
      | .cp_async_bulk_tensor_g2s_cta | .cp_async_bulk_tensor_g2s_cta_report => (false, none)
      | .cp_async_bulk_tensor_g2s_cluster => (true, if flag r .multicast then some 16 else none)
      | .cp_async_bulk_tensor_g2s_cluster_report => (true, multicastWidth? (r.get .multicast))
      | .cp_async_bulk_tensor_g2s_cluster_multicast16 => (true, some 16)
      | _ => (true, some 32)
    let cs ← args r "coords"
    tensorCoords rank mode cs
    let policy ← cachePolicy env r
    let multicast ← match width with
      | none => pure none
      | some w => do pure (some (w, ← src env w (← arg r "cta_mask")))
    let (db, doff) ← address env 32 (← arg r "dst_mem")
    let (mb, moff) ← address env 32 (← arg r "mbar")
    return .cpTensor cluster (r.get .cta_group == some .cta_group_2) db doff
      (← src env 64 (← arg r "tmap")) (← srcs env 32 cs) mb moff multicast mode policy
  | .cp_async_bulk_tensor_s2g | .cp_reduce_async_bulk_tensor =>
    let some (rank, mode) := tensorShape? r | return .unmodeled r
    let reduce? : Option (Option AtomOp) := match r.entry, r.get .redop with
      | .cp_async_bulk_tensor_s2g, _ => some none
      | _, some .add => some (some .add)
      | _, some .min => some (some .min)
      | _, some .max => some (some .max)
      | _, some .inc => some (some .inc)
      | _, some .dec => some (some .dec)
      | _, some .and => some (some .and)
      | _, some .or => some (some .or)
      | _, some .xor => some (some .xor)
      | _, _ => none
    let some reduce := reduce? | return .unmodeled r
    let cs ← args r "coords"
    tensorCoords rank mode cs
    let (sb, soff) ← address env 32 (← arg r "src_mem")
    let policy ← cachePolicy env r
    return .cpTensorStore (← src env 64 (← arg r "tmap")) (← srcs env 32 cs) sb soff policy mode
      reduce
  | .cp_async_bulk_tensor_prefetch | .cp_async_bulk_tensor_prefetch_evict_last =>
    let some (rank, mode) := tensorShape? r | return .unmodeled r
    let cs ← args r "coords"
    tensorCoords rank mode cs
    let policy ← cachePolicy env r
    return .prefetchTensor (← src env 64 (← arg r "tmap")) (← srcs env 32 cs) mode policy
  | .cp_async_bulk_commit_group => return .bulkCommit
  | .cp_async_bulk_wait_group =>
    let mode? : Option BulkGroup.WaitMode := match r.get .read with
      | none => some .full
      | some .read => some .read
      | some .sync_restrict_proxy_async => some .asyncProxy
      | some _ => none
    let some mode := mode? | return .unmodeled r
    let .literal n ← arg r "group" | throw "bulk wait needs an integer constant"
    let .imm v ← literal n | throw "bulk wait needs an integer constant"
    unless 0 ≤ v do throw "negative bulk wait count"
    return .bulkWait mode v.toNat
  | .prefetch_tensormap =>
    if flag r .level || flag r .evict then return .unmodeled r
    let generic? : Option Bool := match r.get .space with
      | none => some true
      | some .param => some false
      | some _ => none
    let some generic := generic? | return .unmodeled r
    let .address [a] ← arg r "addr" | throw "unsupported tensormap prefetch address"
    let w ← match a with
      | .register x => regWidth env.classes x
      | _ => pure 64
    unless w = 32 ∨ w = 64 do throw "prefetch address must be 32 or 64 bits"
    return .prefetchTensorMap generic w (← src env w a)
  | .st_async | .st_async_vec | .st_async_release | .red_async | .red_async_release =>
    if flag r .mmio then return .unmodeled r
    let space? : Option (Option StateSpace) := match r.get .space with
      | none => some none
      | some t => (MemAccess.space? t).map some
    let some space := space? | return .unmodeled r
    let reduce ← match r.entry with
      | .red_async | .red_async_release => do pure (some (← MemAccess.atomOp? (r.get .op)))
      | _ => pure none
    let some value := opnd? r (if reduce.isSome then "value" else "b")
      | throw "st.async or red.async value operand"
    let release ← match r.entry with
      | .st_async_release | .red_async_release => MemAccess.scope? (r.get .scope)
      | _ => pure none
    let mbar ← match r.entry with
      | .st_async_release | .red_async_release => pure none
      | _ => do pure (some (← MemAccess.addrOf env (← arg r "mbar")))
    let elem ← dtype (r.get .type)
    let vec := match r.get .vec with | some .v2 => 2 | some .v4 => 4 | _ => 1
    let addr ← MemAccess.addrOf env (← arg r "addr")
    let srcs ← rsrcs env value
    return .asyncStore (AsyncStore.mk reduce elem vec space addr srcs mbar release)
  | _ => return .unmodeled r

/-- The `tc` family: the listed `tcgen05` forms of PROG-ISA-SYNC-FORMS, and every `tcgen05.mma`
entry (PROG-ISA-TC-MMA). -/
def tcOp (env : Env) (r : Isa.Raw) : M Op := do
  if r.get .action == some .mma then
    return .tcMma (← TcMmaInstr.ofRaw env r)
  let group? := ctaGroup? (r.get .cta_group)
  match r.entry with
  | .tcgen05_alloc =>
    let some group := group? | return .unmodeled r
    if r.get .space != some .shared_cta then return .unmodeled r
    let (base, off) ← address env 32 (← arg r "dst")
    return .tcAlloc group base off (← src env 32 (← arg r "ncols"))
  | .tcgen05_dealloc =>
    let some group := group? | return .unmodeled r
    return .tcDealloc group (← src env 32 (← arg r "taddr")) (← src env 32 (← arg r "ncols"))
  | .tcgen05_relinquish_alloc_permit =>
    let some group := group? | return .unmodeled r
    return .tcRelinquish group
  | .tcgen05_fence =>
    match r.get .action with
    | some .fence_before_thread_sync => return .tcFenceBefore
    | some .fence_after_thread_sync => return .tcFenceAfter
    | _ => return .unmodeled r
  | .tcgen05_wait =>
    match r.get .action with
    | some .wait_ld => return .tcWaitLd
    | some .wait_st => return .tcWaitSt
    | _ => return .unmodeled r
  | .tcgen05_commit | .tcgen05_commit_multicast | .tcgen05_commit_multicast_width =>
    let some group := group? | return .unmodeled r
    if r.get .space != some .shared_cluster then return .unmodeled r
    let mask? : Option (Option String) := match r.entry, r.get .multicast with
      | .tcgen05_commit, _ => some none
      | .tcgen05_commit_multicast, _ => some (some "mask")
      | _, some .multicast_cluster_16b => some (some "cta_mask")
      | _, _ => none
    let some mask := mask? | return .unmodeled r
    let (base, off) ← address env 32 (← arg r "mbar")
    match mask with
    | none => return .tcCommit group base off none
    | some n => return .tcCommit group base off (some (← src env 16 (← arg r n)))
  | .tcgen05_ld | .tcgen05_ld_split =>
    let some num := tcNum? (r.get .num) | return .unmodeled r
    let .vector ds ← arg r "r" | throw "tcgen05.ld destination vector"
    let some shape := tcShape? r | return .unmodeled r
    let shape ← shape
    unless shape.regs * num ≤ 128 do return .unmodeled r
    tcVector shape num ds.length
    let some shape := tcPack16? (flag r .pack) shape | return .unmodeled r
    return .tcLd (← dstRegs env 32 ds) (← tmemDataAddress env (← arg r "taddr")) shape
  | .tcgen05_ld_red | .tcgen05_ld_red_split =>
    let some num := tcNum? (r.get .num) | return .unmodeled r
    let .vector ds ← arg r "r" | throw "tcgen05.ld destination vector"
    let some shape := tcShape? r | return .unmodeled r
    let shape ← shape
    unless 2 ≤ num do throw "tcgen05.ld.red .num below .x2"
    tcVector shape num ds.length
    let red ← TcLdRed.ofRaw env r
    let ds ← dstRegs env 32 ds
    if ds.contains red.dst then throw "tcgen05.ld.red redval is a loaded register"
    return .tcLd ds (← tmemDataAddress env (← arg r "taddr")) shape (some red)
  | .tcgen05_st | .tcgen05_st_split =>
    let some num := tcNum? (r.get .num) | return .unmodeled r
    let .vector ss ← arg r "r" | throw "tcgen05.st source vector"
    let some shape := tcShape? r | return .unmodeled r
    let shape ← shape
    unless shape.regs * num ≤ 128 do return .unmodeled r
    tcVector shape num ss.length
    let some shape := tcPack16? (flag r .unpack) shape | return .unmodeled r
    return .tcSt (← tmemDataAddress env (← arg r "taddr")) (← srcs env 32 ss) shape
  | .tcgen05_cp =>
    let some group := group? | return .unmodeled r
    let shape ← tcCpShape? (r.get .shape) (r.get .multicast)
    let fmt ← tcCpFmt? (r.get .dst_fmt) (r.get .src_fmt)
    return .tcCp group shape (← tmemDst env (← arg r "taddr")) (← src env 64 (← arg r "s_desc"))
      fmt
  | .tcgen05_shift =>
    let some group := group? | return .unmodeled r
    return .tcShift group (← tmemDst env (← arg r "taddr"))
  | _ => return .unmodeled r

/-- The `clc` family: `try_cancel` to `.shared::cta`, and the scalar response queries. -/
def clcOp (env : Env) (r : Isa.Raw) : M Op := do
  match r.entry with
  | .clusterlaunchcontrol_try_cancel =>
    if r.get .space != some .shared_cta then return .unmodeled r
    let (d, off) ← address env 32 (← arg r "addr")
    let (m, moff) ← address env 32 (← arg r "mbar")
    return .clcTryCancel (flag r .multicast) d off m moff
  | .clusterlaunchcontrol_query_cancel_is_canceled =>
    return .clcQuery .isCanceled (← reg env 1 (← arg r "p")) (← src env 128 (← arg r "response"))
  | .clusterlaunchcontrol_query_cancel_get_first_ctaid =>
    let dim? : Option ClcDim := match r.get .query with
      | some .get_first_ctaid_x => some .x
      | some .get_first_ctaid_y => some .y
      | some .get_first_ctaid_z => some .z
      | _ => none
    let some dim := dim? | return .unmodeled r
    return .clcQuery (.first dim) (← reg env 32 (← arg r "d"))
      (← src env 128 (← arg r "response"))
  | _ => return .unmodeled r

/-- The `misc` family: `setmaxnreg` with its count, and `createpolicy`, `nanosleep` and `pmevent`
(PROG-ISA-MISC). -/
def miscOp (env : Env) (r : Isa.Raw) : M Op := do
  match r.entry with
  | .createpolicy_range | .createpolicy_fractional | .createpolicy_fraction | .createpolicy_cvt
  | .nanosleep | .pmevent | .griddepcontrol => return .misc (← MiscInstr.ofRaw env r)
  | .setmaxnreg =>
    let increase? : Option Bool := match r.get .action with
      | some .inc => some true
      | some .dec => some false
      | _ => none
    let some increase := increase? | return .unmodeled r
    let .literal v ← arg r "nreg" | throw "setmaxnreg immediate"
    let some n := natLit? v.toList | throw "setmaxnreg immediate"
    unless 24 ≤ n ∧ n ≤ 256 ∧ n % 8 = 0 do throw "setmaxnreg count"
    return .setMaxReg increase n
  | _ => return .unmodeled r

/-- The `Op` of a recognized instruction of the `barrier`, `mbarrier`, `fence`, `async`, `tc`,
`clc` or `misc` family (PROG-ISA-SYNC-FORMS): the instruction's own constructor for a listed
form, `Op.unmodeled` for another qualifier combination, and an error for an operand that cannot be
resolved. -/
def keptOp (env : Env) (r : Isa.Raw) : M Op :=
  match r.entry.family with
  | .barrier => barrierOp env r
  | .mbarrier => mbarrierOp env r
  | .fence => fenceOp env r
  | .async => asyncOp env r
  | .tc => tcOp env r
  | .clc => clcOp env r
  | .misc => miscOp env r
  | _ => pure (.unmodeled r)

end Decode

end PTX

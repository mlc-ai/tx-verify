-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Data.Sites

@[expose] public section

/-!
# Shared-memory synchronization objects of the FlashMLA sparse decode head64 kernel

`deepseek-ai/FlashMLA` commit `395cb3afbb331fef7b1b21e9340861b9436b42d8`,
`csrc/cuda_kernels/sm100/decode/sparse/head64/kernel.cuh` and `config.h`, the
`v41_h64_no_split` instance (`Config{ModelType::V41, ModelType::V41, false}`). This module
records the two kinds of CTA-wide synchronization object the kernel uses, for the protocol layer:

- the 23 `mbarrier` objects of `SharedMemoryPlan` (`config.h:166-171`), initialized by the
  prologue block `Sites.mbarInits` (PTX lines 104-239), with their byte offsets from
  `wksp_buf` and their expected arrival counts;
- the five `NamedBarriers` of `config.h:22-28`, with the source id, the PTX id the CUTLASS
  `NamedBarrier` wrapper encodes, and the count each is used with, plus the 16 CTA-barrier
  sites `Sites.bars` and the id/count each site resolves to.

Every value below is proved against the decoded program: `Decoded.kernel.code` is scanned for
the instruction that writes the register an operand names, and the theorem pins the written
constant. Two conventions matter for reading the decoded prologue:

- `Op.mbarInit base offset count` records the *address register* in `base` and the address
  offset in `offset` (0 in all 23 sites here). The shared byte offset from `wksp_buf` is the
  immediate of the `add.s32 base, wksp, imm` that writes `base` (`wksp` is the register that
  holds `.shared` symbol `wksp_buf`, decoded as `Opnd.sharedSym 0`).
- The decoded register ids differ from the PTX names: the `.b32` class starts at id 458, so
  `%rN` decodes to `458 + N` (for example `%r514` is 972 and `%r1692` is 2150).

## The 23 mbarriers

`kernel.cuh:63-77` initializes them, with `NUM_BUFS = 2` and `NUM_INDEX_BUFS = 4`
(`config.h:49-50`). Site order is the PTX order of `mbarrier.init.shared::cta.b64`; the
`SharedMemoryPlan` field order (`config.h:166-171`) is the same: each barrier occupies 8 bytes
at the offset its field takes in declaration order, and only the array elements of `mbars` are
listed in loop order rather than field order.

| # | `mbars` name | offset | count | PTX line | source |
| - | ------------ | ------ | ----- | -------- | ------ |
| 1 | `bar_last_store_done` | 222768 | 128 | 104 | `kernel.cuh:63` |
| 2 | `bar_q_tma` | 222776 | 1 | 111 | `kernel.cuh:64` |
| 3 | `bar_q_utccp` | 222784 | 1 | 117 | `kernel.cuh:65` |
| 4 | `bar_quant_part_dequant_ready[0]` | 222792 | 128 | 123 | `kernel.cuh:67` |
| 5 | `bar_raw_ready[0]` | 222808 | 1 | 129 | `kernel.cuh:68` |
| 6 | `bar_raw_free[0]` | 222824 | 128 | 135 | `kernel.cuh:69` |
| 7 | `bar_qk_done[0]` | 222904 | 1 | 141 | `kernel.cuh:70` |
| 8 | `bar_so_ready[0]` | 222920 | 128 | 147 | `kernel.cuh:71` |
| 9 | `bar_sv_done[0]` | 222936 | 1 | 153 | `kernel.cuh:72` |
| 10 | `bar_quant_part_dequant_ready[1]` | 222800 | 128 | 159 | `kernel.cuh:67` |
| 11 | `bar_raw_ready[1]` | 222816 | 1 | 165 | `kernel.cuh:68` |
| 12 | `bar_raw_free[1]` | 222832 | 128 | 171 | `kernel.cuh:69` |
| 13 | `bar_qk_done[1]` | 222912 | 1 | 177 | `kernel.cuh:70` |
| 14 | `bar_so_ready[1]` | 222928 | 128 | 183 | `kernel.cuh:71` |
| 15 | `bar_sv_done[1]` | 222944 | 1 | 189 | `kernel.cuh:72` |
| 16 | `bar_valid_coord_ready[0]` | 222840 | 32 | 196 | `kernel.cuh:75` |
| 17 | `bar_valid_coord_free[0]` | 222872 | 129 | 203 | `kernel.cuh:77` |
| 18 | `bar_valid_coord_ready[1]` | 222848 | 32 | 209 | `kernel.cuh:75` |
| 19 | `bar_valid_coord_free[1]` | 222880 | 129 | 215 | `kernel.cuh:77` |
| 20 | `bar_valid_coord_ready[2]` | 222856 | 32 | 221 | `kernel.cuh:75` |
| 21 | `bar_valid_coord_free[2]` | 222888 | 129 | 227 | `kernel.cuh:77` |
| 22 | `bar_valid_coord_ready[3]` | 222864 | 32 | 233 | `kernel.cuh:75` |
| 23 | `bar_valid_coord_free[3]` | 222896 | 129 | 239 | `kernel.cuh:77` |

The counts are the four constants the prologue moves into registers 526, 528, 543 and 545:
128 (7 sites), 1 (8 sites), 32 (4 sites) and 129 (4 sites); `129` is the source's `128+1`
(`kernel.cuh:77`, the 128 exp lanes of wg0 plus the elected KV producer lane).

The offsets follow `SharedMemoryPlan` (`config.h:141-172`) as
`u` (204800) + `s_p` (16384) + `rowwise_max_buf` (512) + `is_token_valid` (32) +
`tma_coord` (1024) + `tmem_start_addr` (16) = 222768:

- `u` (`config.h:142-157`): the `kv` member is 2 `dequant` tiles of 64*512 `bf16`
  (2*65536, `alignas(1024)`) plus 2 `raw_quant` blocks of 64*576 bytes (2*36864,
  `RAW_TOKEN_SMEM_STRIDE` = 512 + 16 + 48, `config.h:54-57,61`), 204800 bytes; the `qo` member is
  `q` (64*512 `bf16`, 65536) plus `o_accum_buf` (`cosize` of a 64x512 layout of stride 520,
  133088) = 198624 bytes, so `u` is 204800.
- `s_p` (`config.h:158-161`): `p_exchange_buf` is 4*32*32 floats = 16384.
- `rowwise_max_buf` (`config.h:162`): 128 floats = 512, at 221184; the PTX reads and writes
  `wksp_buf+221184`.
- `is_token_valid` (`config.h:163`): 4*8 bytes = 32, at 221696; the PTX addresses
  `wksp_buf+221696`.
- `tma_coord` (`config.h:164`): 4*64 `int` = 1024, at 221728; the PTX loads
  `wksp_buf+221728`.
- `tmem_start_addr` (`config.h:165`): `array_aligned<uint32_t, 1>` is `alignas(16)`, so its
  4-byte value at 222752 occupies a 16-byte slot; `tcgen05.alloc` and the following
  `ld.shared.b32` use `wksp_buf+222752`.
- the barrier block then runs 222768 to 222952, and the plan's 1024-byte alignment (from the
  `alignas(1024)` `dequant` member) rounds `sizeof(SharedMemoryPlan)` to 223232, the launch's
  dynamic shared size.

## The named CTA barriers

`config.h:22-28` declares five ids, and `kernel.cuh` (`:147`, `:196`, `:202-206`, `:220`,
`:289`, `:291`, `:350`, `:384`) and `common_subroutine.h:129` use them. The CUTLASS
`NamedBarrier` wrapper adds `ReservedNamedBarrierCount` (its `FirstUserBarrier`, 8) to a source
id, so the PTX `bar.sync`/`barrier.sync` operand is `barrierId + 8`.

| `namedBars` name | source id | PTX id | count | source |
| ---------------- | --------- | ------ | ----- | ------ |
| `main_loop_sync` | 0 | 8 | (unused) | `config.h:23`, never used |
| `wg0_sync` | 1 | 9 | 128 | `kernel.cuh:196,220,289,291,350,384` |
| `wg0_warp02_sync` | 2 | 10 | 64 | `kernel.cuh:202-206`, `common_subroutine.h:129` |
| `wg0_warp13_sync` | 3 | 11 | 64 | `kernel.cuh:202-206`, `common_subroutine.h:129` |
| `everyone_sync` | 4 | 12 | 384 | `kernel.cuh:147`, `config.h:63` (`NUM_THREADS = 128*3`) |

`main_loop_sync` is unused in this kernel: no `bar.sync` site has id 8. The count 0 below
records that, not a real arrival count. `wg0_warp02_sync` and `wg0_warp13_sync` are used through
the `retrieve_mask_and_reduce_p` template parameters with `local_warp_idx & 1`, which is why
the one site at PTX line 720 selects `10 | (warp_idx & 1)` rather than a constant.

## The 16 CTA-barrier sites

`Sites.bars` lists them in program order; the table gives the PTX line, the resolved operand
values and the named barrier each stands for.

| pc | PTX line | form | id | count | object |
| -- | -------- | ---- | -- | ----- | ------ |
| 97 | 265 | `bar.sync 0` | 0 | CTA, 384 threads (no operand) | `__syncthreads()`, `kernel.cuh:85` |
| 256 | 447 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 475 | 720 | `bar.sync` | `10+(warp_idx&1)`: 10 or 11 | 64 | `wg0_warp02_sync`/`wg0_warp13_sync` |
| 569 | 864 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 1154 | 2055 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 1156 | 2059 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 1342 | 2463 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 1502 | 2838 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 1659 | 3210 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 1817 | 3583 | `bar.sync` | 9 | 128 | `wg0_sync` |
| 1835 | 3615 | `barrier.sync` | 12 | 384 | `everyone_sync` |
| 2160 | 4212 | `barrier.sync` | 12 | 384 | `everyone_sync` |
| 2330 | 4485 | `barrier.sync` | 12 | 384 | `everyone_sync` |
| 2585 | 4791 | `barrier.sync` | 12 | 384 | `everyone_sync` |
| 2604 | 4819 | `barrier.sync` | 12 | 384 | `everyone_sync` |
| 3610 | 6673 | `barrier.sync` | 12 | 384 | `everyone_sync` |

The 10 `bar.sync` sites are the aligned form CUTLASS emits for `arrive_and_wait`; the 6
`barrier.sync` sites are the unaligned form of `arrive_and_wait_unaligned`, which is how
`everyone_sync` is used at `kernel.cuh:147`. The site at pc 1659 takes its count register
`%r1692` from `mov.b32 %r1692, 128` at PTX line 2865, 345 lines before the barrier; it is still
an unguarded constant move and no branch target lies between the two (proved below). The site at
pc 475 is the only one whose id is not a moved constant: it is
`or.b32 %r538, %r513, 10` with `%r513 = %r7 & 1` and `%r7` the shuffled `%tid.x >> 5` (warp
index), matching `BARRIER_WARP02_SYNC_ID + (local_warp_idx&1)` in `common_subroutine.h:129`;
`barSiteIds` therefore records `none` there and the shape theorem below pins the `and`/`or`.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64

open PTX

/-! ## Scanning the decoded code for register writes -/

/-- The registers an operand names, if it is a register. -/
def opndRegs : Opnd → List Nat
  | .reg r => [r]
  | _ => []

/-- The registers an operation writes, from the destination fields of its decoded form; `none`
for an `Op.unmodeled` instruction, which may write any register. -/
def opWrittenRegs : Op → Option (List Nat)
  | .prefetchTensorMap .. => some []
  | .prefetchTensor .. => some []
  | .setMaxReg .. => some []
  | .int i => some (i.dsts.filterMap id)
  | .move m => some (m.dsts.filterMap id)
  | .cvt c => some [c.d]
  | .mem a => some (a.dsts.filterMap id)
  | .addr c => some (match c with
      | .cvta _ _ _ d _ => [d]
      | .mapa _ _ d _ _ => [d]
      | .isspacep _ p _ => [p]
      | .getctarank _ _ d _ => [d]
      | .prefetch _ _ _ _ | .applypriority _ _ => [])
  | .warp w => some (w.dsts.filterMap id)
  | .matrix m => some m.dsts
  | .misc m => some (match m with
      | .createPolicy d _ => [d]
      | _ => [])
  | .float f => some (f.dsts.filterMap id)
  | .barSync .. | .barSyncN .. | .barArrive .. => some []
  | .cluster _ => some []
  | .bra .. | .brx .. | .ret | .exit | .trap => some []
  | .cpTensor .. | .cpTensorStore .. | .bulkCommit | .bulkWait .. => some []
  | .clcTryCancel .. => some []
  | .clcQuery _ _ response => some (opndRegs response)
  | .mbarInit .. | .mbarInval .. | .fence .. | .fenceMbarInit => some []
  | .mbarArrive _ _ _ _ _ _ _ state => some state.toList
  | .cpBulk _ | .asyncStore _ | .cpAsync .. | .cpAsyncCommit | .cpAsyncWait ..
  | .cpAsyncArrive .. | .prefetchBulk .. => some []
  | .mbarWait dst .. => some [dst]
  | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. | .tcMma .. | .tcCommit ..
  | .tcFenceBefore | .tcFenceAfter | .tcWaitLd | .tcWaitSt | .tcSt .. | .tcCp ..
  | .tcShift .. => some []
  | .tcLd dsts .. => some dsts
  | .unmodeled _ => none

/-- Whether the instruction may write register `r` (a guarded write counts: the register is not
known to keep its value). -/
def writesReg (r : Nat) (i : Instr) : Bool :=
  match opWrittenRegs i.op with
  | some rs => rs.contains r
  | none => true

/-- The pc of the last instruction before `pc` that may write register `r`. -/
def lastWrite? (r : Nat) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match codeAt n with
    | some i => if writesReg r i then some n else lastWrite? r n
    | none => lastWrite? r n

/-- The immediate an unguarded `mov.b32 d, imm` writes to `d`, when `d = r`. -/
def movImm? (r : Nat) (i : Instr) : Option Int :=
  match i.guard, i.op with
  | none, .move m => match m.kind, m.ty, m.dsts, m.srcs with
    | .scalar, .int .b 32, [some d], [.imm v] => if d == r then some v else none
    | _, _, _, _ => none
  | _, _ => none

/-- The value the nearest preceding write gives register `r`, when that write is an unguarded
`mov.b32` of an immediate; `none` when the nearest write is anything else (the value is
computed) or no instruction writes `r`. -/
def lastMovImm? (r pc : Nat) : Option Int :=
  match lastWrite? r pc with
  | some p => (codeAt p).bind (movImm? r)
  | none => none

/-- Whether register `r` holds the base of the dynamic shared window at `pc`: its nearest
preceding write is an unguarded `mov.b32` of the `.shared` symbol `wksp_buf`
(`Opnd.sharedSym 0`). -/
def holdsWkspBase (r pc : Nat) : Bool :=
  match lastWrite? r pc with
  | some p => match codeAt p with
    | some i => match i.guard, i.op with
      | none, .move m => match m.kind, m.dsts, m.srcs with
        | .scalar, [some d], [.sharedSym 0] => d == r
        | _, _, _ => false
      | _, _ => false
    | none => false
  | none => false

/-! ## The 23 mbarriers -/

/-- One initialized `mbarrier` of `SharedMemoryPlan`: its plan field name, its byte offset from
`wksp_buf`, and the arrival count the kernel initializes it with. -/
structure Mbar where
  /-- The `SharedMemoryPlan` field (`config.h:166-171`), with `[i]` for an array element. -/
  name : String
  /-- Shared byte offset from `wksp_buf`. -/
  offset : Nat
  /-- The count operand of `mbarrier.init`. -/
  count : Nat

/-- The 23 `mbarrier.init` sites of `Sites.mbarInits`, in site (PTX) order: PTX lines 104-239,
`kernel.cuh:63-77`. The offsets are `222768 + 8 * i` in declaration order of
`SharedMemoryPlan` (`config.h:166-171`); see the module note for the 222768 base. -/
def mbars : List Mbar :=
  [ { name := "bar_last_store_done", offset := 222768, count := 128 },
    { name := "bar_q_tma", offset := 222776, count := 1 },
    { name := "bar_q_utccp", offset := 222784, count := 1 },
    { name := "bar_quant_part_dequant_ready[0]", offset := 222792, count := 128 },
    { name := "bar_raw_ready[0]", offset := 222808, count := 1 },
    { name := "bar_raw_free[0]", offset := 222824, count := 128 },
    { name := "bar_qk_done[0]", offset := 222904, count := 1 },
    { name := "bar_so_ready[0]", offset := 222920, count := 128 },
    { name := "bar_sv_done[0]", offset := 222936, count := 1 },
    { name := "bar_quant_part_dequant_ready[1]", offset := 222800, count := 128 },
    { name := "bar_raw_ready[1]", offset := 222816, count := 1 },
    { name := "bar_raw_free[1]", offset := 222832, count := 128 },
    { name := "bar_qk_done[1]", offset := 222912, count := 1 },
    { name := "bar_so_ready[1]", offset := 222928, count := 128 },
    { name := "bar_sv_done[1]", offset := 222944, count := 1 },
    { name := "bar_valid_coord_ready[0]", offset := 222840, count := 32 },
    { name := "bar_valid_coord_free[0]", offset := 222872, count := 129 },
    { name := "bar_valid_coord_ready[1]", offset := 222848, count := 32 },
    { name := "bar_valid_coord_free[1]", offset := 222880, count := 129 },
    { name := "bar_valid_coord_ready[2]", offset := 222856, count := 32 },
    { name := "bar_valid_coord_free[2]", offset := 222888, count := 129 },
    { name := "bar_valid_coord_ready[3]", offset := 222864, count := 32 },
    { name := "bar_valid_coord_free[3]", offset := 222896, count := 129 } ]

/-- The shared byte offset of the `mbarInit` at `pc`: the immediate of the `add.s32` that writes
its address register, where the add's other operand is the register holding `wksp_buf`
(`Opnd.sharedSym 0`). -/
def initOffset? (pc : Nat) : Option Int :=
  match codeAt pc with
  | some i => match i.op with
    | .mbarInit base _ _ =>
      match lastWrite? base pc with
      | some p => match codeAt p with
        | some j => match j.guard, j.op with
          | none, .int ii => match ii.op, ii.ty, ii.dsts, ii.srcs with
            | .add, .int .s 32, [some d], [.reg b, .imm v] =>
              if d == base && holdsWkspBase b p then some v else none
            | _, _, _, _ => none
          | _, _ => none
        | none => none
      | none => none
    | _ => none
  | none => none

/-- The register the `mbarInit` at `pc` uses as its count operand. -/
def initCountReg? (pc : Nat) : Option Nat :=
  match codeAt pc with
  | some i => match i.op with
    | .mbarInit _ _ (.reg r) => some r
    | _ => none
  | none => none

/-- The value the kernel gives the count register of the `mbarInit` at `pc`: the immediate of
its nearest preceding write, when that write is an unguarded `mov.b32` (an immediate count
operand is returned directly). -/
def initCountValue? (pc : Nat) : Option Int :=
  match codeAt pc with
  | some i => match i.op with
    | .mbarInit _ _ (.reg r) => lastMovImm? r pc
    | .mbarInit _ _ (.imm v) => some v
    | _ => none
  | none => none

/-- The 23 offsets `mbars` records are, in site order, the offsets the decoded prologue adds to
the `wksp_buf` base register before each initialization (PTX lines 104-239). -/
theorem mbars_offsets :
    mbarInits.map initOffset? = mbars.map fun m => some (Int.ofNat m.offset) := by
  decide +kernel

/-- The 23 initialization sites are distinct. -/
theorem mbarInits_nodup : mbarInits.Nodup := by
  decide +kernel

/-- Every initialization sits in the prologue block, before the `fence.mbarrier_init` at pc 87
(PTX line 244). -/
theorem mbarInits_prologue : mbarInits.all (fun pc => pc < 87) = true := by
  decide +kernel

/-- The count register of each initialization, in site order: the prologue uses only registers
526, 528, 543 and 545. -/
theorem mbarInits_countRegs :
    mbarInits.map initCountReg? =
      [some 526, some 528, some 528, some 526, some 528, some 526, some 528, some 526,
       some 528, some 526, some 528, some 526, some 528, some 526, some 528, some 543,
       some 545, some 543, some 545, some 543, some 545, some 543, some 545] := by
  decide +kernel

/-- For every initialization, the nearest preceding write to its count register is an unguarded
`mov.b32` whose immediate is the recorded count: no count is computed. The same four registers
carry 128 (526), 1 (528), 32 (543) and 129 (545). -/
theorem mbars_counts :
    mbarInits.map initCountValue? = mbars.map fun m => some (Int.ofNat m.count) := by
  decide +kernel

/-! ## Branch targets and the dominance of the defining moves -/

/-- The branch targets of the program: every `bra` target and every `brx` table entry. -/
def branchTargets : List Nat :=
  Decoded.kernel.code.flatMap fun i =>
    match i.op with
    | .bra t _ => [t]
    | .brx _ ts _ => ts
    | _ => []

/-- The `(first defining move pc, use pc)` intervals of the values the two tables record: one
interval for the prologue, whose `wksp_buf` move (pc 36) and count moves (pcs 38-73) define
every address and count of the 23 initializations, and one interval per barrier site for its id
and count moves. The one computed barrier id (pc 475) contributes only its count move. -/
def valueWindows : List (Nat × Nat) :=
  [ (36, 86),
    (254, 256), (474, 475), (567, 569), (1152, 1156), (1340, 1342), (1500, 1502),
    (1518, 1659), (1658, 1659), (1815, 1817), (1833, 1835), (2158, 2160), (2328, 2330),
    (2583, 2585), (2602, 2604), (3608, 3610) ]

/-- No branch target lies strictly between a defining move and the instruction that uses its
value, nor at the use itself: on every path that reaches the use, the move has executed. (A
target at the move's own pc is fine, and so is a branch out of the interval.) -/
theorem no_branch_into_value_windows :
    (branchTargets.filter fun p => valueWindows.any fun w => w.1 < p && p ≤ w.2).isEmpty =
      true := by
  decide +kernel

/-! ## The five named barriers -/

/-- One `NamedBarriers` id of `config.h:22-28`. `barrierId` is the source value; `ptxId` is the
operand the CUTLASS `NamedBarrier` wrapper emits, `barrierId + ReservedNamedBarrierCount` = 8
(`cutlass/arch/barrier.h`, `ReservedNamedBarriers::FirstUserBarrier`). -/
structure NamedBar where
  /-- The enumerator name (`config.h:23-27`). -/
  name : String
  /-- The source id (`config.h:23-27`). -/
  barrierId : Nat
  /-- The count the source passes to `NamedBarrier::arrive_and_wait` (0: never used). -/
  count : Nat
  /-- The id the PTX `bar.sync`/`barrier.sync` carries. -/
  ptxId : Nat

/-- The five named barriers, with the counts the source uses: `wg0_sync` 128
(`kernel.cuh:196,220,289,291,350,384`); `wg0_warp02_sync` / `wg0_warp13_sync` 64
(`common_subroutine.h:129`, selected by `local_warp_idx & 1` through the
`retrieve_mask_and_reduce_p` template arguments at `kernel.cuh:202-206`); `everyone_sync`
`NUM_THREADS` = 384 (`kernel.cuh:147`, `config.h:63`). `main_loop_sync` is declared but never
used, so its count is recorded as 0. -/
def namedBars : List NamedBar :=
  [ { name := "main_loop_sync", barrierId := 0, count := 0, ptxId := 8 },
    { name := "wg0_sync", barrierId := 1, count := 128, ptxId := 9 },
    { name := "wg0_warp02_sync", barrierId := 2, count := 64, ptxId := 10 },
    { name := "wg0_warp13_sync", barrierId := 3, count := 64, ptxId := 11 },
    { name := "everyone_sync", barrierId := 4, count := 384, ptxId := 12 } ]

/-- The source ids are 0 to 4 (`config.h:23-27`). -/
theorem namedBars_ids : namedBars.map (fun b => b.barrierId) = [0, 1, 2, 3, 4] := by
  decide

/-- The PTX ids are the source ids plus the CUTLASS reserved count 8. -/
theorem namedBars_ptxIds : namedBars.map (fun b => b.ptxId) = [8, 9, 10, 11, 12] := by
  decide

/-- Every PTX id equals its source id plus 8. -/
theorem namedBars_reserved : namedBars.all (fun b => b.ptxId == b.barrierId + 8) = true := by
  decide

/-- The counts: no count for the unused `main_loop_sync`, 128 for `wg0_sync`, 64 for the two
warp-pair barriers and 384 for `everyone_sync`. -/
theorem namedBars_counts : namedBars.map (fun b => b.count) = [0, 128, 64, 64, 384] := by
  decide

/-! ## The 16 CTA-barrier sites -/

/-- The barrier id of the `bar.sync`/`barrier.sync` site at `pc`: the immediate for the form
without a thread count, and the immediate of the nearest preceding unguarded `mov.b32` for the
id register; `none` when the id is computed or no such move precedes. -/
def barIdValue? (pc : Nat) : Option Int :=
  match codeAt pc with
  | some i => match i.op with
    | .barSync (.imm v) _ => some v
    | .barSync (.reg a) _ => lastMovImm? a pc
    | .barSyncN (.imm v) _ _ => some v
    | .barSyncN (.reg a) _ _ => lastMovImm? a pc
    | _ => none
  | none => none

/-- The thread count of the site at `pc`: the immediate of the nearest preceding unguarded
`mov.b32` for the count register; `none` for the form without a thread count (the whole CTA). -/
def barCountValue? (pc : Nat) : Option Int :=
  match codeAt pc with
  | some i => match i.op with
    | .barSyncN _ (.imm v) _ => some v
    | .barSyncN _ (.reg c) _ => lastMovImm? c pc
    | _ => none
  | none => none

/-- The `.aligned` flag of the site at `pc`: true for `bar.sync` and `barrier.sync.aligned`,
false for `barrier.sync`. -/
def barAligned? (pc : Nat) : Bool :=
  match codeAt pc with
  | some i => match i.op with
    | .barSync _ a | .barSyncN _ _ a | .barArrive _ _ a => a
    | _ => false
  | none => false

/-- The id operands of the 16 sites of `Sites.bars`, in order. Site 475 is the computed id; the
`bar.sync 0` at site 97 is the whole-CTA barrier (immediate, not a named barrier). -/
def barSiteIds : List (Option Int) := bars.map barIdValue?

/-- The id operands: 0 at the `__syncthreads`, 9 at each `wg0_sync`, computed at the
warp-pair site, 12 at each `everyone_sync`. -/
theorem barSiteIds_eq :
    barSiteIds = [some 0, some 9, none, some 9, some 9, some 9, some 9, some 9, some 9,
      some 9, some 12, some 12, some 12, some 12, some 12, some 12] := by
  decide +kernel

/-- The thread counts of the 16 sites, in order: none for the count-less `bar.sync 0`, 128 for
each `wg0_sync`, 64 for the warp-pair barrier, 384 for each `everyone_sync`. -/
def barSiteCounts : List (Option Int) := bars.map barCountValue?

/-- The count operands. -/
theorem barSiteCounts_eq :
    barSiteCounts = [none, some 128, some 64, some 128, some 128, some 128, some 128,
      some 128, some 128, some 128, some 384, some 384, some 384, some 384, some 384,
      some 384] := by
  decide +kernel

/-- The aligned flags of the 16 sites: true for the ten `bar.sync` sites, false for the six
`barrier.sync` sites (`everyone_sync`, `kernel.cuh:147`). -/
def barSiteAligned : List Bool := bars.map barAligned?

/-- The aligned flags. -/
theorem barSiteAligned_eq :
    barSiteAligned = [true, true, true, true, true, true, true, true, true, true, false, false,
      false, false, false, false] := by
  decide +kernel

/-- Every constant-id site pairs its PTX id and count with one of `namedBars`: the resolved
pairs are `(9, 128)` for `wg0_sync` and `(12, 384)` for `everyone_sync`. The `bar.sync 0` site
(the whole-CTA barrier) and the computed site at pc 475 are excluded. -/
theorem barSites_match_namedBars :
    (bars.filter (fun pc => pc != 97 && pc != 475)).all (fun pc =>
      match barIdValue? pc, barCountValue? pc with
      | some id, some c => namedBars.any (fun b => b.ptxId == id && b.count == c)
      | _, _ => false) = true := by
  decide +kernel

/-- The unguarded integer instruction at `pc`, as `(operation, type, destinations, sources)`;
`none` when the instruction is guarded or is not an integer instruction. -/
def intAt? : Nat → Option (IntOp × DType × List (Option Nat) × List Opnd)
  | pc => match codeAt pc with
    | some i => match i.guard, i.op with
      | none, .int ii => some (ii.op, ii.ty, ii.dsts, ii.srcs)
      | _, _ => none
    | none => none

/-- The one computed barrier id: pc 475 reads `or.b32 %r538, %r513, 10` with
`%r513 = %r7 & 1`. `%r7` is the warp index (`shfl.sync.idx.b32 %r7, %r6, 0, 31, -1` of
`%r6 = %tid.x >> 5`, PTX lines 50-51), so the id is `10 | (warp_idx & 1)`, that is
`wg0_warp02_sync` or `wg0_warp13_sync` (`common_subroutine.h:129`). -/
theorem bar475_id_computed :
    intAt? 241 = some (IntOp.and, DType.int IType.b 32, [some 971], [Opnd.reg 465, Opnd.imm 1]) ∧
      intAt? 242 = some (IntOp.or, DType.int IType.b 32, [some 996], [Opnd.reg 971, Opnd.imm 10]) :=
  ⟨rfl, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Idle
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Data.Mma
public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Lemmas.Flow.Bar
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.SegFree
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.Compose
public import Lemmas.Flow.TensorIssue
public import Lemmas.Flow.Tc
public import Lemmas.Flow.TcMmaTs
public import Lemmas.Flow.Events
public import Lemmas.Flow.SignedBits
public import Lemmas.Flow.RoleTemplates
public import Lemmas.Flow.OrBits
public import Lemmas.Flow.BitForms
public import Lemmas.Flow.Join
public import Lemmas.Execution.EventFrame

@[expose] public section

/-! # `wg1Mma`: warp 4 of warpgroup 1, the MMA warp of the FlashMLA sparse decode kernel

Warp 4 (pcs 1843-2161, `kernel.cuh:409`, "MMA Warp") issues the kernel's two `tcgen05.mma.ws`
GEMMs. The file also holds the warpgroup-1 head (pcs 1843-1849), which every warp of warpgroup 1
executes: the warp-index broadcast, the three warp tests, and the hand-off to warp 7's index
role (2332), warp 5's raw-KV producer (2162), and warp 6's idle main loop (2587). Warp 4 falls
through the tests at 1850.

The warp-4 body:

* lines 1850-1857 elect one lane of the warp; the unelected lanes leave for the idle loop
  (`Wg1Idle`, pc 2587). The elected lane reads the launch's batch count `b` and traps out of the
  role when `%ctaid.y >= b` (pc 1860, to the `ret` at 3611), then reads the row's two lengths
  (`topk_length` / `extra_topk_length`, `ld.global.nc` where a pointer is non-null) and forms the
  padded total `max(64, 64 ceil(len0/64)) + 64 ceil(len1/64)` (pcs 1878-1893); the total is at
  least 64, so the `trap` at 1896 is not reached;
* it loads the query tile with eight rank-4 TMA copies into 64 KiB of shared memory (`cpTensor`,
  pcs 1906-1927; map `param_1 + 128`, coordinates `0/64/…/448`, `0`, `%ctaid.x`, `%ctaid.y`,
  barrier `bar_q_tma`), arrives with `expect_tx 65536` (1929) and waits (1931);
* it copies the query from shared memory into Tensor Memory with sixteen
  `tcgen05.cp.128x256b` (1936-1980, columns 256-383), commits to `bar_q_utccp` (1982) and waits
  (1983); the block loop then starts at 2003;
* per 64-token block it waits `bar_dequant_ready[phase]` (2012), issues the sixteen QK
  `tcgen05.mma.ws` into P at Tensor-Memory column 400 (2027-2103, A = Q from Tensor Memory,
  B = the K tile in shared memory), commits to `bar_qk_done[phase]` (2105) and waits
  `bar_so_ready[phase]` (2107) for the softmax warpgroup's P tile in shared memory;
* it issues the eight PV `tcgen05.mma.ws` that accumulate O at columns 0 and 128 (2117-2146,
  A = P from shared memory, B = the V tile) and commits to `bar_sv_done[phase]` (2148);
* it flips the buffer phase xor and the parity toggle (2149-2155) and repeats while the block
  counter is negative, then passes the CTA-wide `barrier.sync 12, 384` (2160) and returns at
  the program's single `ret` (2161 to 3611).

## The site machine

The abstract states (`Site`) are the role's event instructions, in program order: the
warp-index shuffle, the election, the two `.nc` length reads, the eight Q TMA issues, the
arrive and wait of `bar_q_tma`, the copy fence, the sixteen `tcgen05.cp`, the copy commit and
wait, the copy fence, and — inside the block loop — the dequant wait and fence, the sixteen QK
MMAs, the QK commit, the softmax wait and fence, the eight PV MMAs, the PV commit, and finally
the CTA barrier and the `ret`. Every other instruction the role runs is local and lies between
two sites; the local segments evaluate them by kernel reduction.

`D` is the role's small state: the next site and the block iteration `i` (the 64-token block of
the padded token list). Every register the role reads is a function of `(P, L, g, i)`: the
launch's reads, the two length values, the padded total and block count, the shared addresses,
the phase `i % 2` and parity `i / 2 % 2` of the two-slot ring, the barrier addresses, the four
shared matrix descriptors and sixteen Tensor-Memory columns.

## The invariant

`Inv` records what the role needs beyond the value table:

* the thread is warp 4 of warpgroup 1 (`warpOf L g = 4`) and a lane of the warp;
* the block iteration is bounded by the padded block count, and the two exit states are at the
  loop's end (`i = blocks`);
* the query map is the launch's map at `param_1 + 128` (`Pre.mapQBind`);
* the two instruction descriptors decode to the QK and PV descriptors of `Data/Mma.lean`;
* the Tensor-Memory allocation starts at column 0 (the prologue's allocation check) and the
  Q, P and O column ranges fit the 512 allocated columns: Q at 256 (128 columns), P at 400
  (64 columns) and O at 0 (two 128-column blocks).

The KV block's cache tag is not observable in this role: the QK and PV B descriptors name the
shared dequantized tile, which either cache's gather fills. The block index is `d.i`, the
64-token block of the padded list.

The value table makes the register content of `Inv` explicit: `%r100`/`%r6` (register 558/464)
are `warpOf L g`, so `Inv.warp` is `%r100 = 4`; the TMEM operands are `tmemBase + {O, Q, P}`
plus the per-MMA column offsets, so the Q, P and O ranges are the invariant's `tmem_ranges`; the
Q descriptor address is `param_1 + 128` (`Inv.qmap`, register 3058); the Q load coordinates are
`qCoord` and `qDstOff`; the barrier ring's addresses and parities are `phaseOf`/`parOf` of the
block index; and the idesc registers 859 and 880 are `qkIdesc` and `pvIdesc`, whose decoded
descriptors are `Inv.qk_desc`/`Inv.pv_desc`.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxErrors 1000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.deprecated false

namespace Wg1Mma

/-- The assumptions the role is evaluated under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ## The thread's place in the launch

The batch and query of the thread's CTA (`eOf`, `qOf`) are the `%ctaid` coordinates the kernel
indexes its tensors with. `Proof/Thread/Wg1Idle.lean` and the prologue give the launch reads
`ctaidX`, `ctaidY`, `tidOf`, `laneOf` and `warpOf`, and the shared window's base `sb`. -/

/-- The thread's CTA (`%ctaid` is per CTA). -/
def ctaOf (L : Launch) (g : Nat) : Nat := g / L.block

/-- `%ctaid.y` of the thread's CTA: the batch of the kernel's `(s_q, b, 1)` grid. -/
def batchOf (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).y % 2 ^ 32

/-- `%ctaid.x` of the thread's CTA: the query position. -/
def queryOf (L : Launch) (g : Nat) : Nat := (L.ctaidOf (ctaOf L g)).x % 2 ^ 32

theorem batchOf_eq_ctaidY (L : Launch) (g : Nat) : batchOf L g = ctaidY L g := rfl

theorem queryOf_eq_ctaidX (L : Launch) (g : Nat) : queryOf L g = ctaidX L g := rfl

/-- A 32-bit word of the scalar parameter object `param_0`, as the launch supplies it. -/
abbrev paramWord (L : Launch) (off n : Nat) : Nat := paramNat L (param "0") off n

/-- The CTAs of the kernel's grid are the launch's `(s_q, b, 1)` block indices, so every CTA
index is in range. The cluster has one CTA (`Pre.clusterSize`), which makes `%ctaid` its
cluster place. -/
theorem ctaidOf_eq (hpre : Pre P L mem0) (c : Nat) :
    L.ctaidOf c = ⟨c % P.s_q, c / P.s_q % P.b, 0⟩ := by
  have hsz : L.clusterSize.val = 1 := hpre.clusterSize
  have hloc : ∀ (n k cc : Nat), L.locate n k cc = (k + cc, 0) := by
    intro n k cc
    rw [Launch.locate_regular (fun k => by rw [hpre.clusterPlaces, hsz]; rfl), hsz,
      Nat.div_one, Nat.mod_one]
  have hco : L.clusterOfCta c = c := by
    simp only [Launch.clusterOfCta, hloc, Nat.zero_add]
  have hrk : L.rankOfCta c = 0 := by
    simp only [Launch.rankOfCta, hloc]
  have hplace : L.clusterPlaces c = ⟨⟨c % P.s_q, c / P.s_q % P.b, 0⟩, ⟨1, 1, 1⟩,
      ⟨c % P.s_q, c / P.s_q % P.b, 0⟩, ⟨P.s_q, P.b, 1⟩⟩ := by
    rw [hpre.clusterPlaces]; rfl
  simp only [Launch.ctaidOf, Launch.placeOf, hco, hplace, Launch.clusterCtaidOf, hrk,
    Dim3.coord]
  simp only [Nat.mod_one, Nat.div_one, Nat.zero_add, Nat.add_zero]

/-- The batch of the thread's CTA, as the linear block index gives it. -/
theorem batchOf_eq (hpre : Pre P L mem0) (g : Nat) :
    batchOf L g = (g / L.block) / P.s_q % P.b := by
  unfold batchOf ctaOf
  rw [ctaidOf_eq hpre]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpre.bPos) hpre.bRange)

/-- The query of the thread's CTA, as the linear block index gives it. -/
theorem queryOf_eq (hpre : Pre P L mem0) (g : Nat) :
    queryOf L g = g / L.block % P.s_q := by
  unfold queryOf ctaOf
  rw [ctaidOf_eq hpre]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpre.sqPos) hpre.sqRange)

/-- The thread's CTA is a batch index of the grid. -/
theorem batchOf_lt (hpre : Pre P L mem0) {g : Nat} (_hg : g < L.threads) :
    batchOf L g < P.b := by
  rw [batchOf_eq hpre]
  exact Nat.mod_lt _ hpre.bPos

/-- The thread's CTA is a query index of the grid. -/
theorem queryOf_lt (hpre : Pre P L mem0) {g : Nat} (_hg : g < L.threads) :
    queryOf L g < P.s_q := by
  rw [queryOf_eq hpre]
  exact Nat.mod_lt _ hpre.sqPos

/-- The role's batch (`%ctaid.y`). -/
def eOf (L : Launch) (g : Nat) : Nat := batchOf L g

/-- The value of the exit guard `setp.ge.s32 %p58, %ctaid.y, b` (pc 1859). -/
def geBatch (L : Launch) (g : Nat) : Bool :=
  compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 (eOf L g)))
    (truncBits 32 (BitVec.ofNat 64 (paramWord L 0 4)))

/-- `ptrIsNull L off`: the 64-bit pointer word at byte `off` of `param_0` is zero, i.e. the
optional array is absent. -/
def ptrIsNull (L : Launch) (off : Nat) : Bool :=
  compare .eq .b 64 (truncBits 64 (BitVec.ofNat 64 (paramWord L off 8)))
    (truncBits 64 (BitVec.ofInt 64 0))

/-! ## The token geometry of the block loop -/

/-- `n` rounded up to a multiple of 64, the padding the kernel applies to each length. -/
def pad64 (n : Nat) : Nat := (n + 63) / 64 * 64

/-- The row's main-cache length (`topk_length`, or `topk` when the pointer is null). -/
def len0 (P : Params) (L : Launch) (g : Nat) : Nat := P.topkLen (eOf L g)

/-- The row's extra-cache length (`extra_topk_length`, or `extra_topk`). -/
def len1 (P : Params) (L : Launch) (g : Nat) : Nat := P.extraTopkLen (eOf L g)

/-- The padded token total `%r27`: `max(64, 64 ceil(len0/64)) + 64 ceil(len1/64)`. -/
def total (P : Params) (L : Launch) (g : Nat) : Nat :=
  max (pad64 (len0 P L g)) 64 + pad64 (len1 P L g)

/-- The number of 64-token blocks the loop runs. -/
def blocks (P : Params) (L : Launch) (g : Nat) : Nat := total P L g / 64

theorem blocks_pos (P : Params) (L : Launch) (g : Nat) : 0 < blocks P L g := by
  unfold blocks total
  have hle : 64 ≤ max (pad64 (len0 P L g)) 64 + pad64 (len1 P L g) :=
    Nat.le_add_right_of_le (Nat.le_max_right _ _)
  exact Nat.div_pos hle (by decide)

/-- The ring phase of block `i`: the two-slot KV buffers and their barriers. -/
def phaseOf (i : Nat) : Nat := i % 2

/-- The ring parity of block `i`: the barriers complete once per two blocks. -/
def parOf (i : Nat) : Nat := i / 2 % 2

/-! ## Tensor-Memory columns and the protocol objects -/

/-- The Tensor-Memory column the allocation starts at: the prologue's `tcgen05.alloc` of 512
columns returned address 0, which is the only value for which it does not trap. -/
def tmemBase : Nat := 0

/-- The first Tensor-Memory column of the O accumulator (two 128-column blocks). -/
def tmemO : Nat := 0

/-- The first Tensor-Memory column of the Q operand (`tcgen05.cp`'s destination). -/
def tmemQ : Nat := 256

/-- The first Tensor-Memory column of the QK result P. -/
def tmemP : Nat := 400

/-- The 512 columns the prologue allocates. -/
def tmemAlloc : Nat := 512

/-- The A operand column of QK MMA `k`: 8 columns per copy of the query tile. -/
def qkACol (k : Fin 16) : Nat := tmemQ + 8 * k.val

/-- The destination column of `tcgen05.cp` copy `k`. -/
def qCopyCol (k : Fin 16) : Nat := tmemQ + 8 * k.val

/-- The accumulator column of PV MMA `k`: the O blocks at columns 0 and 128 alternate. -/
def pvDest (k : Fin 8) : Nat := tmemO + 128 * (k.val % 2)

/-- The shared byte offset of the dequantized K/V tile of a ring phase: two 64 KiB buffers. -/
def kvBase (L : Launch) (i : Nat) : Nat := L.sharedBase + 65536 * (i % 2)

/-- The low 15-bit start field of a shared matrix descriptor over `off`: 16-byte units, the
14-bit window the kernel's shared addresses stay in (`Pre.sharedRange`). -/
def descLo (off : Nat) : Nat := off / 16 % 2 ^ 14

/-- The shared-memory source descriptor of the query tile (`tcgen05.cp` and the QK A). -/
def qDescLo (L : Launch) : Nat := descLo L.sharedBase

/-- The descriptor of `tcgen05.cp` copy `k`: the b128-swizzled query tile, 32 bytes apart in a
group of four copies and 16 KiB between groups. -/
def qCopyDesc (L : Launch) (k : Fin 16) : Value :=
  b64 (qDescLo L + (1024 * (k.val / 4) + 2 * (k.val % 4)) + 4611756662049538048)

/-- The K-major descriptor of the dequantized K tile of block `i` (leading 16, stride 1024,
128-byte swizzle), offset `delta` 16-byte units into the tile. -/
def kDesc (L : Launch) (i delta : Nat) : Value :=
  b64 (descLo (kvBase L i) + delta + 4611756662049538048)

/-- The MN-major descriptor of the dequantized V tile of block `i` (leading 512, stride 1024). -/
def vDesc (L : Launch) (i delta : Nat) : Value :=
  b64 (descLo (kvBase L i) + delta + 4611756662083026944)

/-- The descriptor of the shared P tile (unswizzled, leading 1024, stride 128) at byte offset
`128 k` of the softmax output: the A operand of PV MMA `k`. -/
def pDesc (L : Launch) (k : Nat) : Value :=
  b64 (descLo (L.sharedBase + 204800) + 128 * k + 70403108110336)

/-- The offset of QK MMA `j`'s B descriptor into the K tile: four groups of four 32-byte steps
16 KiB apart. -/
def qkBDelta (j : Nat) : Nat := 1024 * (j / 4) + 2 * (j % 4)

/-- The offset of PV MMA `j`'s B descriptor into the V tile: the four 64-byte column groups of
two 32 KiB halves. -/
def pvBDelta (j : Nat) : Nat := 128 * (j / 2) + 2048 * (j % 2)

/-- The first coordinate of Q TMA load `k`: the head-dimension tile of the 512-wide row. -/
def qCoord (k : Fin 8) : Nat := 64 * k.val

/-- The shared byte offset of Q TMA load `k`'s 8192-byte frame: the eight frames tile the
64 KiB query buffer. -/
def qDstOff (k : Fin 8) : Nat := 8192 * k.val

/-- The shared byte of the query descriptor the eight TMA loads name: `param_1 + 128`. -/
def qMapOff : Nat := 128

/-- The cache-policy operand of the Q TMA loads (`createpolicy.fractional.L2::evict_last`
built by the compiler as a constant). -/
def qCachePolicy : Nat := 1364590687093260288

theorem qTmaOff : (Protocol.Mbar.qTma).off = 222776 := rfl

theorem qUtccpOff : (Protocol.Mbar.qUtccp).off = 222784 := rfl

theorem dequantOff (i : Nat) :
    (Protocol.Mbar.dequantReady ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off =
      222792 + 8 * (i % 2) := by
  simp only [Protocol.Mbar.off]
  split <;> omega

theorem qkDoneOff (i : Nat) : (Protocol.Mbar.qkDone ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off =
    222904 + 8 * (i % 2) := by
  simp only [Protocol.Mbar.off]
  split <;> omega

theorem soReadyOff (i : Nat) : (Protocol.Mbar.soReady ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off =
    222920 + 8 * (i % 2) := by
  simp only [Protocol.Mbar.off]
  split <;> omega

theorem svDoneOff (i : Nat) : (Protocol.Mbar.svDone ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off =
    222936 + 8 * (i % 2) := by
  simp only [Protocol.Mbar.off]

/-- The `bar_q_tma` address: `param_1`'s Q copies complete here. -/
def qTmaAddr (L : Launch) : Nat := L.sharedBase + (Protocol.Mbar.qTma).off

/-- The `bar_q_utccp` address: the query's shared-to-Tensor-Memory copies complete here. -/
def qUtccpAddr (L : Launch) : Nat := L.sharedBase + (Protocol.Mbar.qUtccp).off

/-- The address of `bar_dequant_ready[phase]`. -/
def dequantAddr (L : Launch) (i : Nat) : Nat :=
  L.sharedBase + (Protocol.Mbar.dequantReady ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off

/-- The address of `bar_qk_done[phase]`. -/
def qkDoneAddr (L : Launch) (i : Nat) : Nat :=
  L.sharedBase + (Protocol.Mbar.qkDone ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off

/-- The address of `bar_so_ready[phase]`. -/
def soReadyAddr (L : Launch) (i : Nat) : Nat :=
  L.sharedBase + (Protocol.Mbar.soReady ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off

/-- The address of `bar_sv_done[phase]`. -/
def svDoneAddr (L : Launch) (i : Nat) : Nat :=
  L.sharedBase + (Protocol.Mbar.svDone ⟨i % 2, Nat.mod_lt _ (by decide)⟩).off

/-! ## The sites -/

/-- The role's event instructions. `head` and `elect` are the warpgroup-1 head's events (the
shuffle and the election); `loadTopk` and `loadExtra` are the two `.nc` length reads; the
`q*` sites are the query's TMA load, its completion, and the shared-to-Tensor-Memory copy; the
`kvWait` … `pvCommit` sites are one iteration of the block loop; `outBar` and `exit` are the
role's end. -/
inductive Site where
  /-- The warp-index broadcast `shfl.sync.idx.b32 %r100|%p10, %r6, 0, 31, -1` (pc 1843). -/
  | head
  /-- The election of the lane that issues the MMAs (pc 1853). -/
  | elect
  /-- The `topk_length` read (pc 1876), when its pointer is non-null. -/
  | loadTopk
  /-- The `extra_topk_length` read (pc 1886), when its pointer is non-null. -/
  | loadExtra
  /-- Q TMA load `k` of the eight rank-4 copies (pcs 1906-1927). -/
  | qLoad (k : Fin 8)
  /-- The `mbarrier.arrive.expect_tx` of `bar_q_tma` with 65536 bytes (pc 1929). -/
  | qArrive
  /-- The wait on `bar_q_tma` (pc 1931). -/
  | qWait
  /-- The fence between the Q wait and the Tensor-Memory copies (pc 1934). -/
  | qFence
  /-- `tcgen05.cp` copy `k` of the sixteen (pcs 1936-1980). -/
  | qCopy (k : Fin 16)
  /-- The `tcgen05.commit` of the sixteen copies to `bar_q_utccp` (pc 1982). -/
  | qCopyCommit
  /-- The wait on `bar_q_utccp` (pc 1983). -/
  | qCopyWait
  /-- The fence between the copy wait and the first block (pc 1986). -/
  | qCopyFence
  /-- The wait on `bar_dequant_ready[phase]` (pc 2012). -/
  | kvWait
  /-- The fence between the dequant wait and the QK MMAs (pc 2015). -/
  | kvFence
  /-- QK MMA `k` (pcs 2027-2103). -/
  | qkMma (k : Fin 16)
  /-- The `tcgen05.commit` of the QK MMAs to `bar_qk_done[phase]` (pc 2105). -/
  | qkCommit
  /-- The wait on `bar_so_ready[phase]` (pc 2107). -/
  | soWait
  /-- The fence between the softmax wait and the PV MMAs (pc 2110). -/
  | soFence
  /-- PV MMA `k` (pcs 2117-2146). -/
  | pvMma (k : Fin 8)
  /-- The `tcgen05.commit` of the PV MMAs to `bar_sv_done[phase]` (pc 2148). -/
  | pvCommit
  /-- `barrier.sync 12, 384` at the role's end (pc 2160). -/
  | outBar
  /-- The kernel's single `ret` (pc 3611). -/
  | exit
  deriving DecidableEq, Repr

/-- The eight Q TMA issues. -/
def qLoadPcs : List Nat := (List.finRange 8).map fun k => Flow.tensorCopy.getD (4 + k.val) 0

/-- The sixteen shared-to-Tensor-Memory copies. -/
def qCopyPcs : List Nat := (List.finRange 16).map fun k => Flow.tmemCopy.getD k.val 0

/-- The sixteen QK MMAs. -/
def qkMmaPcs : List Nat := (List.finRange 16).map fun k => Flow.mma.getD k.val 0

/-- The eight PV MMAs. -/
def pvMmaPcs : List Nat := (List.finRange 8).map fun k => Flow.mma.getD (16 + k.val) 0

/-- Every site's program counter, in program order. -/
def eventPcs : List Nat :=
  [Flow.shfl_2, Flow.elect_6, Flow.load_15, Flow.load_16] ++ qLoadPcs ++
    [Flow.mbarArrive_3, Flow.mbarWait_3, Flow.tcFence_5] ++ qCopyPcs ++
    [Flow.tcCommit_0, Flow.mbarWait_4, Flow.tcFence_6, Flow.mbarWait_5, Flow.tcFence_7] ++
    qkMmaPcs ++ [Flow.tcCommit_1, Flow.mbarWait_6, Flow.tcFence_8] ++ pvMmaPcs ++
    [Flow.tcCommit_2, Flow.bar_11, Flow.exit_0]

def Site.pc : Site → Nat
  | .head => Flow.shfl_2
  | .elect => Flow.elect_6
  | .loadTopk => Flow.load_15
  | .loadExtra => Flow.load_16
  | .qLoad k => Flow.tensorCopy.getD (4 + k.val) 0
  | .qArrive => Flow.mbarArrive_3
  | .qWait => Flow.mbarWait_3
  | .qFence => Flow.tcFence_5
  | .qCopy k => Flow.tmemCopy.getD k.val 0
  | .qCopyCommit => Flow.tcCommit_0
  | .qCopyWait => Flow.mbarWait_4
  | .qCopyFence => Flow.tcFence_6
  | .kvWait => Flow.mbarWait_5
  | .kvFence => Flow.tcFence_7
  | .qkMma k => Flow.mma.getD k.val 0
  | .qkCommit => Flow.tcCommit_1
  | .soWait => Flow.mbarWait_6
  | .soFence => Flow.tcFence_8
  | .pvMma k => Flow.mma.getD (16 + k.val) 0
  | .pvCommit => Flow.tcCommit_2
  | .outBar => Flow.bar_11
  | .exit => Flow.exit_0

/-- The role's small state: the next site and the block iteration. -/
structure D where
  /-- The next event. -/
  site : Site
  /-- The 64-token block of the padded token list the loop is in. -/
  i : Nat

/-- The first state: the warp-index shuffle, block 0. -/
def init : D := { site := .head, i := 0 }

/-! ## The abstract state and the register table -/

/-- The site the elected lane enters after the election: the exit when the CTA is outside the
batch grid, else the first `.nc` length read (or the query load when a pointer is null). -/
def startSite (_P : Params) (L : Launch) (g : Nat) : Site :=
  if geBatch L g then .exit
  else if ptrIsNull L 80 then (if ptrIsNull L 144 then .qLoad 0 else .loadExtra)
  else .loadTopk

/-- The site after the `topk_length` read. -/
def afterTopk (L : Launch) : Site := if ptrIsNull L 144 then .qLoad 0 else .loadExtra

/-- The QK instruction descriptor (M 64, N 128, bf16 inputs, f32 accumulator, K-major). -/
def qkDescriptor : TcMma.Descriptor :=
  { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 128, negateA := false,
    negateB := false, transposeA := false, transposeB := false, ws := true }

/-- The PV instruction descriptor (M 64, N 256, bf16 inputs, f32 accumulator, B MN-major). -/
def pvDescriptor : TcMma.Descriptor :=
  { group := .one, kind := .f16 .bf16 .f32, m := 64, n := 256, negateA := false,
    negateB := false, transposeA := false, transposeB := true, ws := true }

/-- A 16-bit integer value. -/
def b16 (n : Nat) : Value := .bits 16 (BitVec.ofNat 64 n)

/-- The exit guard of the padded total (`setp.gt.s32 %p61, %r485, 63` at pc 1894): the total
exceeds the block size, so the `trap` at 1896 is not reached. -/
def totalGt63 (P : Params) (L : Launch) (g : Nat) : Bool :=
  compare .gt .s 32 (truncBits 32 (BitVec.ofNat 64 (total P L g)))
    (truncBits 32 (BitVec.ofInt 64 63))

/-- The registers of the role, as functions of the launch and the block iteration. Every
register live at a site is here; `valueOf` reads the table. -/
def values (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let ph := phaseOf d.i
  let par := parOf d.i
  [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
   (464, b32 (warpOf L g)), (466, b32 (laneOf L g)), (796, sb L 0),
   (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   -- the warpgroup-1 head
   (558, b32 (warpOf L g)), (10, .pred true),
   (11, .pred (warpOf L g == 7)), (12, .pred (warpOf L g == 5)),
   (13, .pred (warpOf L g != 4)),
   (793, b32 0), (794, b32 4294967295),
   -- the parameter loads and the padded total
   (795, b32 (paramWord L 0 4)),
   (3004, b64 (paramWord L 80 8)), (3005, b64 (paramWord L 144 8)),
   (3054, b64 ((paramWord L 80 8 + 4 * batchOf L g) % 2 ^ 64)),
   (3056, b64 ((paramWord L 144 8 + 4 * batchOf L g) % 2 ^ 64)),
   (2958, b32 P.extra_topk), (2957, b32 P.topk),
   (484, b32 (pad64 (len0 P L g))),
   (485, b32 (total P L g)),
   (62, .pred (total P L g < 64)), (58, .pred (geBatch L g)),
   (59, .pred (ptrIsNull L 80)), (60, .pred (ptrIsNull L 144)),
   (61, .pred (totalGt63 P L g)),
   -- the query load and the shared window
   (3006, .ptr 64 true (.param (param "1")) 0),
   (810, sb L 0), (811, b32 (qTmaAddr L)), (812, b32 0),
   (813, sb L (qDstOff 1)), (814, b32 (qCoord 1)), (815, sb L (qDstOff 2)), (816, b32 (qCoord 2)),
   (817, sb L (qDstOff 3)), (818, b32 (qCoord 3)), (819, sb L (qDstOff 4)), (820, b32 (qCoord 4)),
   (821, sb L (qDstOff 5)), (822, b32 (qCoord 5)), (823, sb L (qDstOff 6)), (824, b32 (qCoord 6)),
   (825, sb L (qDstOff 7)), (826, b32 (qCoord 7)), (827, b32 65536), (828, b32 10000000),
   (3058, b64 (P.param1Base + qMapOff)), (3059, b64 qCachePolicy), (3076, b64 (qDescLo L)),
   (843, b32 (qUtccpAddr L)),
   -- the sixteen copies' destination columns (copy 0 is `%r320`, copy 8 is `%r322`)
   (829, b32 (qCopyCol 1)), (830, b32 (qCopyCol 2)), (831, b32 (qCopyCol 3)),
   (832, b32 (qCopyCol 4)), (833, b32 (qCopyCol 5)), (834, b32 (qCopyCol 6)),
   (835, b32 (qCopyCol 7)), (836, b32 (qCopyCol 9)), (837, b32 (qCopyCol 10)),
   (838, b32 (qCopyCol 11)), (839, b32 (qCopyCol 12)), (840, b32 (qCopyCol 13)),
   (841, b32 (qCopyCol 14)), (842, b32 (qCopyCol 15)),
   -- the P tile's descriptors
   (3093, pDesc L 0), (3096, pDesc L 1), (3099, pDesc L 2), (3102, pDesc L 3),
   -- the ring of block i
   (152, b16 par), (879, b32 par), (855, b32 (dequantAddr L d.i)), (856, b32 10000000),
   (887, b32 (L.sharedBase + 8 * ph)),
   (888, b32 (if ph = 0 then 4294967295 else 4294967294)),
   (2959, b32 (i32Bits ((d.i : Int) - (blocks P L g : Int)))),
   (2960, b32 d.i), (2961, b32 ph), (63, .pred (d.i != 0)),
   (453, b16 par),
   (65, .pred (d.i + 1 != blocks P L g)),
   (877, b32 (qkDoneAddr L d.i)), (878, b32 (soReadyAddr L d.i)), (883, b32 (svDoneAddr L d.i)),
   -- the QK MMAs: P, Q columns, descriptors and enable predicates
   (857, b32 tmemP), (858, b32 tmemQ), (859, b32 qkIdesc), (860, b32 tmemO),
   (861, b32 (qkACol 1)), (863, b32 (qkACol 2)), (864, b32 (qkACol 3)),
   (865, b32 (qkACol 4)), (866, b32 (qkACol 5)), (867, b32 (qkACol 6)),
   (868, b32 (qkACol 7)), (869, b32 (qkACol 8)), (870, b32 (qkACol 9)),
   (871, b32 (qkACol 10)), (872, b32 (qkACol 11)), (873, b32 (qkACol 12)),
   (874, b32 (qkACol 13)), (875, b32 (qkACol 14)), (876, b32 (qkACol 15)),
   (862, b32 1), (4091, .pred false),
   (4092, .pred true), (4093, .pred true), (4094, .pred true), (4095, .pred true),
   (4096, .pred true), (4097, .pred true), (4098, .pred true), (4099, .pred true),
   (4100, .pred true), (4101, .pred true), (4102, .pred true), (4103, .pred true),
   (4104, .pred true), (4105, .pred true), (4106, .pred true),
   (3105, b64 (descLo (kvBase L d.i))),
   (892, b32 (descLo (kvBase L d.i) + 65536)),
   (893, b32 1073758272),
   (3077, kDesc L d.i (qkBDelta 0)), (3078, kDesc L d.i (qkBDelta 1)),
   (3079, kDesc L d.i (qkBDelta 2)), (3080, kDesc L d.i (qkBDelta 3)),
   (3081, kDesc L d.i (qkBDelta 4)), (3082, kDesc L d.i (qkBDelta 5)),
   (3083, kDesc L d.i (qkBDelta 6)), (3084, kDesc L d.i (qkBDelta 7)),
   (3085, kDesc L d.i (qkBDelta 8)), (3086, kDesc L d.i (qkBDelta 9)),
   (3087, kDesc L d.i (qkBDelta 10)), (3088, kDesc L d.i (qkBDelta 11)),
   (3089, kDesc L d.i (qkBDelta 12)), (3090, kDesc L d.i (qkBDelta 13)),
   (3091, kDesc L d.i (qkBDelta 14)), (3092, kDesc L d.i (qkBDelta 15)),
   -- the PV MMAs: O columns, the V descriptors and the accumulate predicates
   (880, b32 pvIdesc), (881, b32 (if d.i = 0 then 0 else 1)), (882, b32 (tmemO + 128)),
   (4108, .pred (d.i != 0)), (4109, .pred (d.i != 0)),
   (4110, .pred true), (4111, .pred true), (4112, .pred true), (4113, .pred true),
   (4114, .pred true), (4115, .pred true),
   (909, b32 (descLo (kvBase L d.i) + 33554432)), (910, b32 1073758272),
   (3094, vDesc L d.i (pvBDelta 0)), (3095, vDesc L d.i (pvBDelta 1)),
   (3097, vDesc L d.i (pvBDelta 2)), (3098, vDesc L d.i (pvBDelta 3)),
   (3100, vDesc L d.i (pvBDelta 4)), (3101, vDesc L d.i (pvBDelta 5)),
   (3103, vDesc L d.i (pvBDelta 6)), (3104, vDesc L d.i (pvBDelta 7)),
   -- the role's end
   (918, b32 12), (919, b32 384),
   (3060, qCopyDesc L 0), (3061, qCopyDesc L 1), (3062, qCopyDesc L 2),
   (3063, qCopyDesc L 3), (3064, qCopyDesc L 4), (3065, qCopyDesc L 5),
   (3066, qCopyDesc L 6), (3067, qCopyDesc L 7), (3068, qCopyDesc L 8),
   (3069, qCopyDesc L 9), (3070, qCopyDesc L 10), (3071, qCopyDesc L 11),
   (3072, qCopyDesc L 12), (3073, qCopyDesc L 13), (3074, qCopyDesc L 14),
   (3075, qCopyDesc L 15)]

/-- The value of a register at a site: the table's, or zero for a register the role does not
track. -/
def valueOf (P : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values P L g d).lookup r).getD (b32 0)

/-- The registers live at `pc`, with the table's values. -/
def factsAt (P : Params) (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  factsFrom (Flow.live pc) (valueOf P L g d)

/-- The facts of a site. -/
abbrev facts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsAt P L g d.site.pc d

/-! ## The invariant -/

/-- The sites one block iteration runs, from the dequant wait to the PV commit. -/
def LoopSite : Site → Prop
  | .kvWait | .kvFence | .qkMma _ | .qkCommit | .soWait | .soFence | .pvMma _ | .pvCommit =>
    True
  | _ => False

/-- The sites before the block loop: the warpgroup-1 head, the election, the length reads and
the query load. A state of one of these sites has not entered the loop yet. -/
def PrefixSite : Site → Prop
  | .head | .elect | .loadTopk | .loadExtra | .qLoad _ | .qArrive | .qWait | .qFence
  | .qCopy _ | .qCopyCommit | .qCopyWait | .qCopyFence => True
  | _ => False

theorem prefix_not_loop {s : Site} (h : PrefixSite s) : ¬ LoopSite s := by
  cases s <;> first | exact h.elim | (intro hl; exact hl)

theorem prefix_not_outBar {s : Site} (h : PrefixSite s) : s ≠ .outBar := by
  rintro rfl
  exact h

theorem loop_not_prefix {s : Site} (h : LoopSite s) : ¬ PrefixSite s := by
  cases s <;> first | exact h.elim | (intro hl; exact hl)

theorem loop_not_outBar {s : Site} (h : LoopSite s) : s ≠ .outBar := by
  rintro rfl
  exact h

/-- The role's loop invariant. -/
structure Inv (P : Params) (L : Launch) (g : Nat) (d : D) : Prop where
  /-- The thread is warp 4 of warpgroup 1. -/
  warp : warpOf L g = 4
  /-- The thread's lane in its warp. -/
  lane : laneOf L g < 32
  /-- The padded block count is positive. -/
  blocks_pos : 0 < blocks P L g
  /-- The block iteration is at most the block count. -/
  i_le : d.i ≤ blocks P L g
  /-- A loop state runs a block of the padded list. -/
  i_lt : LoopSite d.site → d.i < blocks P L g
  /-- A state before the block loop has not entered it: its iteration is block 0. -/
  prefix_i : PrefixSite d.site → d.i = 0
  /-- The role's loop-end state is reached after the last block. The `exit` site is also
  reached directly from the batch-grid test at pc 1860, where the loop never ran. -/
  end_i : d.site = .outBar → d.i = blocks P L g
  /-- The Q descriptor is the launch's query map at `param_1 + 128`. -/
  qmap : L.tensorMaps (P.param1Base + qMapOff) =
    some ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩
  /-- The QK instruction descriptor decodes to the QK MMA. -/
  qk_desc : TcMma.decode .one true .f16 qkIdesc = some qkDescriptor
  /-- The PV instruction descriptor decodes to the PV MMA. -/
  pv_desc : TcMma.decode .one true .f16 pvIdesc = some pvDescriptor
  /-- The Tensor-Memory allocation starts at column 0. -/
  tmem_base : tmemBase = 0
  /-- The Q, P and O column ranges fit the 512 allocated columns. -/
  tmem_ranges : tmemO + 256 ≤ tmemQ ∧ tmemQ + 128 ≤ tmemP ∧ tmemP + 64 ≤ tmemAlloc

theorem init_inv {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hw : warpOf L g = 4) : Inv P L g init := by
  refine ⟨hw, Nat.mod_lt _ (by decide), blocks_pos P L g, Nat.zero_le _, ?_, ?_, ?_,
    hpre.mapQBind, qkIdesc_decode, pvIdesc_decode, rfl, by decide⟩
  · intro h
    exact absurd h (by simp [init, LoopSite])
  · intro _
    rfl
  · intro h
    exact absurd h (by simp [init])

/-- A change of the next site keeps the iteration and re-establishes the loop bounds. -/
theorem inv_prefix {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d)
    (hs : PrefixSite d.site) {s : Site} (hs' : PrefixSite s) :
    Inv P L g { d with site := s } := by
  refine ⟨h.warp, h.lane, h.blocks_pos, h.i_le, ?_, ?_, ?_, h.qmap, h.qk_desc, h.pv_desc,
    h.tmem_base, h.tmem_ranges⟩
  · intro hl
    exact absurd hl (prefix_not_loop hs')
  · intro _
    exact h.prefix_i hs
  · intro ho
    exact absurd ho (prefix_not_outBar hs')

/-- A change of the next site inside the loop keeps the iteration. -/
theorem inv_loop {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d)
    (hs : LoopSite d.site) {s : Site} (hs' : LoopSite s) :
    Inv P L g { d with site := s } := by
  refine ⟨h.warp, h.lane, h.blocks_pos, h.i_le, ?_, ?_, ?_, h.qmap, h.qk_desc, h.pv_desc,
    h.tmem_base, h.tmem_ranges⟩
  · intro _
    exact h.i_lt hs
  · intro hp
    exact absurd hp (loop_not_prefix hs')
  · intro ho
    exact absurd ho (loop_not_outBar hs')

/-! ## The successor relation -/

/-- The next site of an index-`k` site of a family of `n`: the next index, or the site after
the family. -/
def nextSite (n : Nat) (next : Site) (k : Nat) (make : Fin n → Site) : Site :=
  if h : k + 1 < n then make ⟨k + 1, h⟩ else next

/-- The abstract successor after event `e`. A shuffle continues only on the warp's own index
(the lane-0 broadcast); the election continues into the body only for the elected lane, and the
other lanes leave the machine at the idle role's entry. The `.nc` reads continue only on the
length the launch's premise gives; the mbarrier waits retry; the block loop advances the phase
and ends at `i = blocks`. -/
def next (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .head =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      if recv = b32 (warpOf L g) then some (some { d with site := .elect }) else some none
    | _ => none
  | .elect =>
    match e.kind with
    | .elect _ _ ld =>
      if laneOf L g = ld then some (some { d with site := startSite P L g }) else some none
    | _ => none
  | .loadTopk =>
    match e.kind with
    | .nc _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v = b32 (P.topkLen (eOf L g)) then some (some { d with site := afterTopk L })
        else some none
      | .error _ => none
    | _ => none
  | .loadExtra =>
    match e.kind with
    | .nc _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v = b32 (P.extraTopkLen (eOf L g)) then some (some { d with site := .qLoad 0 })
        else some none
      | .error _ => none
    | _ => none
  | .qLoad k => some (some { d with site := nextSite 8 .qArrive k.val .qLoad })
  | .qArrive => some (some { d with site := .qWait })
  | .qWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .qFence } else d))
    | _ => none
  | .qFence => some (some { d with site := .qCopy 0 })
  | .qCopy k => some (some { d with site := nextSite 16 .qCopyCommit k.val .qCopy })
  | .qCopyCommit => some (some { d with site := .qCopyWait })
  | .qCopyWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .qCopyFence } else d))
    | _ => none
  | .qCopyFence =>
    some (some { d with site := if total P L g < 64 then .outBar else .kvWait })
  | .kvWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .kvFence } else d))
    | _ => none
  | .kvFence => some (some { d with site := .qkMma 0 })
  | .qkMma k => some (some { d with site := nextSite 16 .qkCommit k.val .qkMma })
  | .qkCommit => some (some { d with site := .soWait })
  | .soWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .soFence } else d))
    | _ => none
  | .soFence => some (some { d with site := .pvMma 0 })
  | .pvMma k => some (some { d with site := nextSite 8 .pvCommit k.val .pvMma })
  | .pvCommit =>
    if d.i + 1 < blocks P L g then some (some { site := .kvWait, i := d.i + 1 })
    else some (some { site := .outBar, i := d.i + 1 })
  | .outBar => some (some { d with site := .exit })
  | .exit => none

/-- The role's code machine. -/
def code (P : Params) (L : Launch) (g : Nat) : PTX.Flow.Code kernel asms L g where
  D := D
  init := init
  pc := fun d => d.site.pc
  facts := fun d => facts P L g d
  inv := Inv P L g
  next := fun d e => next P L g d e

/-! ## The sites are event instructions -/

/-- Every pc of `eventPcs` holds an unguarded event instruction. -/
theorem eventPcs_ok :
    eventPcs.all (fun pc => match codeAt pc with
      | some i => !i.op.isLocal && i.guard.isNone
      | none => false) = true := by
  decide +kernel

/-- A site's pc is one of the role's event pcs. -/
theorem mem_eventPcs (s : Site) : s.pc ∈ eventPcs := by
  cases s with
  | qLoad k => fin_cases k <;> decide
  | qCopy k => fin_cases k <;> decide
  | qkMma k => fin_cases k <;> decide
  | pvMma k => fin_cases k <;> decide
  | head => decide
  | elect => decide
  | loadTopk => decide
  | loadExtra => decide
  | qArrive => decide
  | qWait => decide
  | qFence => decide
  | qCopyCommit => decide
  | qCopyWait => decide
  | qCopyFence => decide
  | kvWait => decide
  | kvFence => decide
  | qkCommit => decide
  | soWait => decide
  | soFence => decide
  | pvCommit => decide
  | outBar => decide
  | exit => decide

/-- **Every site is an unguarded event instruction**: the site's pc holds an instruction that
performs an event and has no guard, so the machine's guard obligation is immediate. -/
theorem site_event (P : Params) (L : Launch) (g : Nat) (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      PTX.Flow.Code.GuardTrue (facts P L g d) ins.guard := by
  have hok := List.all_eq_true.mp eventPcs_ok d.site.pc (mem_eventPcs d.site)
  rcases h : codeAt d.site.pc with _ | ins
  · rw [h] at hok
    exact absurd hok (by decide)
  · rw [h] at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hok
    exact ⟨ins, h, hok.1, by rw [hok.2]; trivial⟩

/-! ## The hand-off facts of the warpgroup-1 head

The warp-index broadcast at pc 1843 leaves the warp index in `%r558`; the three tests read it
and branch. The tables below are the registers those tests and each role's entry need. -/

/-- The facts at pc 1844, after the warp-index broadcast: the broadcast value `w` in `%r558`
and the warp index `%r6`, with the prologue's launch reads. -/
abbrev headFacts (L : Launch) (g : Nat) (w : Nat) : List (Nat × Value) :=
  [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
   (464, b32 w), (466, b32 (laneOf L g)),
   (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (558, b32 w), (10, .pred true)]

/-- The facts at pc 1845, after `%p11 = (%r100 == 7)`. -/
abbrev facts1845 (L : Launch) (g w : Nat) (b11 : Bool) : List (Nat × Value) :=
  [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
   (464, b32 w), (466, b32 (laneOf L g)),
   (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (558, b32 w), (11, .pred b11)]

/-- The facts at pc 1847, after `%p12 = (%r100 == 5)`. -/
abbrev facts1847 (L : Launch) (g w : Nat) (b11 b12 : Bool) : List (Nat × Value) :=
  [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
   (464, b32 w), (466, b32 (laneOf L g)),
   (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (558, b32 w), (11, .pred b11), (12, .pred b12)]

/-- The facts at pc 1849, after `%p13 = (%r100 != 4)`. -/
abbrev facts1849 (L : Launch) (g w : Nat) (b11 b12 b13 : Bool) : List (Nat × Value) :=
  [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
   (464, b32 w), (466, b32 (laneOf L g)),
   (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (558, b32 w), (11, .pred b11), (12, .pred b12), (13, .pred b13)]

/-- The facts at pc 1857 of a lane the election did not choose: the tests left the warp index
in `%r558`, and the elected-lane flag `%r335` is zero. -/
abbrev idleFacts (L : Launch) (g : Nat) (w : Nat) : List (Nat × Value) :=
  [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
   (464, b32 w), (466, b32 (laneOf L g)),
   (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (57, .pred true)]

/-- Facts of a list hold as facts of a sublist. -/
theorem holds_of_facts {R : Nat → Option Value} {F G : List (Nat × Value)}
    (h : Holds R F) (hsub : ∀ p ∈ G, p ∈ F) : Holds R G := by
  induction G with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨r, v⟩ := p
    exact ⟨holds_mem h (hsub _ (by simp)), ih fun q hq => hsub q (by simp [hq])⟩

section
variable (L : Launch)
include L

/-- The warp test of pc 1844 for warp 7: the predicate `%p11` is true. -/
theorem step_setp11_7 (g : Nat) {t : TState} (h : At t 1844 (headFacts L g 7)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 1845 (facts1845 L g 7 true) := by
  seg_fp h using decide

/-- The warp test of pc 1844 for warp 5: the predicate `%p11` is false. -/
theorem step_setp11_5 (g : Nat) {t : TState} (h : At t 1844 (headFacts L g 5)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 1845 (facts1845 L g 5 false) := by
  seg_fp h using decide

/-- The warp test of pc 1844 for warp 6: the predicate `%p11` is false. -/
theorem step_setp11_6 (g : Nat) {t : TState} (h : At t 1844 (headFacts L g 6)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 1845 (facts1845 L g 6 false) := by
  seg_fp h using decide

/-- The warp test of pc 1846 for warp 5: the predicate `%p12` is true. -/
theorem step_setp12_5 (g : Nat) {t : TState} (h : At t 1846 (facts1845 L g 5 false)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 1847 (facts1847 L g 5 false true) := by
  seg_fp h using decide

/-- The warp test of pc 1846 for warp 6: the predicate `%p12` is false. -/
theorem step_setp12_6 (g : Nat) {t : TState} (h : At t 1846 (facts1845 L g 6 false)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 1847 (facts1847 L g 6 false false) := by
  seg_fp h using decide

/-- The warp test of pc 1848 for warp 6: the predicate `%p13` is true. -/
theorem step_setp13_6 (g : Nat) {t : TState} (h : At t 1848 (facts1847 L g 6 false false)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 1849 (facts1849 L g 6 false false true) := by
  seg_fp h using decide

/-- A guarded branch of the head, taken or not, is one local step. -/
theorem head_branch (g : Nat) {t : TState} {F : List (Nat × Value)} {pc target p : Nat}
    {pick : Bool} (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc F) (hp : (p, .pred pick) ∈ F) (hadd : t.pc ∉ paramAdds)
    (hpre : t.pc ∉ prefetchTensorMapSites) (hA : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (if pick then target else pc + 1) F :=
  run_bra hc pick h (holds_mem h.2.2.2.2 hp)
    (fun a ha => _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.asms_localRule_bra
      (L := L) (g := g) (t := t) hadd hpre a ha)
    hA
end

/-- The facts of the idle role's entry at pc 2587, from the head's facts: its live registers
are `%r2` and `%rd2`, whose values the prologue's table gives. -/
theorem idle_entry_regs {L : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (h : Holds t.regs F) (hval : ∀ r ∈ Flow.live 2587,
      (r, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g r) ∈ F) :
    Holds t.regs (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.entryFacts L g) := by
  rw [show _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.entryFacts L g =
      factsFrom (Flow.live 2587)
        (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g) from rfl]
  refine holds_of_facts h fun p hp => ?_
  simp only [factsFrom, List.mem_map] at hp ⊢
  obtain ⟨r, hr, rfl⟩ := hp
  exact hval r hr

/-- **The dispatch hands warp 6 to the idle loop**: the three warp tests and the branch at
1849 reach `Wg1Idle.Entry` at pc 2587. -/
theorem handoff_idle {L : Launch} {g : Nat} {t : TState}
    (h : At t 1844 (headFacts L g 6)) :
    ∃ t', run kernel asms L g 6 t = some t' ∧
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Entry L g t' := by
  obtain ⟨t1, hr1, h1⟩ := step_setp11_6 L g h
  obtain ⟨t2, hr2, h2⟩ := head_branch L g (pc := 1845) (target := 2332) (p := 11)
    (pick := false) Flow.code_1845 h1 (by simp [facts1845])
    (by rw [h1.1]; decide) (by rw [h1.1]; decide)
  obtain ⟨t3, hr3, h3⟩ := step_setp12_6 L g h2
  obtain ⟨t4, hr4, h4⟩ := head_branch L g (pc := 1847) (target := 2162) (p := 12)
    (pick := false) Flow.code_1847 h3 (by simp [facts1847])
    (by rw [h3.1]; decide) (by rw [h3.1]; decide)
  obtain ⟨t5, hr5, h5⟩ := step_setp13_6 L g h4
  obtain ⟨t6, hr6, h6⟩ := head_branch L g (pc := 1849) (target := 2587) (p := 13)
    (pick := true) Flow.code_1849 h5 (by simp [facts1849])
    (by rw [h5.1]; decide) (by rw [h5.1]; decide)
  refine ⟨t6, run_comp (run_comp (run_comp (run_comp (run_comp hr1 hr2) hr3) hr4) hr5) hr6,
    ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, ?_⟩⟩
  exact idle_entry_regs h6.2.2.2.2 fun r hr => by
    rw [show Flow.live 2587 = [460, 2991] from by decide +kernel] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [facts1849, batchOf_eq_ctaidY,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit,
        Option.getD_some]
    · simp [facts1849, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit,
        Option.getD_some]

/-- **The unelected lanes join the idle loop**: at the branch of pc 1857 (`%p57`, the negation
of the elected-lane flag) the thread reaches `Wg1Idle.Entry` at pc 2587. -/
theorem handoff_unelected {L : Launch} {g : Nat} {t : TState}
    (h : At t 1857 (idleFacts L g 6)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Entry L g t' := by
  obtain ⟨t1, hr1, h1⟩ := head_branch L g (pc := 1857) (target := 2587) (p := 57)
    (pick := true) Flow.code_1857 h (by simp [idleFacts])
    (by rw [h.1]; decide) (by rw [h.1]; decide)
  refine ⟨t1, hr1, ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, ?_⟩⟩
  exact idle_entry_regs h1.2.2.2.2 fun r hr => by
    rw [show Flow.live 2587 = [460, 2991] from by decide +kernel] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [idleFacts, batchOf_eq_ctaidY,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit,
        Option.getD_some]
    · simp [idleFacts, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit,
        Option.getD_some]

/-! ## The warp-index broadcast

The head's first event is the broadcast of the warp index from lane 0. The template reads the
thread's `%r6`; the machine continues only when the value received is the thread's own warp
index, so the three tests below select the warp's role. -/

/-- The shuffle template of pc 1843 reads the thread's warp index `%r6` and continues with the
value lane 0 broadcasts. -/
theorem event_head (P : Params) (L : Launch) (g : Nat) {t : TState}
    (h : At t 1843 (facts P L g init)) (hb : L.block % 32 = 0) :
    eventTmpl asms L g t
        (.warp ⟨.shfl .idx, some (.int .b 32), [some 558, some 10],
          [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩) =
      .shfl .idx (b32 (warpOf L g)) 0 31
        (fun recv ok => PTX.next (setReg (setReg t 558 recv) 10 (.pred ok))) := by
  have hr : t.regs 464 = some (b32 (warpOf L g)) := by
    have hm := holds_mem h.2.2.2.2
      (mem_factsFrom (val := valueOf P L g init) (r := 464) (by
        show (464 : Nat) ∈ Flow.live 1843
        rw [show Flow.live 1843 = [459, 460, 461, 464, 466, 2990, 2991] from by decide +kernel]
        simp))
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hrule : WarpInstr.rule ⟨.shfl .idx, some (.int .b 32), [some 558, some 10],
      [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩ = some .threadShfl := rfl
  simp only [eventTmpl, warpTmpl, hrule, shflTmpl, readValue, readReg, hr, readBits, b32,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 by decide]
  simp [hb, Value.bytes]
  decide

/-- After the broadcast the thread is at pc 1844 with the value lane 0 sent in `%r558`. -/
theorem at_after_head (P : Params) (L : Launch) (g : Nat) {t : TState} {recv : Value}
    {ok : Bool} (h : At t 1843 (facts P L g init)) (hrecv : recv = b32 (warpOf L g)) :
    At (PTX.next (setReg (setReg t 558 recv) 10 (.pred ok))) 1844
      [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
       (466, b32 (laneOf L g)), (558, b32 (warpOf L g)),
       (2990, .ptr 64 false (.param (param "1")) 0),
       (2991, .ptr 64 false (.param (param "0")) 0)] := by
  subst hrecv
  have hlive : Flow.live 1843 = [459, 460, 461, 464, 466, 2990, 2991] := by decide +kernel
  have hv : ∀ r ∈ [459, 460, 461, 464, 466, 2990, 2991],
      t.regs r = some (valueOf P L g init r) := by
    intro r hr
    exact holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g init) (by
      show r ∈ Flow.live 1843
      rw [hlive]; exact hr))
  have h459 : t.regs 459 = some (b32 (queryOf L g)) := by
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hv 459 (by simp)
  have h460 : t.regs 460 = some (b32 (batchOf L g)) := by
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hv 460 (by simp)
  have h461 : t.regs 461 = some (b32 (tidOf L g)) := by
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hv 461 (by simp)
  have h466 : t.regs 466 = some (b32 (laneOf L g)) := by
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hv 466 (by simp)
  have h2990 : t.regs 2990 = some (.ptr 64 false (.param (param "1")) 0) := by
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hv 2990 (by simp)
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hv 2991 (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [PTX.next, setReg] using h.1
  · simpa [PTX.next, setReg] using h.2.1
  · simpa [PTX.next, setReg] using h.2.2.1
  · simpa [PTX.next, setReg] using h.2.2.2.1
  · simpa [PTX.next, setReg] using h459
  · simpa [PTX.next, setReg] using h460
  · simpa [PTX.next, setReg] using h461
  · simpa [PTX.next, setReg] using h466
  · simp [PTX.next, setReg]
  · simpa [PTX.next, setReg] using h2990
  · simpa [PTX.next, setReg] using h2991

/-- `at_after_head` at the role's warp 4: the broadcast value is `b32 4`. -/
theorem at_after_head4 (P : Params) (L : Launch) (g : Nat) {t : TState} {ok : Bool}
    (h : At t 1843 (facts P L g init)) (hw : warpOf L g = 4) :
    At (PTX.next (setReg (setReg t 558 (b32 4)) 10 (.pred ok))) 1844
      [(459, b32 (queryOf L g)), (460, b32 (batchOf L g)), (461, b32 (tidOf L g)),
       (466, b32 (laneOf L g)), (558, b32 4),
       (2990, .ptr 64 false (.param (param "1")) 0),
       (2991, .ptr 64 false (.param (param "0")) 0)] := by
  have h' := at_after_head P L g (recv := b32 (warpOf L g)) (ok := ok) h rfl
  rw [hw] at h'
  exact h'

/-- **The head's step**: the broadcast of pc 1843 continues, for warp 4, at the election of
pc 1853; a value other than the thread's warp index ends the machine. -/
theorem step_head {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    (code P L g).StepAt ⟨.head, 0⟩ := by
  constructor
  · intro _
    exact ⟨_, Flow.code_1843, rfl, trivial⟩
  · intro t e u ins hat hinv hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1843)
    have hb : L.block % 32 = 0 := by rw [hpre.block]
    rw [event_head P L g hat hb] at hf
    obtain ⟨recv, ok, he, hu⟩ := hf
    have hu' : u = PTX.next (setReg (setReg t 558 recv) 10 (.pred ok)) := Option.some.inj hu
    by_cases hrecv : recv = b32 (warpOf L g)
    · have hnext : next P L g ⟨.head, 0⟩ e = some (some ⟨.elect, 0⟩) := by
        rw [he]
        simp only [next]
        rw [ite_eq_left hrecv]
      obtain ⟨t', hr', hat'⟩ : ∃ t', run kernel asms L g 9
          (PTX.next (setReg (setReg t 558 (b32 4)) 10 (.pred ok))) = some t' ∧
          At t' 1853 (facts P L g ⟨.elect, 0⟩) := by
        seg_fp (at_after_head4 P L g hat hinv.warp) using
          (simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some]; decide)
      refine Or.inl (Or.inr ⟨⟨.elect, 0⟩, t', hnext, ?_, ?_⟩)
      · rw [hu', hrecv, hinv.warp]
        exact run_rtg hr'
      · refine ⟨hat', hinv.warp, hinv.lane, hinv.blocks_pos, hinv.i_le, ?_, ?_, ?_, hinv.qmap,
          hinv.qk_desc, hinv.pv_desc, hinv.tmem_base, hinv.tmem_ranges⟩
        · intro h
          exact absurd h (by simp [LoopSite])
        · intro _
          rfl
        · intro h
          exact absurd h (by simp)
    · have hnext : next P L g ⟨.head, 0⟩ e = some none := by
        rw [he]
        simp only [next]
        rw [ite_eq_right hrecv]
      exact Or.inl (Or.inl hnext)

/-! ## The entry and the machine's soundness -/

/-- The hand-off state of the role: thread `t` is about to execute the warp-index broadcast at
pc 1843, with the prologue's registers live there. The prologue's machine stops at the
`setmaxnreg.dec 72` of pc 1842; a run of that event from its hand-off facts reaches this state. -/
structure Entry (P : Params) (L : Launch) (g : Nat) (t : TState) : Prop where
  /-- The thread is at pc 1843, before the warp-index broadcast. -/
  pc : t.pc = 1843
  /-- The state is at an instruction boundary. -/
  sub : t.sub = 0
  acc : t.acc = []
  fault : t.fault = none
  /-- The thread is warp 4 of warpgroup 1, the MMA warp. -/
  warp : warpOf L g = 4
  /-- The prologue's launch reads and the two parameter-space addresses. -/
  regs : Holds t.regs (facts P L g init)

theorem Entry.at {P : Params} {L : Launch} {g : Nat} {t : TState} (h : Entry P L g t) :
    At t 1843 (facts P L g init) :=
  ⟨h.pc, h.sub, h.acc, h.fault, h.regs⟩

/-- The hand-off is already the machine's initial state. -/
theorem start_of_entry {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) {t : TState} (hentry : Entry P L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (code P L g).init t' ∧ (code P L g).inv (code P L g).init :=
  ⟨t, .refl, hentry.at, init_inv hpre hentry.warp⟩

/-- The site half of `StepAt` for every state: a state sits at an unguarded event
instruction. -/
theorem stepAt_site (P : Params) (L : Launch) (g : Nat) (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      PTX.Flow.Code.GuardTrue (facts P L g d) ins.guard :=
  site_event P L g d

/-! ## The per-site steps

Each site's `StepAt.step` has the same shape: invert the event's template, name the successor,
and evaluate the local instructions between the event and the next site. The local segments are
`seg_fp` runs whose written registers take the value table's forms. -/

/-- The per-event obligation of a state, as `Code.StepAt.step` states it. -/
abbrev Step (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) (u : TState) : Prop :=
  ((code P L g).next d e = some none ∨
      ∃ d' t', (code P L g).next d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
    ((code P L g).next d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-- **`Code.StepAt` from the per-event continuation**: the site obligation is `site_event`. -/
theorem stepAt_of (P : Params) (L : Launch) (g : Nat) (d : D)
    (h : ∀ {t : TState} {e : Event} {u : TState} (ins : Instr),
      (code P L g).AtD d t → Inv P L g d → kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → Step P L g d e u) :
    (code P L g).StepAt d :=
  ⟨fun _ => site_event P L g d, h⟩

/-- The `AtD` of a state is `At` at the site's pc with the site's facts. -/
theorem atD_at {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : (code P L g).AtD d t) : At t d.site.pc (facts P L g d) := h

/-- The state after a site's event, with the site's facts. -/
theorem at_next {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : (code P L g).AtD d t) : At (PTX.next t) (d.site.pc + 1) (facts P L g d) :=
  At.next (atD_at h)

/-- A concrete state of a state's site is the machine's `Good`. -/
theorem good_of_at {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : At t d.site.pc (facts P L g d)) (hi : Inv P L g d) : (code P L g).Good (some d) t :=
  ⟨h, hi⟩

/-- A tracked register live at the state's site holds the table's value. -/
theorem atD_reg {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : (code P L g).AtD d t) {pc r : Nat} (hpc : d.site.pc = pc) (hm : r ∈ Flow.live pc) :
    t.regs r = some (valueOf P L g d r) := by
  subst hpc
  exact holds_mem (atD_at h).2.2.2.2 (mem_factsFrom hm)

/-- A register that is not live at the state's site is not among its facts. -/
theorem facts_ne {P : Params} {L : Launch} {g : Nat} {d : D} {pc r : Nat}
    (hpc : d.site.pc = pc) (h : r ∉ Flow.live pc) :
    ∀ p ∈ facts P L g d, p.1 ≠ r := by
  subst hpc
  exact not_mem_factsFrom (val := valueOf P L g d) h

/-- **A step whose event continues at the next instruction**: the successor is fixed, and a
local segment from the next instruction reaches its facts. -/
theorem step_advance {P : Params} {L : Launch} {g : Nat} {d d' : D} {t u : TState} {e : Event}
    {n : Nat} (hnext : (code P L g).next d e = some (some d'))
    (hu : u = PTX.next t)
    (hseg : ∃ t', run kernel asms L g n u = some t' ∧ At t' d'.site.pc (facts P L g d'))
    (hinv : Inv P L g d') : Step P L g d e u := by
  obtain ⟨t', hr, hat⟩ := hseg
  subst hu
  exact Or.inl (Or.inr ⟨d', t', hnext, run_rtg hr, good_of_at hat hinv⟩)

/-- The value table's entries, as `simp` reduces them after a segment's evaluation. -/
macro "wg1_values" : tactic =>
  `(tactic| simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

theorem dequantAddr_eq (L : Launch) (i : Nat) :
    dequantAddr L i = L.sharedBase + 222792 + 8 * (i % 2) := by
  simp [dequantAddr, dequantOff, Nat.add_assoc]

theorem qkDoneAddr_eq (L : Launch) (i : Nat) :
    qkDoneAddr L i = L.sharedBase + 222904 + 8 * (i % 2) := by
  simp [qkDoneAddr, qkDoneOff, Nat.add_assoc]

theorem soReadyAddr_eq (L : Launch) (i : Nat) :
    soReadyAddr L i = L.sharedBase + 222920 + 8 * (i % 2) := by
  simp [soReadyAddr, soReadyOff, Nat.add_assoc]

theorem svDoneAddr_eq (L : Launch) (i : Nat) :
    svDoneAddr L i = L.sharedBase + 222936 + 8 * (i % 2) := by
  simp [svDoneAddr, svDoneOff, Nat.add_assoc]

theorem phaseOf_lt (i : Nat) : phaseOf i < 2 := by
  unfold phaseOf
  omega

theorem parOf_lt (i : Nat) : parOf i < 2 := by
  unfold parOf
  omega

theorem parOf_lt_two_pow (i : Nat) : parOf i < 2 ^ 32 := by
  have := parOf_lt i
  omega

theorem phaseOf_succ (i : Nat) : phaseOf (i + 1) = 1 - phaseOf i := by
  unfold phaseOf
  omega

theorem parOf_succ (i : Nat) : parOf (i + 1) = (if parOf i = phaseOf i then 0 else 1) := by
  have h2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
  unfold parOf phaseOf
  rcases h2 with h | h
  · have hdiv : (i + 1) / 2 = i / 2 := by
      have h1 : i + 1 = 2 * (i / 2) + 1 := by
        have hdm : 2 * (i / 2) + i % 2 = i := Nat.div_add_mod i 2
        rw [h] at hdm
        omega
      rw [h1, Nat.mul_add_div (by decide : 0 < 2) (i / 2) 1]
      rw [Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero]
    rw [hdiv, h]
    by_cases hc : i / 2 % 2 = 0
    · rw [ite_eq_left hc]
      exact hc
    · rw [ite_eq_right hc]
      have := Nat.mod_lt (i / 2) (by decide : 0 < 2)
      omega
  · have hdiv : (i + 1) / 2 = i / 2 + 1 := by
      have h1 : i + 1 = 2 * (i / 2) + 2 := by
        have hdm : 2 * (i / 2) + i % 2 = i := Nat.div_add_mod i 2
        rw [h] at hdm
        omega
      rw [h1, Nat.mul_add_div (by decide : 0 < 2) (i / 2) 2,
        show 2 / 2 = 1 by decide]
    rw [hdiv, h]
    by_cases hc : i / 2 % 2 = 1
    · rw [ite_eq_left hc, Nat.add_mod, hc]
    · rw [ite_eq_right hc, Nat.add_mod]
      have := Nat.mod_lt (i / 2) (by decide : 0 < 2)
      omega

/-- The parity toggle the kernel keeps in `%r453`: the `selp` of the current parity against the
buffer phase. -/
theorem toggle_eq (a b : Nat) : (if a != b then (1 : Nat) else 0) = if a = b then 0 else 1 := by
  by_cases h : a = b <;> simp [h]

/-- The phase bit of the next block, from the parity toggle. -/
theorem phase_succ_of_two (i : Nat) :
    (if phaseOf i = 0 then 4294967295 else 4294967294) &&& 1 = phaseOf (i + 1) := by
  rw [phaseOf_succ]
  have h := phaseOf_lt i
  rcases (by omega : phaseOf i = 0 ∨ phaseOf i = 1) with h0 | h0 <;> rw [h0] <;> decide

/-- `not.b32` of the block's phase bit. -/
private theorem not_phase (i : Nat) :
    truncBits 32 (~~~truncBits 32 (BitVec.ofNat 64 (phaseOf i))) =
      BitVec.ofNat 64 (if phaseOf i = 0 then 4294967295 else 4294967294) := by
  have hp := phaseOf_lt i
  rcases (by omega : phaseOf i = 0 ∨ phaseOf i = 1) with h0 | h1
  · rw [h0]
    decide
  · rw [h1]
    decide

/-- `not.b32` of the next block's phase bit. -/
theorem not_phase_succ (i : Nat) :
    truncBits 32 (~~~truncBits 32 (BitVec.ofNat 64 (phaseOf (i + 1)))) =
      BitVec.ofNat 64 (if phaseOf (i + 1) = 0 then 4294967295 else 4294967294) :=
  not_phase (i + 1)

/-- `descLo` of any shared offset keeps the 14 bits of the descriptor's start field. -/
theorem descLo_lt (off : Nat) : descLo off < 2 ^ 16 := by
  have h := Nat.mod_lt (off / 16) (by decide : 0 < 2 ^ 14)
  unfold descLo
  omega

/-- `or` of a low descriptor field below bit 16 with a multiple of `2 ^ 16` is a sum. -/
theorem or_shifted {x c : Nat} (hx : x < 2 ^ 16) (hc : c % 2 ^ 16 = 0) : x ||| c = x + c := by
  have hc' : c = 2 ^ 16 * (c / 2 ^ 16) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc)).symm
  rw [Nat.or_comm, hc', ← Nat.two_pow_add_eq_or_of_lt (i := 16) hx]
  omega

/-- The `or.b64` of a descriptor's low field with a constant word whose low 16 bits are clear
is the two words' sum. -/
theorem bits_or_const {x c : Nat} (hx : x < 2 ^ 16) (hc : c % 2 ^ 16 = 0) (hc64 : c < 2 ^ 64) :
    Value.bits 64 (BitVec.ofNat 64 x ||| BitVec.ofNat 64 c) = b64 (x + c) := by
  have hor : (x % 18446744073709551616 ||| c % 18446744073709551616) = x + c := by
    rw [Nat.mod_eq_of_lt (show x < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show c < 18446744073709551616 by omega)]
    exact or_shifted hx hc
  have hor2 : (BitVec.ofNat 64 x ||| BitVec.ofNat 64 c) = BitVec.ofNat 64 (x + c) := by
    rw [nf_or, hor]
  rw [hor2, b64]

/-- The same for a 32-to-64-bit conversion's truncated low field. -/
theorem bits_or_const_trunc {x c : Nat} (hx : x < 2 ^ 16) (hc : c % 2 ^ 16 = 0)
    (hc64 : c < 2 ^ 64) :
    Value.bits 64 (truncBits 64 (BitVec.ofNat 64 x) ||| BitVec.ofNat 64 c) = b64 (x + c) := by
  have h1 : truncBits 64 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
    apply BitVec.eq_of_toNat_eq
    simp [truncBits, BitVec.toNat_ofNat]
  rw [h1]
  exact bits_or_const hx hc hc64

/-- The descriptor's start field as the kernel computes it: the `mad.lo` of the ring phase and
the swizzled base, the 16-byte-unit shift and the 14-bit mask. -/
theorem descLo_word (s p : Nat) :
    ((p % 4294967296 * 65528 + (s + 8 * p) % 4294967296) % 4294967296 / 16 % 4294967296) &&&
        16383 = (s + 65536 * p) / 16 % 16384 := by
  rw [land16383, Nat.mod_mod_of_dvd _ (show 16384 ∣ 4294967296 by decide)]
  have h1 : (p % 4294967296 * 65528 + (s + 8 * p) % 4294967296) % 4294967296 =
      (s + 65536 * p) % 4294967296 := by omega
  rw [h1]
  omega

/-- `or.b64` of a start field below bit 16 with the K descriptor constant is the sum. -/
theorem or_desc {x : Nat} (hx : x < 2 ^ 16) :
    x ||| 4611756662049538048 = x + 4611756662049538048 :=
  or_shifted hx (by decide)

/-- Xor of two 64-bit patterns in the `Nat` normal form. -/
theorem nf_xor (a b : Nat) : BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b =
    BitVec.ofNat 64 (a % 18446744073709551616 ^^^ b % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : a % 18446744073709551616 ^^^ b % 18446744073709551616 < 18446744073709551616 :=
    Nat.xor_lt_two_pow (n := 64) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt h1]

/-- The `and` with the byte mask `255`. -/
theorem land255 (x : Nat) : x &&& 255 = x % 256 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 8
  rw [show (255 : Nat) = 2 ^ 8 - 1 from by decide]
  exact h

/-- The `and` with the bit mask `1`. -/
theorem land1 (x : Nat) : x &&& 1 = x % 2 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 1
  rw [show (1 : Nat) = 2 ^ 1 - 1 from by decide]
  exact h

/-- The `mul.wide.u32` at pc 1884 is unsigned: its signed branch is not taken. -/
theorem mul_wide_not_signed :
    ¬ ((((
        { op := IntOp.mul MulMode.wide, ty := DType.int IType.u 32, dsts := [some 3057],
          srcs := [Opnd.reg 460, Opnd.imm 4] } : IntInstr)).ty.kind? == some IType.s) =
        true) := by
  decide

/-- A descriptor equation whose computed side is the `or.b64` of a low field with the
descriptor constant, closed for the shared descriptor words. -/
macro "wg1_or" : tactic =>
  `(tactic| first
    | (simp only [kDesc, vDesc, pDesc, qCopyDesc]
       first
         | (apply bits_or_const (c := 4611756662049538048) <;>
            first | (simp only [descLo, qDescLo, kvBase, qCopyCol, tmemQ]; omega) | decide | omega)
         | (apply bits_or_const_trunc (c := 4611756662049538048) <;>
            first | (simp only [descLo, qDescLo, kvBase, qCopyCol, tmemQ]; omega) | decide | omega))
    | (simp only [kDesc, vDesc, pDesc, qCopyDesc]
       first
         | (apply bits_or_const (c := 4611756662083026944) <;>
            first | (simp only [descLo, qDescLo, kvBase, pvDest, tmemO]; omega) | decide | omega)
         | (apply bits_or_const_trunc (c := 4611756662083026944) <;>
            first | (simp only [descLo, qDescLo, kvBase, pvDest, tmemO]; omega) | decide | omega))
    | (simp only [kDesc, vDesc, pDesc, qCopyDesc]
       first
         | (apply bits_or_const (c := 70403108110336) <;>
            first | (simp only [descLo, qDescLo, kvBase]; omega) | decide | omega)
         | (apply bits_or_const_trunc (c := 70403108110336) <;>
            first | (simp only [descLo, qDescLo, kvBase]; omega) | decide | omega)))

/-- The role's abbreviations unfolded and the integer normal form applied. -/
macro "wg1_simpnf" : tactic =>
  `(tactic| first
    | (simp only [sb, b32, b16, Value.bits.injEq, true_and, qDstOff, qCoord, qCopyCol,
        qkACol, pvDest, tmemQ, tmemO, tmemP, descLo, kvBase, qDescLo, kDesc, vDesc, pDesc,
        qCopyDesc, phaseOf, parOf, toggle_eq, parOf_succ, phaseOf_succ, phase_succ_of_two,
        not_phase_succ, geBatch, eOf, ptrIsNull, totalGt63, pad64, total, blocks, len0, len1,
        dequantAddr_eq, qkDoneAddr_eq, soReadyAddr_eq, svDoneAddr_eq]
       nf_simp [sb, nf_xor, land255, land1, Nat.xor_self, Nat.zero_and, Nat.zero_xor,
         Nat.xor_zero]))

/-- The value normal form: first the unsigned `mul.wide` at pc 1884, whose signed branch would
otherwise leave an `ite` whose instance rewriting cannot follow. -/
macro "wg1_nf0" : tactic =>
  `(tactic| first
    | (rw [ite_eq_right mul_wide_not_signed]
       wg1_simpnf)
    | wg1_simpnf)

/-- The value normal form with the descriptor low-field sum closed. -/
macro "wg1_nf1" : tactic =>
  `(tactic| first
    | (wg1_nf0
       first
         | (rw [descLo_word]
            first
              | (rw [or_desc (by omega)]; omega)
              | omega)
         | omega))

/-- A 64-bit truncation of a 64-bit word is the word. -/
theorem trunc64_ofNat (x : Nat) : truncBits 64 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]
  omega

/-- `or.b64` of a quotient descriptor's start field with its constant, each side as the
register read truncates it. -/
theorem bitrunc_or {x c : Nat} (hx : x < 2 ^ 16) (hc : c % 2 ^ 16 = 0) (hc64 : c < 2 ^ 64) :
    Value.bits 64 (truncBits 64 (BitVec.ofNat 64 x) ||| truncBits 64 (BitVec.ofNat 64 c)) =
      b64 (x + c) := by
  rw [trunc64_ofNat, trunc64_ofNat]
  exact bits_or_const hx hc hc64

/-- `add.s64` of a descriptor's start field and a constant, each side as the register read
truncates it. -/
theorem bitrunc_add {x c : Nat} (hx : x < 2 ^ 64) (hc : c < 2 ^ 64) :
    Value.bits 64
        (truncBits 64 (truncBits 64 (BitVec.ofNat 64 x) + truncBits 64 (BitVec.ofInt 64 c))) =
      b64 (x + c) := by
  nf_simp
  omega

/-- The `mov.b64 {lo, hi}` of an MMA B descriptor: a start field plus a constant in the low
half and the descriptor's upper word in the high half. -/
theorem join_desc {base delta hi : Nat} (hb : base + delta < 2 ^ 32) (hhi : hi < 2 ^ 32) :
    joinValue
        (Value.bits 32
          (truncBits 32
            (truncBits 32 (BitVec.ofNat 64 base) + truncBits 32 (BitVec.ofInt 64 delta))))
        (b32 hi) =
      b64 (base + delta + hi * 2 ^ 32) := by
  have hx : truncBits 32
      (truncBits 32 (BitVec.ofNat 64 base) + truncBits 32 (BitVec.ofInt 64 delta)) =
      BitVec.ofNat 64 (base + delta) := by
    nf_simp
    omega
  have hy : b32 hi = Value.bits 32 (BitVec.ofNat 64 hi) := rfl
  rw [hx, hy, join_bits32 rfl rfl (by omega) hhi]
  simp only [b64]

/-- The descriptor's start field as the K tile's ring address computes it. -/
theorem descLo_word_bits (s p : Nat) :
    Value.bits 64
      (truncBits 64
        (truncBits 32
          (truncBits 32
            (if (truncBits 32 (BitVec.ofInt 64 4)).toNat ≥ 32 then 0
             else
               truncBits 32
                 (truncBits 32
                   (truncBits 32 (BitVec.ofNat 64 p) * truncBits 32 (BitVec.ofInt 64 65528) +
                    truncBits 32 (BitVec.ofNat 64 (s + 8 * p)))) >>>
                   (truncBits 32 (BitVec.ofInt 64 4)).toNat) &&&
              truncBits 32 (BitVec.ofInt 64 16383)))) =
      b64 ((s + 65536 * p) / 16 % 16384) := by
  nf_simp
  rw [descLo_word]
  rw [Nat.mod_eq_of_lt (show (s + 65536 * p) / 16 % 16384 < 4294967296 by omega),
    Nat.mod_eq_of_lt (show (s + 65536 * p) / 16 % 16384 < 18446744073709551616 by omega)]

/-- The block counter's `setp.ne` test as the table states it: the runtime compares the
32-bit word `i` with zero. -/
theorem pred_ne_zero (i : Nat) (hi : i < 2 ^ 32) :
    Value.pred (compare .ne .b 32 (truncBits 32 (BitVec.ofNat 64 i))
      (truncBits 32 (BitVec.ofInt 64 0))) = Value.pred (i != 0) := by
  nf_simp [PTX.compare]
  rw [show (i != 0) = decide (i ≠ 0) from rfl]
  rw [decide_eq_decide]
  omega

/-- The `mul.wide.u32` of the batch word by 4 and its `add.s64` to a parameter pointer word,
as pcs 1874-1875 and 1884-1885 compute them. -/
theorem mul_wide_u32_add {a n : Nat} (hn : n < 2 ^ 32) (ha : a < 2 ^ 64) :
    Value.bits 64
      (truncBits 64
        (truncBits 64 (BitVec.ofNat 64 a) +
          truncBits 64
            (if (some IType.u == some IType.s) = true then
              truncBits (2 * 32) (BitVec.ofInt 64
                (toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) *
                 toSigned 32 (truncBits 32 (BitVec.ofInt 64 4))))
            else BitVec.ofNat 64
              ((truncBits 32 (BitVec.ofNat 64 n)).toNat *
               (truncBits 32 (BitVec.ofInt 64 4)).toNat)))) =
      b64 ((a + 4 * n) % 2 ^ 64) := by
  change Value.bits 64
      (truncBits 64
        (truncBits 64 (BitVec.ofNat 64 a) +
          truncBits 64
            (BitVec.ofNat 64 ((truncBits 32 (BitVec.ofNat 64 n)).toNat *
              (truncBits 32 (BitVec.ofInt 64 4)).toNat)))) =
      b64 ((a + 4 * n) % 2 ^ 64)
  nf_simp
  omega

section diag
open Lean Elab Tactic Meta
elab "wg1_goal" : tactic => do
  let t ← Lean.Elab.Tactic.getMainTarget
  let e ← Lean.instantiateMVars t
  let s ← Lean.Meta.ppExpr e
  Lean.logInfo m!"WG1GOAL {s}"
end diag

set_option hygiene false in
/-- Close a segment's written-register equation: the stated value, by the shared window's
arithmetic, with the role's index and descriptor abbreviations unfolded. -/
macro "wg1_close" : tactic =>
  `(tactic| first
    | with_reducible rfl
    | (rw [not_phase_succ]; rfl)
    | wg1_or
    | (simp only [qCopyDesc]
       first
         | (rw [bitrunc_or (by simp only [qDescLo, descLo]; omega) (by decide) (by decide)])
         | (rw [bitrunc_add (by simp only [qDescLo, descLo]; omega) (by decide)])
       simp only [b64, Value.bits.injEq, nf_eq]
       omega)
    | (simp only [kDesc, vDesc, qkBDelta, pvBDelta]
       rw [join_desc (by simp only [descLo]; omega) (by decide)]
       simp only [b64, Value.bits.injEq, nf_eq]
       omega)
    | (exact descLo_word_bits L.sharedBase (phaseOf i))
    | join_close [sb, qDstOff, qCoord, qCopyCol, qkACol, pvDest, tmemQ, tmemO, tmemP,
        descLo, kvBase, qDescLo, kDesc, vDesc, pDesc, qCopyDesc, phaseOf, parOf,
        geBatch, eOf, ptrIsNull, totalGt63, pad64, total, blocks, len0, len1,
        dequantAddr_eq, qkDoneAddr_eq, soReadyAddr_eq, svDoneAddr_eq]
    | (first
        | with_reducible rfl
        | (show PTX.joinValue _ _ = _; simp [PTX.joinValue, PTX.Value.bytes])
        | (show PTX.Value.ptr _ _ (.param _) 0 = _; simp)
        | close_fact [sb, qDstOff, qCoord, qCopyCol, qkACol, pvDest, tmemQ, tmemO, tmemP,
            descLo, kvBase, qDescLo, kDesc, vDesc, pDesc, qCopyDesc, phaseOf, parOf,
            geBatch, eOf, ptrIsNull, totalGt63, pad64, total, blocks, len0, len1,
            dequantAddr_eq, qkDoneAddr_eq, soReadyAddr_eq, svDoneAddr_eq])
    | (split_ifs with h <;>
       first
         | (simp only [PTX.DType.kind?, kind_u_beq_s, Bool.false_eq_true] at h
            exact absurd h (by decide))
         | wg1_nf1)
    | wg1_nf1
    | wg1_goal)

/-- The shared window's base plus an offset the kernel addresses is a 32-bit word. -/
theorem sharedAddr_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) {off : Nat}
    (h : off ≤ 222952) : L.sharedBase + off < 2 ^ 32 := by
  have := sharedBase_lt hpre
  omega

/-- The shared window's base is eight-byte aligned, so an aligned offset gives an aligned
address. -/
theorem sharedAddr_align {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {off : Nat} (h : off % 8 = 0) : (L.sharedBase + off) % 8 = 0 := by
  have h8 : L.sharedBase % 8 = 0 := by
    rw [hpre.sharedBase]
    have := hpre.sharedAlignment
    omega
  omega

/-! ### The Q Tensor-Memory copy and the query load -/

/-- The `tcgen05.cp` step of the template, as the issue rule reads it. -/
theorem tcTmpl_tcCp_eq (L : Launch) (g : Nat) (t : TState) (group : CtaGroup) (shape : TcCpShape)
    (ta : Nat) (sd : Opnd) (fmt : Option TcCpFmt) :
    tcTmpl L g t (.tcCp group shape ta sd fmt) = ofExec (do
      unless g < L.threads do throw .badValue
      let a ← readBits L g t 32 (.reg ta)
      unless TcCopy.AddressOk shape a.toNat do throw .badValue
      let s ← readBits L g t 64 sd
      let some src := TcShared.decode s.toNat | throw .noRule
      let some ctas := L.ctaGroup (g / L.block) group | throw .badValue
      pure (.tc (.cp { address := a.toNat, src, shape, ctas, fmt }) (PTX.next t))) := rfl

/-- A `tcgen05.cp` that fires continues at the next instruction. -/
theorem fires_tcCp_next {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {group : CtaGroup} {shape : TcCpShape} {ta : Nat} {sd : Opnd} {fmt : Option TcCpFmt}
    {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.tcCp group shape ta sd fmt)) e (some u)) :
    u = PTX.next t := by
  have hm : PTX.EventFrame.CallbackFrame (· = PTX.next t)
      (eventTmpl A L g t (.tcCp group shape ta sd fmt)) := by
    simp only [eventTmpl, tcTmpl_tcCp_eq]
    apply PTX.EventFrame.ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply PTX.EventFrame.allOk_bind; intro v)
      | split
  exact PTX.EventFrame.callbackFrame_fires (P := (· = PTX.next t)) hm hf

/-- A fired `tcgen05.mma.ws` with A in Tensor Memory and the zero-column-mask operand
continues at the next instruction. -/
theorem fires_tcMmaTs_ws {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {dst ta : Nat} {aoff : Int} {bd id en : Opnd} {mask : List Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t
      (.tcMma { TcMmaInstr.dense .one true .f16 dst (.tmem ta aoff) bd id mask en with
        zeroColumnMask := some (.imm 0) }))
      e (some u)) :
    u = PTX.next t := by
  have hm : PTX.EventFrame.CallbackFrame (· = PTX.next t)
      (eventTmpl A L g t
        (.tcMma { TcMmaInstr.dense .one true .f16 dst (.tmem ta aoff) bd id mask en with
          zeroColumnMask := some (.imm 0) })) := by
    simp only [eventTmpl, tcTmpl, mmaTmpl, TcMmaInstr.dense, TcMmaInstr.rule]
    apply PTX.EventFrame.ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply PTX.EventFrame.allOk_bind; intro v)
      | split
  exact PTX.EventFrame.callbackFrame_fires (P := (· = PTX.next t)) hm hf

/-- A fired `tcgen05.mma.ws` with A in shared memory and the zero-column-mask operand
continues at the next instruction. -/
theorem fires_tcMma_ws {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {dst : Nat} {ad bd id en : Opnd} {mask : List Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t
      (.tcMma { TcMmaInstr.dense .one true .f16 dst (.smem ad) bd id mask en with
        zeroColumnMask := some (.imm 0) }))
      e (some u)) :
    u = PTX.next t := by
  have hm : PTX.EventFrame.CallbackFrame (· = PTX.next t)
      (eventTmpl A L g t
        (.tcMma { TcMmaInstr.dense .one true .f16 dst (.smem ad) bd id mask en with
          zeroColumnMask := some (.imm 0) })) := by
    simp only [eventTmpl, tcTmpl, mmaTmpl, TcMmaInstr.dense, TcMmaInstr.rule]
    apply PTX.EventFrame.ofExec_frame
    repeat' first
      | rfl
      | exact True.intro
      | (apply PTX.EventFrame.allOk_bind; intro v)
      | split
  exact PTX.EventFrame.callbackFrame_fires (P := (· = PTX.next t)) hm hf

/-- **The eight Q TMA issues**: the copy at each pc fires its issue, and the local instructions
that follow form the next copy's destination and coordinate. -/
theorem step_qLoad (P : Params) (L : Launch) (g i : Nat) (k : Fin 8) {mem0 : Mem0}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.qLoad k, i⟩ t)
    (hinv : Inv P L g ⟨.qLoad k, i⟩) (hc : kernel.code[(Site.qLoad k).pc]? = some ins)
    (hf : Fires (Site.qLoad k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qLoad k, i⟩ e u := by
  revert hat hinv hc hf
  fin_cases k <;> intro hat hinv hc hf
  · -- `.qLoad 0`: pc 1906, then the destination and coordinate of copy 1 (1907, 1908)
    have hpc : (Site.qLoad ⟨0, by decide⟩).pc = 1906 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_4)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1906) hf
    have h0 : At u 1907 (facts P L g ⟨.qLoad ⟨0, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1909 (facts P L g ⟨.qLoad ⟨1, by decide⟩, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qLoad ⟨1, by decide⟩, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])
  · -- `.qLoad 1`: pc 1909
    have hpc : (Site.qLoad ⟨1, by decide⟩).pc = 1909 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_5)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1909) hf
    have h0 : At u 1910 (facts P L g ⟨.qLoad ⟨1, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1912 (facts P L g ⟨.qLoad ⟨2, by decide⟩, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qLoad ⟨2, by decide⟩, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])
  · -- `.qLoad 2`: pc 1912
    have hpc : (Site.qLoad ⟨2, by decide⟩).pc = 1912 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_6)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1912) hf
    have h0 : At u 1913 (facts P L g ⟨.qLoad ⟨2, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1915 (facts P L g ⟨.qLoad ⟨3, by decide⟩, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qLoad ⟨3, by decide⟩, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])
  · -- `.qLoad 3`: pc 1915
    have hpc : (Site.qLoad ⟨3, by decide⟩).pc = 1915 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_7)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1915) hf
    have h0 : At u 1916 (facts P L g ⟨.qLoad ⟨3, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1918 (facts P L g ⟨.qLoad ⟨4, by decide⟩, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qLoad ⟨4, by decide⟩, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])
  · -- `.qLoad 4`: pc 1918
    have hpc : (Site.qLoad ⟨4, by decide⟩).pc = 1918 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_8)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1918) hf
    have h0 : At u 1919 (facts P L g ⟨.qLoad ⟨4, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1921 (facts P L g ⟨.qLoad ⟨5, by decide⟩, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qLoad ⟨5, by decide⟩, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])
  · -- `.qLoad 5`: pc 1921
    have hpc : (Site.qLoad ⟨5, by decide⟩).pc = 1921 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_9)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1921) hf
    have h0 : At u 1922 (facts P L g ⟨.qLoad ⟨5, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1924 (facts P L g ⟨.qLoad ⟨6, by decide⟩, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qLoad ⟨6, by decide⟩, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])
  · -- `.qLoad 6`: pc 1924
    have hpc : (Site.qLoad ⟨6, by decide⟩).pc = 1924 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_10)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1924) hf
    have h0 : At u 1925 (facts P L g ⟨.qLoad ⟨6, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1927 (facts P L g ⟨.qLoad ⟨7, by decide⟩, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qLoad ⟨7, by decide⟩, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])
  · -- `.qLoad 7`: pc 1927, then the arrive's byte count (1928)
    have hpc : (Site.qLoad ⟨7, by decide⟩).pc = 1927 := rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_11)
    obtain ⟨_addr, _spec, _he, hu, _loc⟩ := fires_cpTensor_issue (A := asms) (pc := 1927) hf
    have h0 : At u 1928 (facts P L g ⟨.qLoad ⟨7, by decide⟩, i⟩) := by
      rw [hu]; exact at_next hat
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
        At t' 1929 (facts P L g ⟨.qArrive, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine step_advance (d' := ⟨.qArrive, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])

/-- The `bar_q_tma` address of the Q copies. -/
theorem qTmaAddr_eq (L : Launch) : qTmaAddr L = L.sharedBase + 222776 := by
  simp [qTmaAddr, qTmaOff]

theorem qUtccpAddr_eq (L : Launch) : qUtccpAddr L = L.sharedBase + 222784 := by
  simp [qUtccpAddr, qUtccpOff]

/-- **The Q load's expect-tx arrival**: the arrival on `bar_q_tma` with 65536 bytes (pc 1929)
and the timeout register (1930) reach the wait. -/
theorem step_qArrive (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.qArrive, i⟩ t)
    (hinv : Inv P L g ⟨.qArrive, i⟩) (hc : kernel.code[(Site.qArrive).pc]? = some ins)
    (hf : Fires (Site.qArrive).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qArrive, i⟩ e u := by
  have hpc : (Site.qArrive).pc = 1929 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_3)
  have h811 : t.regs 811 = some (b32 (qTmaAddr L)) := by
    have hm := atD_reg hat (pc := 1929) (r := 811) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h827 : t.regs 827 = some (b32 65536) := by
    have hm := atD_reg hat (pc := 1929) (r := 827) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hqa : qTmaAddr L < 2 ^ 32 := by
    rw [qTmaAddr_eq]
    exact sharedAddr_lt hpre (off := 222776) (by decide)
  have hq8 : qTmaAddr L % 8 = 0 := by
    rw [qTmaAddr_eq]
    exact sharedAddr_align hpre (off := 222776) (by decide)
  obtain ⟨_rel, _sc, he, hu⟩ := fires_arrive_next (A := asms) (t := t) (base := 811) (off := 0)
    (tx := .reg 827) (count := .imm 1) (cluster := false) (rel := true) (sc := .cta)
    (pc := 1929) (e := e) (o := some u) (m := ⟨.shared, g / L.block, qTmaAddr L⟩)
    (bytes := BitVec.ofNat 64 65536) (n := BitVec.ofNat 64 1)
    (mbarLoc_b32 h811 hqa hq8) (readBits_b32 h827 (by decide))
    (by simp [readBits, pure, Except.pure]; decide) hf
  have hu' : u = PTX.next t := Option.some.inj hu
  have h0 : At u 1930 (facts P L g ⟨.qArrive, i⟩) := by
    rw [hu']; exact at_next hat
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 1931 (facts P L g ⟨.qWait, i⟩) := by
    have hbase := sharedBase_lt hpre
    seg_fp h0 using
      all_goals (try wg1_values)
      all_goals wg1_close
  refine step_advance (d' := ⟨.qWait, i⟩) ?_ hu' ⟨t', hr, ht⟩ ?_
  · simp [code, next, nextSite]
  · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])

/-! ### The local steps the assumptions do not select -/

/-- No assumption of the kernel's list has a local rule for a branch. -/
theorem asms_localRule_bra {L : Launch} {g : Nat} {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (simp only [Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
          Assumptions.lg2Exact, Assumptions.paramPointers, Assumptions.sharedBits]
         repeat' split
         all_goals rfl)

/-- No assumption of the kernel's list has a local rule for the role's `ld.param`s. -/
theorem asms_localRule_mem {L : Launch} {g : Nat} {t : TState} {a : MemAccess}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites) :
    ∀ b ∈ asms, b.localRule L g t (.mem a) = none := by
  intro b hb
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (refine Assumption.idealReal_localRule_none ?_
         intro f hf
         simp [Assumption.FloatForm.ofOp] at hf)
      | (refine Assumption.approxExact_localRule_none ?_
         intro f hf
         simp [Assumption.ApproxForm.ofOp] at hf)
      | rfl
      | (simp only [Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
          Assumptions.lg2Exact, Assumptions.sharedBits]
         repeat' split
         all_goals rfl)
      | (simp only [Assumptions.paramPointers]
         rw [ite_eq_right (by simpa using h1), ite_eq_right (by simpa using h2)])

section
variable {P : Params} {L : Launch}

/-- A local step that writes the registers `ws` with the table's values reaches the next
instruction with the table's facts. -/
theorem at_written {g : Nat} {d : D} {t t' : TState} {pc : Nat} {ws : List Nat}
    (h : At t pc (factsAt P L g pc d)) (hpc : t'.pc = pc + 1) (hs : t'.sub = t.sub)
    (ha : t'.acc = t.acc) (hf : t'.fault = t.fault)
    (hw : ∀ r ∈ ws, t'.regs r = some (valueOf P L g d r)) (hfr : ∀ r, r ∉ ws → t'.regs r = t.regs r)
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ ws ∨ r ∈ Flow.live pc) :
    At t' (pc + 1) (factsAt P L g (pc + 1) d) := by
  refine ⟨hpc, hs.trans h.2.1, ha.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr => ?_⟩
  by_cases hm : r ∈ ws
  · exact hw r hm
  · rw [hfr r hm]
    rcases hl r hr with h' | h'
    · exact absurd h' hm
    · exact holds_mem h.2.2.2.2 (mem_factsFrom h')

/-- Facts of a state hold as facts of a sublist. -/
theorem At.subset {t : TState} {pc : Nat} {F G : List (Nat × Value)}
    (h : At t pc F) (hFG : ∀ p ∈ G, p ∈ F) : At t pc G :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_of_facts h.2.2.2.2 hFG⟩

/-- An `ld.param` of one register of `param_0` through the pointer register 2991, as one step
to the next instruction's facts. -/
theorem ld_param {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {pc w off r dst : Nat} {ty : DType}
    {t' : TState} (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off r dst)⟩)
    (hrp : t.regs r = some (.ptr 64 false (.param (param "0")) 0))
    (hobj : L.paramObjects (param "0") = some (scalarsParam, P.param0Base))
    (hsup : ParamSupplied L (param "0") off (w / 8)) (hsze : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (h : At t pc (factsAt P L g pc d))
    (hv : paramElem w w (paramNat L (param "0") off (w / 8)) = valueOf P L g d dst)
    (hl : ∀ x ∈ Flow.live (pc + 1), x ∈ [dst] ∨ x ∈ Flow.live pc) (h1 : pc ∉ paramAdds)
    (h2 : pc ∉ prefetchTensorMapSites) (hw : ty.width = w := by rfl)
    (hr : (Thread.paramLoad ty off r dst).rule = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt P L g (pc + 1) d) := by
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem (Thread.paramLoad ty off r dst)) = none :=
    asms_localRule_mem (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2)
  refine ⟨_, run_local hc rfl h (Thread.exec_ldParamReg (A := asms) hrp hobj ⟨by omega, hsze⟩ hal
    hsup (Assumption.SegFreePc.of_eq h.1 (by seg_free_pc)) hL hw hr),
    at_written h ?_ rfl rfl rfl ?_ ?_ hl⟩
  · simp [setReg, PTX.next, h.1]
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [setReg, PTX.next, hv]
  · intro x hx
    simp only [List.mem_singleton] at hx
    simp [setReg, PTX.next, Function.update_of_ne hx]

/-- A guarded branch on a predicate fact, as one step to the taken or fall-through pc. -/
theorem run_bra_to {L : Launch} {g : Nat} {t : TState} {pc target p b : Nat}
    {F : List (Nat × Value)} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc F) (hp : (p, .pred pick) ∈ F)
    (hb : b = if pick then target else pc + 1)
    (hA : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' b F := by
  obtain ⟨t', hr, ht⟩ := run_bra hc pick h (holds_mem h.2.2.2.2 hp)
    (fun a ha => asms_localRule_bra (t := t) (target := target) a ha) hA
  rw [← hb] at ht
  exact ⟨t', hr, ht⟩

/-! ### The batch grid and the optional length pointers -/

theorem eOf_lt_b {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    eOf L g < P.b := by
  unfold eOf
  rw [batchOf_eq hpre]
  exact Nat.mod_lt _ hpre.bPos

theorem paramWord_b_eq {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramWord L 0 4 = P.b % 2 ^ 32 :=
  Thread.paramWord_b hpre

/-- The thread's CTA is a batch index of the grid, for every thread index. -/
theorem batchOf_lt_of_pre {mem0 : Mem0} (hpre : Pre P L mem0) (g : Nat) : batchOf L g < P.b := by
  rw [batchOf_eq hpre]
  exact Nat.mod_lt _ hpre.bPos

/-- The role's batch index is a 32-bit word. -/
theorem batchOf_lt_two_pow {mem0 : Mem0} (hpre : Pre P L mem0) (g : Nat) : batchOf L g < 2 ^ 32 :=
  lt_of_lt_of_le (batchOf_lt_of_pre hpre g) hpre.bRange

/-- A `geq` comparison of two nonnegative signed 32-bit words below `2 ^ 31` is the unsigned
one, and a smaller left word makes it false. -/
theorem compare_ge_s32_false {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h : a < b) :
    compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = false := by
  norm_signed

theorem geBatch_false {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (h : batchOf L g < P.b)
    : geBatch L g = false := by
  have hb32 : P.b % 2 ^ 32 = P.b := Nat.mod_eq_of_lt (by have := hpre.bLt; omega)
  have ha : batchOf L g < 2 ^ 31 := lt_trans h hpre.bLt
  unfold geBatch eOf
  rw [paramWord_b_eq hpre, hb32]
  exact compare_ge_s32_false ha hpre.bLt h

theorem ptrIsNull_80_none {mem0 : Mem0} (hpre : Pre P L mem0) (h : P.topkLenBase = none)
    : ptrIsNull L 80 = true := by
  unfold ptrIsNull
  rw [show paramWord L 80 8 = 0 from Thread.paramWord_80_zero hpre h]
  decide

theorem ptrIsNull_144_none {mem0 : Mem0} (hpre : Pre P L mem0) (h : P.extraTopkLenBase = none)
    : ptrIsNull L 144 = true := by
  unfold ptrIsNull
  rw [show paramWord L 144 8 = 0 from Thread.paramWord_144_zero hpre h]
  decide

theorem ptrIsNull_80_some {mem0 : Mem0} (hpre : Pre P L mem0) {x : Nat} (h : P.topkLenBase = some x)
    : ptrIsNull L 80 = false := by
  unfold ptrIsNull
  rw [show paramWord L 80 8 = x % 2 ^ 64 from Thread.paramWord_80_some hpre h]
  have hx : 0 < x := hpre.topkLenNonNull x h
  have hxlt : x < 2 ^ 64 := hpre.topkLenBaseLt x h
  have h1 : truncBits 64 (BitVec.ofNat 64 (x % 2 ^ 64)) = BitVec.ofNat 64 (x % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp [truncBits, BitVec.toNat_ofNat]
  have h2 : truncBits 64 (BitVec.ofInt 64 0) = BitVec.ofNat 64 0 := by decide
  rw [h1, h2]
  unfold compare
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxlt, Nat.zero_mod, decide_eq_false_iff_not]
  omega

theorem ptrIsNull_144_some {mem0 : Mem0} (hpre : Pre P L mem0) {x : Nat}
    (h : P.extraTopkLenBase = some x) : ptrIsNull L 144 = false := by
  unfold ptrIsNull
  rw [show paramWord L 144 8 = x % 2 ^ 64 from Thread.paramWord_144_some hpre h]
  have hx : 0 < x := hpre.extraTopkLenNonNull x h
  have hxlt : x < 2 ^ 64 := hpre.extraTopkLenBaseLt x h
  have h1 : truncBits 64 (BitVec.ofNat 64 (x % 2 ^ 64)) = BitVec.ofNat 64 (x % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp [truncBits, BitVec.toNat_ofNat]
  have h2 : truncBits 64 (BitVec.ofInt 64 0) = BitVec.ofNat 64 0 := by decide
  rw [h1, h2]
  unfold compare
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxlt, Nat.zero_mod, decide_eq_false_iff_not]
  omega

/-! ### The block count of a row -/

theorem len0_le {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    len0 P L g ≤ P.topk := by
  unfold len0
  cases h : P.topkLenBase with
  | none =>
    have hp := hpre.paramTopkLen
    rw [h] at hp
    exact le_of_eq (hp.2 _ (eOf_lt_b hpre))
  | some x =>
    have hp := hpre.paramTopkLen
    rw [h] at hp
    exact (hp.2.2 (eOf L g) (eOf_lt_b hpre) 0 (by omega)).2 _ (eOf_lt_b hpre)

theorem len1_le {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    len1 P L g ≤ P.extra_topk := by
  unfold len1
  cases h : P.extraTopkLenBase with
  | none =>
    have hp := hpre.paramExtraTopkLen
    rw [h] at hp
    exact le_of_eq (hp.2 _ (eOf_lt_b hpre))
  | some x =>
    have hp := hpre.paramExtraTopkLen
    rw [h] at hp
    exact (hp.2.2 (eOf L g) (eOf_lt_b hpre) 0 (by omega)).2 _ (eOf_lt_b hpre)

theorem total_ge (P : Params) (L : Launch) (g : Nat) : 64 ≤ total P L g :=
  le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)

theorem total_lt (hpre : Pre P L mem0) : total P L g < 2 ^ 31 := by
  simpa [total, pad64, origPadded, ceilToMultiple, topkBlock, len0, len1]
    using hpre.paddedRange (eOf L g) (eOf_lt_b hpre)

theorem totalGt63_true {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) : totalGt63 P L g = true := by
  have ht := total_ge P L g
  have hlt := total_lt (P := P) (L := L) (mem0 := mem0) (g := g) hpre
  unfold totalGt63
  norm_signed
end

theorem blocks_lt_two_pow {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) : blocks P L g < 2 ^ 32 := by
  have := total_lt (g := g) hpre
  unfold blocks
  omega

/-- The padded length word the kernel computes: the `add.s32` of 63, the signed-shift
correction (`shr.s32` by 31, `shr.u32` by 26) and the `-64` mask. -/
theorem pad64_word {n : Nat} (h : n + 63 < 2 ^ 31) :
    (((n % 4294967296 + 63) % 4294967296 +
        (toSigned 32 (BitVec.ofNat 64 ((n % 4294967296 + 63) % 4294967296)) / 2 ^ min 31 32 %
          18446744073709551616).toNat % 4294967296 / 67108864 % 4294967296) % 4294967296) &&&
        4294967232 = (n + 63) / 64 * 64 := by
  have h32 : n < 4294967296 := by omega
  have hX : (n % 4294967296 + 63) % 4294967296 = n + 63 := by
    rw [Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt (by omega : n + 63 < 4294967296)]
  have hs : toSigned 32 (BitVec.ofNat 64 (n + 63)) = ((n + 63 : Nat) : Int) := by
    unfold toSigned
    simp only [BitVec.toNat_ofNat]
    rw [ite_eq_left (by omega : (n + 63) % 2 ^ 64 % 2 ^ 32 < 2 ^ (32 - 1)),
      Nat.mod_eq_of_lt (by omega : n + 63 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n + 63 < 2 ^ 32)]
  rw [hX, hs]
  have hdiv : ((n + 63 : Nat) : Int) / 2 ^ min 31 32 = 0 := by
    rw [show min 31 32 = 31 from rfl]
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [hdiv]
  simp only [Int.reduceMod, Int.toNat_zero, Nat.zero_div, Nat.zero_mod, Nat.add_zero]
  rw [show (n + 63) % 4294967296 = n + 63 from Nat.mod_eq_of_lt (by omega),
    show (4294967232 : Nat) = 2 ^ 32 - 2 ^ 6 from by decide,
    CeilDiv.land_highMask _ 32 6 (by decide),
    Nat.mod_eq_of_lt (show n + 63 < 2 ^ 32 by omega)]
  rfl

/-- The padded length word with the truncation the 32-bit register applies. -/
theorem pad64_word_mod {n : Nat} (h : n + 63 < 2 ^ 31) :
    ((((n % 4294967296 + 63) % 4294967296 +
        (toSigned 32 (BitVec.ofNat 64 ((n % 4294967296 + 63) % 4294967296)) / 2 ^ min 31 32 %
          18446744073709551616).toNat % 4294967296 / 67108864 % 4294967296) % 4294967296) &&&
        4294967232) % 4294967296 = (n + 63) / 64 * 64 := by
  rw [pad64_word h, Nat.mod_eq_of_lt]
  omega

/-- The `max` of the main-cache pad with 64, as the kernel's signed `setp.gt`/`selp` computes
it. -/
theorem max64_word {n : Nat} (h : n + 63 < 2 ^ 31) :
    (if compare (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
        IType.s 32 (BitVec.ofNat 64 ((n + 63) / 64 * 64 % 4294967296)) 64#64 = true
      then BitVec.ofNat 64 ((n + 63) / 64 * 64 % 4294967296)
      else 64#64) = BitVec.ofNat 64 (max ((n + 63) / 64 * 64) 64) := by
  have h1 : (n + 63) / 64 * 64 % 4294967296 = (n + 63) / 64 * 64 := by
    rw [Nat.mod_eq_of_lt]; omega
  rw [h1]
  rw [show (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt) = Cmp.gt
    from by decide]
  by_cases hc : 64 < (n + 63) / 64 * 64
  · rw [show compare Cmp.gt IType.s 32 (BitVec.ofNat 64 ((n + 63) / 64 * 64))
        (BitVec.ofNat 64 64) = true from by norm_signed]
    rw [ite_eq_left (by trivial)]
    congr 1
    exact (Nat.max_eq_left (by omega)).symm
  · have hle : (n + 63) / 64 * 64 ≤ 64 := by omega
    rw [show compare Cmp.gt IType.s 32 (BitVec.ofNat 64 ((n + 63) / 64 * 64))
        (BitVec.ofNat 64 64) = false from by norm_signed]
    rw [ite_eq_right (by trivial)]
    congr 1
    exact (Nat.max_eq_right hle).symm

/-- The padded token total: the two pads' 32-bit sum is the table's `total`. -/
theorem total_word {n m : Nat} (hn : n + 63 < 2 ^ 31) (hm : m + 63 < 2 ^ 31) :
    truncBits 32
      (BitVec.ofNat 64
          ((((m % 4294967296 + 63) % 4294967296 +
                  (toSigned 32 (BitVec.ofNat 64 ((m % 4294967296 + 63) % 4294967296)) /
                              2 ^ min 31 32 %
                            18446744073709551616).toNat %
                        4294967296 /
                      67108864 %
                    4294967296) %
                4294967296 &&&
              4294967232) %
            4294967296) +
        truncBits 32
          (if
              compare (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
                  IType.s 32 (BitVec.ofNat 64 ((n + 63) / 64 * 64 % 4294967296)) 64#64 =
                true then
            BitVec.ofNat 64 ((n + 63) / 64 * 64 % 4294967296)
          else 64#64)) =
      BitVec.ofNat 64 (max ((n + 63) / 64 * 64) 64 + (m + 63) / 64 * 64) := by
  rw [pad64_word_mod hm, max64_word hn]
  norm_bits

/-- The main-cache length is small: its pad fits the signed 32-bit arithmetic. -/
theorem topkLen_add63_lt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) : P.topkLen (batchOf L g) + 63 < 2 ^ 31 := by
  have hlen := len0_le (g := g) hpre
  have hbudget := hpre.topkAdd63Lt
  change len0 P L g + 63 < 2 ^ 31
  omega

/-- The extra-cache length is small: its pad fits the signed 32-bit arithmetic. -/
theorem extraTopkLen_add63_lt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) : P.extraTopkLen (batchOf L g) + 63 < 2 ^ 31 := by
  have hlen := len1_le (g := g) hpre
  have hbudget := hpre.extraTopkAdd63Lt
  change len1 P L g + 63 < 2 ^ 31
  omega

/-- The `topk` parameter fits the signed 32-bit padding arithmetic. -/
theorem topk_add63_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    P.topk + 63 < 2 ^ 31 := hpre.topkAdd63Lt

/-- The `extra_topk` parameter alone fits the signed 32-bit padding arithmetic. -/
theorem extraTopk_add63_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    P.extra_topk + 63 < 2 ^ 31 := hpre.extraTopkAdd63Lt

/-- The `max` with 64 of the already padded main length, in the form the `selp` reads it. -/
theorem max64_word_pad {n : Nat} (h : n + 63 < 2 ^ 31) :
    (if compare (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
        IType.s 32 (BitVec.ofNat 64 (pad64 n % 4294967296)) 64#64 = true
      then BitVec.ofNat 64 (pad64 n % 4294967296)
      else 64#64) = BitVec.ofNat 64 (max (pad64 n) 64) :=
  max64_word h

/-- The padded main length as the kernel computes it (pcs 1878-1882 and 1887-1891). -/
theorem pad64_bits {n : Nat} (h : n + 63 < 2 ^ 31) :
    Value.bits 32
      (truncBits 32
        (truncBits 32
          (truncBits 32
            (truncBits 32
                (truncBits 32 (truncBits 32 (BitVec.ofNat 64 n) +
                  truncBits 32 (BitVec.ofInt 64 63))) +
              truncBits 32
                (if (truncBits 32 (BitVec.ofInt 64 26)).toNat ≥ 32 then 0
                else
                  truncBits 32
                      (truncBits 32
                        (BitVec.ofInt 64
                          (toSigned 32
                              (truncBits 32
                                (truncBits 32
                                  (truncBits 32 (BitVec.ofNat 64 n) +
                                    truncBits 32 (BitVec.ofInt 64 63)))) /
                            2 ^ min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32))) >>>
                    (truncBits 32 (BitVec.ofInt 64 26)).toNat))) &&&
          truncBits 32 (BitVec.ofInt 64 (-64)))) =
      b32 (pad64 n) := by
  nf_simp
  rw [pad64_word_mod h]
  simp only [pad64]
  omega

/-- The padded token total as pcs 1892-1893 add the two pads. -/
theorem total_bits {n m : Nat} (hn : n + 63 < 2 ^ 31) (hm : m + 63 < 2 ^ 31) :
    Value.bits 32
      (truncBits 32
        (truncBits 32
            (truncBits 32
                (truncBits 32
                  (truncBits 32
                      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 m) +
                        truncBits 32 (BitVec.ofInt 64 63))) +
                    truncBits 32
                      (if (truncBits 32 (BitVec.ofInt 64 26)).toNat ≥ 32 then 0
                      else
                        truncBits 32
                            (truncBits 32
                              (BitVec.ofInt 64
                                (toSigned 32
                                    (truncBits 32
                                      (truncBits 32
                                        (truncBits 32 (BitVec.ofNat 64 m) +
                                          truncBits 32 (BitVec.ofInt 64 63)))) /
                                  2 ^ min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32))) >>>
                          (truncBits 32 (BitVec.ofInt 64 26)).toNat))) &&&
              truncBits 32 (BitVec.ofInt 64 (-64))) +
          truncBits 32
            (if
                compare (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
                    (if (some IType.s == some IType.s) = true then IType.s else IType.u) 32
                    (truncBits 32 (BitVec.ofNat 64 (pad64 n))) (truncBits 32 (BitVec.ofInt 64 64)) =
                  true then
              truncBits 32 (BitVec.ofNat 64 (pad64 n))
            else truncBits 32 (BitVec.ofInt 64 64)))) =
      b32 (max (pad64 n) 64 + pad64 m) := by
  nf_simp
  rw [pad64_word_mod hm]
  rw [max64_word_pad hn]
  nf_simp
  simp only [pad64]
  omega

set_option hygiene false in
/-- Close a `seg_fp` value goal of the padded lengths: the by-64 rounding word, its `max`
with 64, or their sum, after the value normal form. -/
macro "wg1_pad_old" : tactic =>
  `(tactic| first
    | (wg1_nf0
       first
         | (rw [total_word (topkLen_add63_lt hpre) (extraTopkLen_add63_lt hpre)]; norm_bits)
         | (rw [pad64_word_mod (extraTopkLen_add63_lt hpre),
               max64_word (topkLen_add63_lt hpre)]; norm_bits)
         | (rw [max64_word (topkLen_add63_lt hpre)]; norm_bits)
         | (rw [pad64_word_mod (topkLen_add63_lt hpre)]; norm_bits)
         | (rw [pad64_word_mod (extraTopkLen_add63_lt hpre)]; norm_bits)
         | (rw [descLo_word]
            first
              | (rw [or_desc (by omega)]; omega)
              | omega)
         | omega)
    | wg1_close
    | wg1_goal)

set_option hygiene false in
/-- The `mul.wide.u32` plus `add.s64` word of the two `.nc` length reads' address setup. -/
macro "wg1_mul" : tactic =>
  `(tactic| first
    | exact mul_wide_u32_add (batchOf_lt_two_pow hpre g) (Thread.paramWord_lt L 144)
    | exact mul_wide_u32_add (batchOf_lt_two_pow hpre g) (Thread.paramWord_lt L 80))

set_option hygiene false in
/-- Close a `seg_fp` value goal of the padded lengths: the by-64 rounding word, its `max`
with 64, or their sum, as `pad64_bits` and `total_bits` state them. -/
macro "wg1_pad" : tactic =>
  `(tactic| first
    | (exact total_bits (topkLen_add63_lt hpre) (extraTopkLen_add63_lt hpre))
    | (exact pad64_bits (topkLen_add63_lt hpre))
    | (exact pad64_bits (extraTopkLen_add63_lt hpre))
    | (exact pad64_bits (topk_add63_lt hpre))
    | (exact pad64_bits (extraTopk_add63_lt hpre))
    | wg1_pad_old
    | wg1_goal)

/-- A table fact of a state. -/
theorem mem_fact {P : Params} {L : Launch} {g : Nat} {d : D} {pc r : Nat} {v : Value}
    (hm : r ∈ Flow.live pc) (hv : valueOf P L g d r = v) : (r, v) ∈ factsAt P L g pc d := by
  have h := mem_factsFrom (val := valueOf P L g d) hm
  rwa [hv] at h

/-- The `param_0` pointer register `%rd2` of a state at `pc` where it is live. -/
theorem reg2991 {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState} {pc : Nat}
    (h : At t pc (factsAt P L g pc d)) (hp : 2991 ∈ Flow.live pc) :
    t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
  have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g d) (r := 2991) hp)
  simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm

/-- Two registers set by one event. -/
theorem At.set2 {t : TState} {pc : Nat} {F : List (Nat × Value)} {r₁ r₂ : Nat} {v₁ v₂ : Value}
    (h : At t pc F) (hr₁ : ∀ p ∈ F, p.1 ≠ r₁)
    (hr₂ : ∀ p ∈ (r₁, v₁) :: F, p.1 ≠ r₂) :
    At (PTX.next (setReg (setReg t r₁ v₁) r₂ v₂)) (pc + 1) ((r₂, v₂) :: (r₁, v₁) :: F) := by
  have hne : r₁ ≠ r₂ := fun e => hr₂ (r₁, v₁) (by simp) e
  have hr₂' : ∀ p ∈ F, p.1 ≠ r₂ := fun p hp => hr₂ p (by simp [hp])
  refine ⟨by simp [PTX.next, setReg, h.1], h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_⟩
  · show (setReg (setReg t r₁ v₁) r₂ v₂).regs r₂ = some v₂
    simp [setReg]
  · show (setReg (setReg t r₁ v₁) r₂ v₂).regs r₁ = some v₁
    simp [setReg, Function.update_of_ne hne]
  · exact holds_update (holds_update h.2.2.2.2 hr₁) hr₂'

theorem paramNat_40 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramNat L (param "0") 40 4 = P.topk := by
  have hb := hpre.paramTopk
  have h4 := Thread.paramWord_four (L := L) (off := 40) (x := P.topk) (fun k hk => hb k hk)
  have h32 : P.topk < 2 ^ 32 := by
    have := hpre.topkRange
    have := hpre.sqPos
    nlinarith
  have h4' : Thread.paramWord L 40 4 = P.topk := by
    rw [h4, Nat.mod_eq_of_lt h32]
  simpa [paramWord, Thread.paramWord] using h4'

theorem paramNat_120 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramNat L (param "0") 120 4 = P.extra_topk := by
  have hb := hpre.paramExtraTopk
  have h4 := Thread.paramWord_four (L := L) (off := 120) (x := P.extra_topk) (fun k hk => hb k hk)
  have h32 : P.extra_topk < 2 ^ 32 := by
    have := hpre.extraTopkRange
    have := hpre.sqPos
    nlinarith
  have h4' : Thread.paramWord L 120 4 = P.extra_topk := by
    rw [h4, Nat.mod_eq_of_lt h32]
  simpa [paramWord, Thread.paramWord] using h4'

theorem holds_of_forall_mem {R : Nat → Option Value} {G : List (Nat × Value)}
    (h : ∀ q ∈ G, R q.1 = some q.2) : Holds R G := by
  induction G with
  | nil => trivial
  | cons q rest ih => exact ⟨h q (by simp), ih fun q' hq => h q' (by simp [hq])⟩

section
variable {P : Params} {L : Launch}

/-- An `ld.param` of one register of `param_0` that is live at the next instruction, to the
table's facts there. -/
theorem ld_param_facts {mem0 : Mem0} {g : Nat} {d : D} {t : TState} {pc w off r dst : Nat}
    {ty : DType} (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off r dst)⟩)
    (hrp : t.regs r = some (.ptr 64 false (.param (param "0")) 0))
    (hobj : L.paramObjects (param "0") = some (scalarsParam, P.param0Base))
    (hsup : ParamSupplied L (param "0") off (w / 8)) (hsze : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (h : At t pc (factsAt P L g pc d))
    (hv : paramElem w w (paramNat L (param "0") off (w / 8)) = valueOf P L g d dst)
    (hl : ∀ x ∈ Flow.live (pc + 1), x ≠ dst → x ∈ Flow.live pc) (h1 : pc ∉ paramAdds)
    (h2 : pc ∉ prefetchTensorMapSites) (hw : ty.width = w := by rfl)
    (hr : (Thread.paramLoad ty off r dst).rule = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsAt P L g (pc + 1) d) := by
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem (Thread.paramLoad ty off r dst)) = none :=
    asms_localRule_mem (t := t) (a := Thread.paramLoad ty off r dst)
      (by rw [h.1]; exact h1) (by rw [h.1]; exact h2)
  have hexec := Thread.exec_ldParamReg (A := asms) hrp hobj ⟨by omega, hsze⟩ hal hsup
    (Assumption.SegFreePc.of_eq h.1 (by seg_free_pc)) hL hw hr
  refine ⟨_, run_local hc rfl h hexec, ?_⟩
  refine ⟨by simp [PTX.next, setReg, h.1], h.2.1, h.2.2.1, h.2.2.2.1,
    holds_of_pointwise fun x hx => ?_⟩
  by_cases hx' : x = dst
  · rw [hx']
    show Function.update t.regs dst
      (some (paramElem w w (paramNat L (param "0") off (w / 8)))) dst = _
    rw [Function.update_self, hv]
  · show Function.update t.regs dst
      (some (paramElem w w (paramNat L (param "0") off (w / 8)))) x = _
    rw [Function.update_of_ne hx']
    exact holds_mem h.2.2.2.2 (mem_factsFrom (hl x hx hx'))

/-- The facts at 1877 when the query's `topk_length` was read: the length register carries the
row's main-cache length. -/
abbrev facts1877 (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (2957, b32 (len0 P L g)) ::
    factsFrom [459, 460, 2958, 3005, 3006, 3093] (valueOf P L g d)

/-- The facts at 1887 when the query's `extra_topk_length` was read. -/
abbrev facts1887 (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (2958, b32 (len1 P L g)) ::
    factsFrom [459, 460, 484, 3006, 3093] (valueOf P L g d)

/-- **The Q copy's wait** (pc 1983): the poll of `bar_q_utccp` at parity 0. -/
theorem step_qCopyWait (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.qCopyWait, i⟩ t)
    (hinv : Inv P L g ⟨.qCopyWait, i⟩) (hc : kernel.code[(Site.qCopyWait).pc]? = some ins)
    (hf : Fires (Site.qCopyWait).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qCopyWait, i⟩ e u := by
  have hpc : (Site.qCopyWait).pc = 1983 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_4)
  have h843 : t.regs 843 = some (b32 (qUtccpAddr L)) := by
    have hm := atD_reg hat (pc := 1983) (r := 843) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h812 : t.regs 812 = some (b32 0) := by
    have hm := atD_reg hat (pc := 1983) (r := 812) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hqa : qUtccpAddr L < 2 ^ 32 := by
    rw [qUtccpAddr_eq]
    exact sharedAddr_lt hpre (off := 222784) (by decide)
  have hq8 : qUtccpAddr L % 8 = 0 := by
    rw [qUtccpAddr_eq]
    exact sharedAddr_align hpre (off := 222784) (by decide)
  obtain ⟨ok, _acq, _sc, he, hu⟩ := fires_wait_at_succ (A := asms) (mbarLoc_b32 h843 hqa hq8)
    (readBits_b32 h812 (by decide)) hf
  cases ok
  · have h0 : At u 1984 ((4089, .pred false) :: facts P L g ⟨.qCopyWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 1983) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1983 (facts P L g ⟨.qCopyWait, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.qCopyWait, i⟩, t', ?_, run_rtg hr, good_of_at ht hinv⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]
  · have h0 : At u 1984 ((4089, .pred true) :: facts P L g ⟨.qCopyWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 1983) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
        At t' 1986 (facts P L g ⟨.qCopyFence, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.qCopyFence, i⟩, t', ?_, run_rtg hr,
      good_of_at ht (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]

/-- **The dequant wait** (pc 2012): the poll of `bar_dequant_ready[phase]` at parity
`i / 2 % 2`. -/
theorem step_kvWait (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.kvWait, i⟩ t)
    (hinv : Inv P L g ⟨.kvWait, i⟩) (hc : kernel.code[(Site.kvWait).pc]? = some ins)
    (hf : Fires (Site.kvWait).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.kvWait, i⟩ e u := by
  have hpc : (Site.kvWait).pc = 2012 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_5)
  have h855 : t.regs 855 = some (b32 (dequantAddr L i)) := by
    have hm := atD_reg hat (pc := 2012) (r := 855) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h879 : t.regs 879 = some (b32 (parOf i)) := by
    have hm := atD_reg hat (pc := 2012) (r := 879) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hda : dequantAddr L i < 2 ^ 32 := by
    rw [dequantAddr_eq, Nat.add_assoc]
    exact sharedAddr_lt hpre (off := 222792 + 8 * (i % 2)) (by omega)
  have hd8 : dequantAddr L i % 8 = 0 := by
    rw [dequantAddr_eq, Nat.add_assoc]
    refine sharedAddr_align hpre (off := 222792 + 8 * (i % 2)) ?_
    omega
  obtain ⟨ok, _acq, _sc, he, hu⟩ := fires_wait_at_succ (A := asms) (mbarLoc_b32 h855 hda hd8)
    (readBits_b32 h879 (by have := parOf_lt_two_pow i; omega)) hf
  cases ok
  · have h0 : At u 2013 ((4090, .pred false) :: facts P L g ⟨.kvWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 2012) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2012 (facts P L g ⟨.kvWait, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.kvWait, i⟩, t', ?_, run_rtg hr, good_of_at ht hinv⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]
  · have h0 : At u 2013 ((4090, .pred true) :: facts P L g ⟨.kvWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 2012) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
        At t' 2015 (facts P L g ⟨.kvFence, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.kvFence, i⟩, t', ?_, run_rtg hr,
      good_of_at ht (inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite]))⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]

/-- **The softmax wait** (pc 2107): the poll of `bar_so_ready[phase]` at parity `i / 2 % 2`. -/
theorem step_soWait (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.soWait, i⟩ t)
    (hinv : Inv P L g ⟨.soWait, i⟩) (hc : kernel.code[(Site.soWait).pc]? = some ins)
    (hf : Fires (Site.soWait).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.soWait, i⟩ e u := by
  have hpc : (Site.soWait).pc = 2107 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_6)
  have h878 : t.regs 878 = some (b32 (soReadyAddr L i)) := by
    have hm := atD_reg hat (pc := 2107) (r := 878) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h879 : t.regs 879 = some (b32 (parOf i)) := by
    have hm := atD_reg hat (pc := 2107) (r := 879) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hda : soReadyAddr L i < 2 ^ 32 := by
    rw [soReadyAddr_eq, Nat.add_assoc]
    exact sharedAddr_lt hpre (off := 222920 + 8 * (i % 2)) (by omega)
  have hd8 : soReadyAddr L i % 8 = 0 := by
    rw [soReadyAddr_eq, Nat.add_assoc]
    refine sharedAddr_align hpre (off := 222920 + 8 * (i % 2)) ?_
    omega
  obtain ⟨ok, _acq, _sc, he, hu⟩ := fires_wait_at_succ (A := asms) (mbarLoc_b32 h878 hda hd8)
    (readBits_b32 h879 (by have := parOf_lt_two_pow i; omega)) hf
  cases ok
  · have h0 : At u 2108 ((4107, .pred false) :: facts P L g ⟨.soWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 2107) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2107 (facts P L g ⟨.soWait, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.soWait, i⟩, t', ?_, run_rtg hr, good_of_at ht hinv⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]
  · have h0 : At u 2108 ((4107, .pred true) :: facts P L g ⟨.soWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 2107) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
        At t' 2110 (facts P L g ⟨.soFence, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.soFence, i⟩, t', ?_, run_rtg hr,
      good_of_at ht (inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite]))⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]

/-- **The CTA barrier at the role's end** (pc 2160) and the `ret` at 3611. -/
theorem step_outBar (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.outBar, i⟩ t)
    (hinv : Inv P L g ⟨.outBar, i⟩) (hc : kernel.code[(Site.outBar).pc]? = some ins)
    (hf : Fires (Site.outBar).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.outBar, i⟩ e u := by
  have hpc : (Site.outBar).pc = 2160 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_11)
  have h918 : t.regs 918 = some (b32 12) := by
    have hm := atD_reg hat (pc := 2160) (r := 918) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h919 : t.regs 919 = some (b32 384) := by
    have hm := atD_reg hat (pc := 2160) (r := 919) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h12 : readBits L g t 32 (.reg 918) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 h918 (by decide)
  have h384 : readBits L g t 32 (.reg 919) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 h919 (by decide)
  have hev : eventTmpl asms L g t (.barSyncN (.reg 918) (.reg 919) false) =
      .bar 12 (PTX.next t) none .sync := by
    simp only [eventTmpl, barTmpl, h12, h384, BitVec.toNat_ofNat,
      show (12 : Nat) < 2 ^ 64 by omega, show (384 : Nat) < 2 ^ 64 by omega,
      Nat.mod_eq_of_lt, show ¬ (16 ≤ 12) by omega, ↓reduceIte,
      show (384 : Nat) % 32 = 0 by decide, hpre.block,
      show (BarMode.sync = BarMode.arrive) = False by decide, false_implies, true_and,
      or_true, reduceCtorEq]
  rw [hev] at hf
  obtain ⟨he, hu⟩ := hf
  have hu' : u = PTX.next t := Option.some.inj hu
  have h0 : At u 2161 (facts P L g ⟨.outBar, i⟩) := by
    rw [hu']; exact at_next hat
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 3611 (facts P L g ⟨.exit, i⟩) := by
    have hbase := sharedBase_lt hpre
    seg_fp h0 using
      all_goals (try wg1_values)
      all_goals wg1_close
  have hi0 : i = blocks P L g := hinv.end_i rfl
  have hinv' : Inv P L g ⟨.exit, i⟩ := by
    refine ⟨hinv.warp, hinv.lane, hinv.blocks_pos, ?_, ?_, ?_, ?_, hinv.qmap, hinv.qk_desc,
      hinv.pv_desc, hinv.tmem_base, hinv.tmem_ranges⟩
    · show i ≤ blocks P L g
      omega
    · intro h
      exact absurd h (by simp [LoopSite])
    · intro h
      exact absurd h (by simp [PrefixSite])
    · intro h
      exact absurd h (by simp)
  refine step_advance (d' := ⟨.exit, i⟩) ?_ hu' ⟨t', hr, ht⟩ hinv'
  rw [he]
  simp only [code, next]

/-- The `ret` has no continuing event. -/
theorem step_exit (P : Params) (L : Launch) (g i : Nat) {t u : TState} {e : Event}
    {ins : Instr} (hat : (code P L g).AtD ⟨.exit, i⟩ t)
    (hc : kernel.code[(Site.exit).pc]? = some ins)
    (hf : Fires (Site.exit).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.exit, i⟩ e u := by
  have hpc : (Site.exit).pc = 3611 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  obtain ⟨_he, hu⟩ := hf
  exact absurd hu (by simp)

/-- **The Q load's wait**: the poll of `bar_q_tma` at parity 0, whose success reaches the fence
through the branch at 1932 and whose failure retries through 1933. -/
theorem step_qWait (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.qWait, i⟩ t)
    (hinv : Inv P L g ⟨.qWait, i⟩) (hc : kernel.code[(Site.qWait).pc]? = some ins)
    (hf : Fires (Site.qWait).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qWait, i⟩ e u := by
  have hpc : (Site.qWait).pc = 1931 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_3)
  have h811 : t.regs 811 = some (b32 (qTmaAddr L)) := by
    have hm := atD_reg hat (pc := 1931) (r := 811) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have h812 : t.regs 812 = some (b32 0) := by
    have hm := atD_reg hat (pc := 1931) (r := 812) rfl (by decide +kernel)
    simpa [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hqa : qTmaAddr L < 2 ^ 32 := by
    rw [qTmaAddr_eq]
    exact sharedAddr_lt hpre (off := 222776) (by decide)
  have hq8 : qTmaAddr L % 8 = 0 := by
    rw [qTmaAddr_eq]
    exact sharedAddr_align hpre (off := 222776) (by decide)
  obtain ⟨ok, _acq, _sc, he, hu⟩ := fires_wait_at_succ (A := asms) (mbarLoc_b32 h811 hqa hq8)
    (readBits_b32 h812 (by decide)) hf
  cases ok
  · -- the poll failed: the retry branch polls again
    have h0 : At u 1932 ((4088, .pred false) :: facts P L g ⟨.qWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 1931) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 1931 (facts P L g ⟨.qWait, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.qWait, i⟩, t', ?_, run_rtg hr, good_of_at ht hinv⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]
  · -- the poll completed: the branch reaches the fence
    have h0 : At u 1932 ((4088, .pred true) :: facts P L g ⟨.qWait, i⟩) := by
      rw [hu]
      exact At.set (atD_at hat) (facts_ne (pc := 1931) rfl (by decide +kernel))
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
        At t' 1934 (facts P L g ⟨.qFence, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals wg1_close
    refine Or.inl (Or.inr ⟨⟨.qFence, i⟩, t', ?_, run_rtg hr,
      good_of_at ht (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)
    rw [he]
    simp only [code, next, Bool.false_eq_true, ↓reduceIte]

/-- The `.nc` load instruction of `.loadTopk`: an `s32` word through register 3054 into 2957. -/
abbrev ncLoadTopk : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, vec := 1, ext := .same,
    nc := true, addr := { base := .reg 3054 64, off := 0 }, dsts := [some 2957] }

/-- The `.nc` load instruction of `.loadExtra`: an `s32` word through register 3056 into 2958. -/
abbrev ncLoadExtra : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, vec := 1, ext := .same,
    nc := true, addr := { base := .reg 3056 64, off := 0 }, dsts := [some 2958] }

theorem asms_ncLoads_1876 : asms.any (·.ncLoads 1876) = true := by decide +kernel

theorem asms_ncLoads_1886 : asms.any (·.ncLoads 1886) = true := by decide +kernel

/-- The launch supplies the batch word of `param_0`. -/
theorem supplied_b {mem0 : Mem0} (hpre : Pre P L mem0) :
    ParamSupplied L (param "0") 0 4 := fun k hk => ⟨_, hpre.paramB k hk⟩

/-- The launch supplies the `topk` field of `param_0`. -/
theorem supplied_40 {mem0 : Mem0} (hpre : Pre P L mem0) :
    ParamSupplied L (param "0") 40 4 := fun k hk => ⟨_, hpre.paramTopk k hk⟩

/-- The launch supplies the `extra_topk` field of `param_0`. -/
theorem supplied_120 {mem0 : Mem0} (hpre : Pre P L mem0) :
    ParamSupplied L (param "0") 120 4 := fun k hk => ⟨_, hpre.paramExtraTopk k hk⟩

/-- After a `.nc` load whose bytes rebuild to `v`, the thread is at the next instruction with
the loaded register `k` set to `v` and the other facts `G`. -/
theorem at_afterNC {g : Nat} {d : D} {t u : TState} {pc k : Nat} {bs : List (Option Byte)}
    {v : Value} {G : List (Nat × Value)} (h : At t pc (factsAt P L g pc d))
    (hu : u = afterLoad t [k] bs) (hrb : rebuild 3 bs = .ok v)
    (hG : ∀ p ∈ G, p.2 = valueOf P L g d p.1) (hl : ∀ p ∈ G, p.1 ∈ Flow.live pc)
    (hne : ∀ p ∈ G, p.1 ≠ k) :
    At u (pc + 1) ((k, v) :: G) := by
  subst hu
  rw [afterLoad_ok h.2.1 h.2.2.1 hrb]
  refine ⟨by simp [setReg, h.1], rfl, rfl, ?_, ?_⟩
  · simpa [setReg] using h.2.2.2.1
  · refine holds_of_forall_mem fun q hq => ?_
    rcases List.mem_cons.mp hq with rfl | hq
    · show Function.update t.regs k (some v) k = some v
      rw [Function.update_self]
    · obtain ⟨hvq, hlq, hneq⟩ : q.2 = valueOf P L g d q.1 ∧ q.1 ∈ Flow.live pc ∧ q.1 ≠ k :=
        ⟨hG q hq, hl q hq, hne q hq⟩
      show Function.update t.regs k (some v) q.1 = some q.2
      rw [Function.update_of_ne hneq, hvq]
      exact holds_mem h.2.2.2.2 (mem_factsFrom hlq)

/-- **The `topk_length` read** (pc 1876): the `ld.global.nc` of `topk_length + 4 * batch`. -/
theorem event_loadTopk {mem0 : Mem0} {g : Nat} {d : D} {t : TState} (hpre : Pre P L mem0)
    (h : At t 1876 (factsAt P L g 1876 d)) :
    eventTmpl asms L g t (.mem ncLoadTopk) =
      .readNC { loc := ⟨.global, 0, (paramWord L 80 8 + 4 * batchOf L g) % 2 ^ 64⟩, size := 4 }
        (afterLoad t [2957]) := by
  have h3054 : t.regs 3054 = some (b64 ((paramWord L 80 8 + 4 * batchOf L g) % 2 ^ 64)) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g d) (r := 3054) (by
      rw [show Flow.live 1876 = [459, 460, 2958, 3005, 3006, 3054, 3093] from by decide +kernel]
      simp))
    simpa [factsAt, valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hr : ncLoadTopk.rule = some .threadAccess := by decide
  have hl : ncLoadTopk.locSpace? = some .global := by decide
  have hnc : asms.any (·.ncLoads t.pc) = true := by rw [h.1]; exact asms_ncLoads_1876
  have hal : (paramWord L 80 8 + 4 * batchOf L g) % 2 ^ 64 % 4 = 0 := by
    simpa [batchOf_eq_ctaidY] using
      Thread.paramAddr_mod4 (w := 80) (Thread.paramWord_80_mod4 hpre) g
  have h1 := loadTmpl_global_nc (A := asms) (L := L) (g := g) (t := t) (d := 2957)
    (base := 3054) (w := 32) (a := (paramWord L 80 8 + 4 * batchOf L g) % 2 ^ 64)
    h.2.1 h3054 (Nat.mod_lt _ (by decide)) (by decide) hal hnc
  have h2 : memTmpl asms L g t ncLoadTopk =
      loadTmpl asms L g t .global true 32 [2957] 3054 0 :=
    memTmpl_direct_weakLoad (A := asms) (L := L) (g := g) (t := t) (a := ncLoadTopk)
      (sp := .global) (base := 3054) (w := 64) hr hl rfl rfl rfl
  show memTmpl asms L g t ncLoadTopk = _
  rw [h2, h1]

/-- **The `extra_topk_length` read** (pc 1886): the `ld.global.nc` of
`extra_topk_length + 4 * batch`. -/
theorem event_loadExtra {mem0 : Mem0} {g : Nat} {d : D} {t : TState} (hpre : Pre P L mem0)
    (h : At t 1886 (factsAt P L g 1886 d)) :
    eventTmpl asms L g t (.mem ncLoadExtra) =
      .readNC { loc := ⟨.global, 0, (paramWord L 144 8 + 4 * batchOf L g) % 2 ^ 64⟩, size := 4 }
        (afterLoad t [2958]) := by
  have h3056 : t.regs 3056 = some (b64 ((paramWord L 144 8 + 4 * batchOf L g) % 2 ^ 64)) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g d) (r := 3056) (by
      rw [show Flow.live 1886 = [459, 460, 484, 3006, 3056, 3093] from by decide +kernel]
      simp))
    simpa [factsAt, valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hr : ncLoadExtra.rule = some .threadAccess := by decide
  have hl : ncLoadExtra.locSpace? = some .global := by decide
  have hnc : asms.any (·.ncLoads t.pc) = true := by rw [h.1]; exact asms_ncLoads_1886
  have hal : (paramWord L 144 8 + 4 * batchOf L g) % 2 ^ 64 % 4 = 0 := by
    simpa [batchOf_eq_ctaidY] using
      Thread.paramAddr_mod4 (w := 144) (Thread.paramWord_144_mod4 hpre) g
  have h1 := loadTmpl_global_nc (A := asms) (L := L) (g := g) (t := t) (d := 2958)
    (base := 3056) (w := 32) (a := (paramWord L 144 8 + 4 * batchOf L g) % 2 ^ 64)
    h.2.1 h3056 (Nat.mod_lt _ (by decide)) (by decide) hal hnc
  have h2 : memTmpl asms L g t ncLoadExtra =
      loadTmpl asms L g t .global true 32 [2958] 3056 0 :=
    memTmpl_direct_weakLoad (A := asms) (L := L) (g := g) (t := t) (a := ncLoadExtra)
      (sp := .global) (base := 3056) (w := 64) hr hl rfl rfl rfl
  show memTmpl asms L g t ncLoadExtra = _
  rw [h2, h1]

/-- The facts of the extra-cache pointer being absent: its length is the parameter's. -/
theorem len1_of_null {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (h : ptrIsNull L 144 = true)
    : len1 P L g = P.extra_topk := by
  have hnone : P.extraTopkLenBase = none := by
    cases hb : P.extraTopkLenBase with
    | none => rfl
    | some x => rw [ptrIsNull_144_some hpre hb] at h; exact absurd h (by decide)
  unfold len1
  have hp := hpre.paramExtraTopkLen
  rw [hnone] at hp
  exact hp.2 (eOf L g) (eOf_lt_b hpre)

/-- The facts of the main-cache pointer being absent: its length is the parameter's. -/
theorem len0_of_null {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (h : ptrIsNull L 80 = true)
    : len0 P L g = P.topk := by
  have hnone : P.topkLenBase = none := by
    cases hb : P.topkLenBase with
    | none => rfl
    | some x => rw [ptrIsNull_80_some hpre hb] at h; exact absurd h (by decide)
  unfold len0
  have hp := hpre.paramTopkLen
  rw [hnone] at hp
  exact hp.2 (eOf L g) (eOf_lt_b hpre)

/-- The election reads the full warp mask and writes the leader and lane predicate. -/
theorem fires_elect {g i : Nat} {mem0 : Mem0} {t u : TState} {e : Event} {ins : Instr}
    (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.elect, i⟩ t) (hinv : Inv P L g ⟨.elect, i⟩)
    (hc : kernel.code[Site.elect.pc]? = some ins)
    (hf : Fires Site.elect.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ inst leader, e = ⟨1853, .elect 4294967295 inst leader⟩ ∧
      u = PTX.next (setReg (setReg t 4086 (b32 leader)) 4087
        (.pred (laneOf L g == leader))) := by
  have hpc : Site.elect.pc = 1853 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_6)
  have h794 : t.regs 794 = some (b32 4294967295) := by
    have hm := atD_reg hat (pc := 1853) (r := 794) rfl (by decide +kernel)
    simpa only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hbits : readBits L g t 32 (.reg 794) = .ok (BitVec.ofNat 64 4294967295) :=
    readBits_b32 h794 (by decide)
  have hmem : electMember 4294967295 (laneOf L g) := by
    refine ⟨hinv.lane, ?_⟩
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hinv.lane
  rw [show eventTmpl asms L g t
      (.warp ⟨.elect, none, [some 4086, some 4087], [], some (.reg 794)⟩) =
      .elect 4294967295
        (fun leader => PTX.next (setReg (setReg t 4086 (b32 leader)) 4087
          (.pred (laneOf L g == leader)))) from by
    simp only [eventTmpl, warpTmpl, WarpInstr.rule, electTmpl, hbits, b32,
      show (BitVec.ofNat 64 4294967295).toNat = 4294967295 from by decide,
      laneOf_core (g := g) hpre, if_pos hmem]] at hf
  obtain ⟨inst, leader, he, hu⟩ := hf
  exact ⟨inst, leader, he, Option.some.inj hu⟩

/-- The election's unelected lane continues to the idle role after four local instructions. -/
theorem handoff_elect_idle {g i : Nat} {mem0 : Mem0} {t u : TState} {e : Event} {ins : Instr}
    (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.elect, i⟩ t) (hinv : Inv P L g ⟨.elect, i⟩)
    (hc : kernel.code[Site.elect.pc]? = some ins)
    (hf : Fires Site.elect.pc (eventTmpl asms L g t ins.op) e (some u))
    (hn : (code P L g).next ⟨.elect, i⟩ e = some none) :
    ∃ t', run kernel asms L g 4 u = some t' ∧ Thread.Entry L g t' := by
  obtain ⟨inst, leader, he, hu⟩ := fires_elect hpre hat hinv hc hf
  have hne : laneOf L g ≠ leader := by
    intro h
    rw [he] at hn
    simp only [code, next, h, ↓reduceIte, reduceCtorEq] at hn
    cases hn
  have hpred : (laneOf L g == leader) = false := beq_eq_false_iff_ne.mpr hne
  have h4086 : ∀ p ∈ facts P L g ⟨.elect, i⟩, p.1 ≠ 4086 :=
    facts_ne (pc := 1853) rfl (by decide +kernel)
  have h4087 : ∀ p ∈ (4086, b32 leader) :: facts P L g ⟨.elect, i⟩, p.1 ≠ 4087 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · change (4086 : Nat) ≠ 4087
      decide
    · exact facts_ne (pc := 1853) rfl (by decide +kernel) p hp
  have h1854 : At u 1854 ((4087, .pred false) :: (4086, b32 leader) ::
      facts P L g ⟨.elect, i⟩) := by
    rw [hu, hpred]
    exact At.set2 (atD_at hat) h4086 h4087
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 3 u = some t1 ∧
      At t1 1857 ((57, .pred true) ::
        factsFrom [460, 2991] (valueOf P L g ⟨.elect, i⟩)) := by
    seg_fp h1854 using
      all_goals decide
  obtain ⟨t2, hr2, h2⟩ := head_branch L g (pc := 1857) (target := 2587) (p := 57)
    (pick := true) Flow.code_1857 h1 (by simp) (by rw [h1.1]; decide) (by rw [h1.1]; decide)
  refine ⟨t2, run_comp hr1 hr2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, ?_⟩
  exact idle_entry_regs h2.2.2.2.2 fun r hr => by
    rw [show Flow.live 2587 = [460, 2991] from by decide +kernel] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [factsFrom, batchOf_eq_ctaidY, valueOf, values,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit]
    · simp [factsFrom, valueOf, values, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
        _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit]
end

/-! ## Query setup and Tensor Memory copies -/

section
variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}

private theorem qLoadTail (hpre : Pre P L mem0) (h : At t 1897 (factsAt P L g 1895 d)) :
    ∃ t', run kernel asms L g 9 t = some t' ∧ At t' 1906 (factsAt P L g 1906 d) := by
  have hbase := sharedBase_lt hpre
  have htotal : total P L g < 2 ^ 31 := total_lt hpre
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 5 t = some t1 ∧
      At t1 1902 (factsAt P L g 1902 d) := by
    seg_fp h using
      all_goals (try wg1_values)
      all_goals first
        | norm_bits [sb, qDescLo, descLo, land16383]
        | norm_signed
  have h3006 : t1.regs 3006 = some (.ptr 64 true (.param (param "1")) 0) := by
    apply holds_mem h1.2.2.2.2
    apply mem_fact (pc := 1902) (r := 3006)
    · decide +kernel
    · wg1_values
  let t2 := PTX.next (setReg t1 3058 (b64 (P.param1Base + 128)))
  have hr2 : run kernel asms L g 1 t1 = some t2 :=
    run_paramAdd (pc := 1902) (k := 128) Flow.code_1902 h1
      (by decide +kernel) h3006 hpre.param1Object (by decide)
  have h2 : At t2 1903 ((3058, b64 (P.param1Base + 128)) :: factsAt P L g 1902 d) :=
    At.set h1 (not_mem_factsFrom (by decide +kernel))
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 3 t2 = some t3 ∧
      At t3 1906 (factsAt P L g 1906 d) := by
    seg_fp h2 using
      all_goals (try wg1_values)
      all_goals norm_bits [sb, qCachePolicy, qTmaAddr, Protocol.Mbar.off]
  exact ⟨t3, run_comp (run_comp hr1 hr2) hr3, h3⟩

private theorem paddedTail (hpre : Pre P L mem0) (h : At t 1887 (facts1887 P L g d)) :
    ∃ t', run kernel asms L g 7 t = some t' ∧ At t' 1894 (factsAt P L g 1894 d) := by
  have hpad0 : len0 P L g + 63 < 2 ^ 31 := topkLen_add63_lt (g := g) hpre
  have hpad1 : len1 P L g + 63 < 2 ^ 31 := extraTopkLen_add63_lt (g := g) hpre
  seg_fp h using
    all_goals (try wg1_values)
    all_goals first
      | exact total_bits hpad0 hpad1
      | (nf_simp [total]
         rw [pad64_word_mod hpad1, max64_word_pad hpad0]
         norm_bits)

theorem len_tail (hpre : Pre P L mem0) (h : At t 1887 (facts1887 P L g d)) :
    ∃ t', run kernel asms L g 18 t = some t' ∧ At t' 1906 (factsAt P L g 1906 d) := by
  obtain ⟨t1, hr1, h1⟩ := paddedTail hpre h
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 1895 (factsAt P L g 1895 d) := by
    seg_fp h1 using
      all_goals (try wg1_values)
      all_goals rfl
  have hp : (61, .pred (totalGt63 P L g)) ∈ factsAt P L g 1895 d := by
    apply mem_fact (pc := 1895) (r := 61)
    · decide +kernel
    · wg1_values
  obtain ⟨t3, hr3, h3⟩ := run_bra_to (L := L) (g := g) (pc := 1895) (target := 1897)
    (p := 61) (pick := totalGt63 P L g) Flow.code_1895 h2 hp (b := 1897) (by
      rw [totalGt63_true hpre]
      rfl)
  obtain ⟨t4, hr4, h4⟩ := qLoadTail hpre h3
  exact ⟨t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, h4⟩

/-- From the extra pointer's null test (pc 1883) to the extra-cache read (pc 1886). -/
theorem seg_to_loadExtra (hpre : Pre P L mem0) (h : At t 1883 (factsAt P L g 1883 d))
    (h60 : ptrIsNull L 144 = false) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 1886 (factsAt P L g 1886 d) := by
  obtain ⟨t1, hr1, h1⟩ := run_bra_to (L := L) (g := g) (pc := 1883) (target := 1887)
    (p := 60) (pick := ptrIsNull L 144) Flow.code_1883 h
    (by
      apply mem_fact (pc := 1883) (r := 60)
      · decide +kernel
      · wg1_values)
    (b := 1884) (by rw [h60]; rfl)
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 2 t1 = some t2 ∧
      At t2 1886 (factsAt P L g 1886 d) := by
    have hbatch := batchOf_lt_two_pow hpre g
    have hptr := Thread.paramWord_lt L 144
    seg_fp h1 using
      all_goals (try wg1_values)
      all_goals first | exact mul_wide_u32_add hbatch hptr | rfl
  exact ⟨t2, run_comp hr1 hr2, h2⟩

/-- Follow the null-extra-pointer branch and reuse the common length calculations. -/
theorem seg_to_qLoad (hpre : Pre P L mem0) (h : At t 1883 (factsAt P L g 1883 d))
    (h60 : ptrIsNull L 144 = true) (hlen1 : len1 P L g = P.extra_topk) :
    ∃ t', run kernel asms L g 19 t = some t' ∧ At t' 1906 (factsAt P L g 1906 d) := by
  obtain ⟨t1, hr1, h1⟩ := run_bra_to (L := L) (g := g) (pc := 1883) (target := 1887)
    (p := 60) (pick := ptrIsNull L 144) Flow.code_1883 h
    (by
      apply mem_fact (pc := 1883) (r := 60)
      · decide +kernel
      · wg1_values)
    (b := 1887) (by rw [h60]; rfl)
  have hkeep : ∀ r ∈ ([459, 460, 484, 3006, 3093] : List Nat), r ∈ Flow.live 1883 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hf : At t1 1887 (facts1887 P L g d) := by
    apply At.subset h1
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hlen1]
      apply mem_fact (pc := 1883) (r := 2958)
      · decide +kernel
      · wg1_values
    · simp only [factsFrom, List.mem_map] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact mem_factsFrom (val := valueOf P L g d) (hkeep r hr)
  obtain ⟨t2, hr2, h2⟩ := len_tail hpre hf
  exact ⟨t2, run_comp hr1 hr2, h2⟩
end

/-- **The `topk_length` read's step**: the `.nc` load fires, and the extra pointer's null test
selects the extra-cache read or the query load. -/
theorem step_loadTopk (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.loadTopk, i⟩ t) (hinv : Inv P L g ⟨.loadTopk, i⟩)
    (hc : kernel.code[(Site.loadTopk).pc]? = some ins)
    (hf : Fires (Site.loadTopk).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.loadTopk, i⟩ e u := by
  have hpc : (Site.loadTopk).pc = 1876 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_15)
  rw [event_loadTopk (P := P) (L := L) (mem0 := mem0) (g := g) (d := ⟨.loadTopk, i⟩) hpre
    (atD_at hat)] at hf
  obtain ⟨bs, _len, he, hu⟩ := hf
  have hu' : u = afterLoad t [2957] bs := Option.some.inj hu
  cases hrb : rebuild 3 bs with
  | error f =>
    refine Or.inr ⟨?_, Machine.dead_of_fault (f := f) ?_⟩
    · rw [he]; simp [code, next, hrb]
    · rw [hu']; simp [afterLoad, hrb]
  | ok v =>
    by_cases hv : v = b32 (P.topkLen (eOf L g))
    · have hrb' : rebuild 3 bs = Except.ok (b32 (len0 P L g)) := by
        rw [show len0 P L g = P.topkLen (eOf L g) from rfl, ← hv]
        exact hrb
      have h1877 : At u 1877 (facts1877 P L g ⟨.loadTopk, i⟩) := by
        refine at_afterNC (d := ⟨.loadTopk, i⟩) (atD_at hat) hu' hrb' ?_ ?_ ?_
        · intro p hp
          simp only [factsFrom, List.mem_map] at hp
          obtain ⟨r, _hr, rfl⟩ := hp
          rfl
        · intro p hp
          simp only [factsFrom, List.mem_map] at hp
          obtain ⟨r, hr, rfl⟩ := hp
          rw [show Flow.live 1876 = [459, 460, 2958, 3005, 3006, 3054, 3093] from by
            decide +kernel]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          tauto
        · intro p hp
          simp only [factsFrom, List.mem_map] at hp
          obtain ⟨r, hr, rfl⟩ := hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 6 u = some t1 ∧
          At t1 1883 (factsAt P L g 1883 ⟨.loadTopk, i⟩) := by
        have hpad0 : len0 P L g + 63 < 2 ^ 31 := topkLen_add63_lt (g := g) hpre
        seg_fp h1877 using
          all_goals (try wg1_values)
          all_goals first
            | rfl
            | (nf_simp
               rw [pad64_word hpad0]
               rfl)
      cases h60 : ptrIsNull L 144
      · have hnext : next P L g ⟨.loadTopk, i⟩ e = some (some ⟨.loadExtra, i⟩) := by
          rw [he]
          simp [next, hrb, hv, afterTopk, h60]
        obtain ⟨t2, hr2, h2⟩ := seg_to_loadExtra hpre h1 h60
        exact Or.inl (Or.inr ⟨⟨.loadExtra, i⟩, t2, hnext, run_rtg (run_comp hr1 hr2),
          good_of_at h2 (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)
      · have hnext : next P L g ⟨.loadTopk, i⟩ e = some (some ⟨.qLoad 0, i⟩) := by
          rw [he]
          simp [next, hrb, hv, afterTopk, h60]
        obtain ⟨t2, hr2, h2⟩ := seg_to_qLoad hpre h1 h60 (len1_of_null hpre h60)
        exact Or.inl (Or.inr ⟨⟨.qLoad 0, i⟩, t2, hnext, run_rtg (run_comp hr1 hr2),
          good_of_at h2 (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)
    · have hnext : next P L g ⟨.loadTopk, i⟩ e = some none := by
        rw [he]
        simp only [next, hrb]
        rw [ite_eq_right hv]
      exact Or.inl (Or.inl hnext)

/-- Continue the election's in-grid path after its batch test. -/
private theorem step_elect_in_grid (P : Params) (L : Launch) (g i : Nat)
    {mem0 : Mem0} {t4 u : TState} {e : Event} (hpre : Pre P L mem0)
    (hinv : Inv P L g ⟨.elect, i⟩) (hg : geBatch L g = false)
    (hnext : next P L g ⟨.elect, i⟩ e = some (some ⟨startSite P L g, i⟩))
    (h4s : At t4 1861 (factsAt P L g 1861 ⟨.elect, i⟩))
    (hprefix : Relation.ReflTransGen (Tau kernel asms L g) u t4) :
    Step P L g ⟨.elect, i⟩ e u := by
  -- the row's main-cache length
  obtain ⟨t5, hr5, h5⟩ : ∃ t5, run kernel asms L g 1 t4 = some t5 ∧
      At t5 1862 (factsAt P L g 1862 ⟨.elect, i⟩) :=
    ld_param_facts (mem0 := mem0) (d := ⟨.elect, i⟩) (w := 64) Flow.code_1861
      (reg2991 h4s (by
      have hlive : Flow.live 1861 = [459, 460, 2990, 2991] := by decide +kernel
      rw [hlive]
      simp))
      hpre.param0Object (Thread.supplied_topk hpre) (by decide) (by decide) h4s
      (by simp [paramElem, paramWord, b32, b64, valueOf, values, PTX.Flow.lookupLit,
          Option.getD_some]) (by decide) (by decide) (by decide)
  obtain ⟨t6, hr6, h6⟩ : ∃ t6, run kernel asms L g 1 t5 = some t6 ∧
      At t6 1863 (factsAt P L g 1863 ⟨.elect, i⟩) :=
    ld_param_facts (mem0 := mem0) (d := ⟨.elect, i⟩) (w := 32) Flow.code_1862
      (reg2991 h5 (by
      have hlive : Flow.live 1862 = [459, 460, 2990, 2991, 3004] := by decide +kernel
      rw [hlive]
      simp))
      hpre.param0Object (supplied_40 hpre) (by decide) (by decide) h5
      (by rw [paramNat_40 hpre]; simp [paramElem, paramWord, b32, b64, valueOf, values,
          PTX.Flow.lookupLit, Option.getD_some]) (by decide) (by decide) (by decide)
  obtain ⟨t7, hr7, h7⟩ : ∃ t7, run kernel asms L g 1 t6 = some t7 ∧
      At t7 1864 (factsAt P L g 1864 ⟨.elect, i⟩) :=
    ld_param_facts (mem0 := mem0) (d := ⟨.elect, i⟩) (w := 64) Flow.code_1863
      (reg2991 h6 (by
      have hlive : Flow.live 1863 = [459, 460, 2957, 2990, 2991, 3004] := by decide +kernel
      rw [hlive]
      simp))
      hpre.param0Object (Thread.supplied_extra hpre) (by decide) (by decide) h6
      (by simp [paramElem, paramWord, b32, b64, valueOf, values, PTX.Flow.lookupLit,
          Option.getD_some]) (by decide) (by decide) (by decide)
  obtain ⟨t8, hr8, h8⟩ : ∃ t8, run kernel asms L g 1 t7 = some t8 ∧
      At t8 1865 (factsAt P L g 1865 ⟨.elect, i⟩) :=
    ld_param_facts (mem0 := mem0) (d := ⟨.elect, i⟩) (w := 32) Flow.code_1864
      (reg2991 h7 (by
      have hlive : Flow.live 1864 = [459, 460, 2957, 2990, 2991, 3004, 3005] := by decide +kernel
      rw [hlive]
      simp))
      hpre.param0Object (supplied_120 hpre) (by decide) (by decide) h7
      (by rw [paramNat_120 hpre]; simp [paramElem, paramWord, b32, b64, valueOf, values,
          PTX.Flow.lookupLit, Option.getD_some]) (by decide) (by decide) (by decide)
  have hbase := sharedBase_lt hpre
  have hdesc := descLo_lt (L.sharedBase + 204800)
  obtain ⟨tP, hrP, hP⟩ : ∃ tP, run kernel asms L g 6 t8 = some tP ∧
      At tP 1871 ((3053, b64 (descLo (L.sharedBase + 204800))) ::
        factsFrom [459, 460, 2957, 2958, 3004, 3005, 3006] (valueOf P L g ⟨.elect, i⟩)) := by
    seg_fp h8 using
      all_goals (try wg1_values)
      all_goals first | rfl | norm_bits [sb, descLo, land16383]
  obtain ⟨t9, hr9, h9⟩ : ∃ t9, run kernel asms L g 1 tP = some t9 ∧
      At t9 1872 (factsAt P L g 1872 ⟨.elect, i⟩) := by
    seg_fp hP using
      all_goals (try wg1_values)
      all_goals first
        | (exact bitrunc_or (c := 70403108110336) (by omega) (by decide) (by decide))
        | rfl
  obtain ⟨t10, hr10, h10⟩ : ∃ t10, run kernel asms L g 1 t9 = some t10 ∧
      At t10 1873 (factsAt P L g 1873 ⟨.elect, i⟩) := by
    seg_fp h9 using
      all_goals (try wg1_values)
      all_goals rfl
  have hr59 := run_comp (run_comp (run_comp (run_comp (run_comp hr5 hr6) hr7) hr8) hrP) hr9
  have hpred : (59, .pred (ptrIsNull L 80)) ∈ factsAt P L g 1873 ⟨.elect, i⟩ := by
    apply mem_fact (pc := 1873) (r := 59)
    · decide +kernel
    · wg1_values
  by_cases h59 : ptrIsNull L 80 = true
  · -- the main-cache pointer is absent: the padded total follows
    have hlen0 := len0_of_null (g := g) hpre h59
    obtain ⟨t11, hr11, h11⟩ := run_bra_to (L := L) (g := g) (pc := 1873) (target := 1877)
      (p := 59) (pick := ptrIsNull L 80) Flow.code_1873 h10
      hpred
      (b := 1877) (by rw [h59]; rfl)
    obtain ⟨t12, hr12, h12⟩ : ∃ t12, run kernel asms L g 6 t11 = some t12 ∧
        At t12 1883 (factsAt P L g 1883 ⟨.elect, i⟩) := by
      have hpad : P.topk + 63 < 2 ^ 31 := topk_add63_lt hpre
      seg_fp h11 using
        all_goals (try wg1_values)
        all_goals first
          | rfl
          | (nf_simp [hlen0]
             rw [pad64_word hpad]; rfl)
    by_cases h60 : ptrIsNull L 144 = true
    · -- the extra pointer is absent too: the query load follows
      have hlen1 := len1_of_null (g := g) hpre h60
      have hs : startSite P L g = .qLoad 0 := by
        unfold startSite
        simp only [hg, h59, h60, Bool.false_eq_true, ↓reduceIte]
      have hnext : next P L g ⟨.elect, i⟩ e = some (some ⟨.qLoad 0, i⟩) := by
        rw [hnext, hs]
      obtain ⟨t13, hr13, h13⟩ := seg_to_qLoad (d := ⟨.elect, i⟩) hpre h12 h60 hlen1
      exact Or.inl (Or.inr ⟨⟨.qLoad 0, i⟩, t13, hnext,
        hprefix.trans (run_rtg (run_comp (run_comp (run_comp (run_comp hr59 hr10) hr11) hr12) hr13)),
        good_of_at h13 (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)
    · have h60' : ptrIsNull L 144 = false := by
        cases hb : ptrIsNull L 144 <;> simp_all
      have hs : startSite P L g = .loadExtra := by
        unfold startSite
        simp only [hg, h59, h60', ↓reduceIte, Bool.false_eq_true]
      have hnext : next P L g ⟨.elect, i⟩ e = some (some ⟨.loadExtra, i⟩) := by
        rw [hnext, hs]
      obtain ⟨t13, hr13, h13⟩ := seg_to_loadExtra (d := ⟨.elect, i⟩) hpre h12 h60'
      exact Or.inl (Or.inr ⟨⟨.loadExtra, i⟩, t13, hnext,
        hprefix.trans (run_rtg (run_comp (run_comp (run_comp (run_comp hr59 hr10) hr11) hr12) hr13)),
        good_of_at h13 (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)
  · have h59' : ptrIsNull L 80 = false := by
      cases hb : ptrIsNull L 80 <;> simp_all
    have hs : startSite P L g = .loadTopk := by
      unfold startSite
      simp only [hg, h59', ↓reduceIte, Bool.false_eq_true]
    have hnext : next P L g ⟨.elect, i⟩ e = some (some ⟨.loadTopk, i⟩) := by
      rw [hnext, hs]
    obtain ⟨t11, hr11, h11⟩ := run_bra_to (L := L) (g := g) (pc := 1873) (target := 1877)
      (p := 59) (pick := ptrIsNull L 80) Flow.code_1873 h10
      hpred
      (b := 1874) (by rw [h59']; rfl)
    obtain ⟨t12, hr12, h12⟩ : ∃ t12, run kernel asms L g 2 t11 = some t12 ∧
        At t12 1876 (factsAt P L g 1876 ⟨.loadTopk, i⟩) := by
      have hbatch := batchOf_lt_two_pow hpre g
      have hptr := Thread.paramWord_lt L 80
      seg_fp h11 using
        all_goals (try wg1_values)
        all_goals first | exact mul_wide_u32_add hbatch hptr | rfl
    exact Or.inl (Or.inr ⟨⟨.loadTopk, i⟩, t12, hnext,
      hprefix.trans (run_rtg (run_comp (run_comp (run_comp hr59 hr10) hr11) hr12)),
      good_of_at h12 (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)

/-- **The election's step** (pc 1853): the elected lane reads the launch's batch count and the
row's lengths, and the other lanes leave for the idle loop. -/
theorem step_elect (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.elect, i⟩ t) (hinv : Inv P L g ⟨.elect, i⟩)
    (hc : kernel.code[(Site.elect).pc]? = some ins)
    (hf : Fires (Site.elect).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.elect, i⟩ e u := by
  obtain ⟨inst, leader, he, hu⟩ := fires_elect hpre hat hinv hc hf
  by_cases hld : laneOf L g = leader
  · have hpred : (laneOf L g == leader) = true := by simp [hld]
    have h4086 : ∀ p ∈ facts P L g ⟨.elect, i⟩, p.1 ≠ 4086 :=
      facts_ne (pc := 1853) rfl (by decide +kernel)
    have h4087 : ∀ p ∈ (4086, b32 leader) :: facts P L g ⟨.elect, i⟩, p.1 ≠ 4087 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · change (4086 : Nat) ≠ 4087
        decide
      · exact facts_ne (pc := 1853) rfl (by decide +kernel) p hp
    have h1854 : At u 1854 ((4087, .pred true) :: (4086, b32 leader) ::
        facts P L g ⟨.elect, i⟩) := by
      rw [hu, hpred]
      exact At.set2 (atD_at hat) h4086 h4087
    let regs := factsAt P L g 1858 ⟨.elect, i⟩
    obtain ⟨t0, hr0, h0⟩ : ∃ t0, run kernel asms L g 3 u = some t0 ∧
        At t0 1857 ((57, .pred false) :: regs) := by
      dsimp only [regs]
      seg_fp h1854 using
        all_goals first
          | rfl
          | (nf_simp [PTX.compare, Value.pred.injEq]; decide)
    obtain ⟨t1, hr01, h01⟩ := run_bra_to (L := L) (g := g) (pc := 1857) (target := 2587)
      (p := 57) (pick := false) Flow.code_1857 h0 (by simp) (b := 1858) rfl
    have hr1 := run_comp hr0 hr01
    have h1 : At t1 1858 (factsAt P L g 1858 ⟨.elect, i⟩) :=
      At.subset h01 (fun _ hp => List.mem_cons_of_mem _ hp)
    -- the batch word of param_0
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
        At t2 1859 (factsAt P L g 1859 ⟨.elect, i⟩) :=
      ld_param_facts (mem0 := mem0) (d := ⟨.elect, i⟩) (w := 32) Flow.code_1858
        (reg2991 h1 (by
          have hlive : Flow.live 1858 = [459, 460, 2990, 2991] := by decide +kernel
          rw [hlive]
          simp))
        hpre.param0Object (supplied_b hpre) (by decide) (by decide) h1
        (by simp [paramElem, paramWord, b32, b64, valueOf, values, PTX.Flow.lookupLit,
            Option.getD_some]) (by decide) (by decide) (by decide)
    -- the batch-grid test
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
        At t3 1860 (factsAt P L g 1860 ⟨.elect, i⟩) := by
      seg_fp h2 using
        all_goals (try wg1_values)
        all_goals rfl
    have hg := geBatch_false hpre (batchOf_lt_of_pre hpre g)
    have h58 : (58, .pred (geBatch L g)) ∈ factsAt P L g 1860 ⟨.elect, i⟩ := by
      apply mem_fact (pc := 1860) (r := 58)
      · decide +kernel
      · wg1_values
    obtain ⟨t4, hr4, h4⟩ := run_bra_to (L := L) (g := g) (pc := 1860) (target := 3611)
      (p := 58) (pick := geBatch L g) Flow.code_1860 h3 h58
      (b := 1861) (by rw [hg]; rfl)
    have h4s : At t4 1861 (factsAt P L g 1861 ⟨.elect, i⟩) :=
      At.subset h4 (by
        intro p hp
        simp only [factsAt, factsFrom, List.mem_map] at hp ⊢
        obtain ⟨r, hr, rfl⟩ := hp
        refine ⟨r, ?_, rfl⟩
        rw [show Flow.live 1861 = [459, 460, 2990, 2991] from by decide +kernel] at hr
        rw [show Flow.live 1860 = [58, 459, 460, 2990, 2991] from by decide +kernel]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        tauto)
    have hnext : next P L g ⟨.elect, i⟩ e = some (some ⟨startSite P L g, i⟩) := by
      rw [he]
      simp only [next, hld, ↓reduceIte]
    exact step_elect_in_grid P L g i hpre hinv hg hnext h4s
      (run_rtg (run_comp (run_comp (run_comp hr1 hr2) hr3) hr4))
  · -- the other lanes join the idle loop
    have hnext : next P L g ⟨.elect, i⟩ e = some none := by
      rw [he]
      simp only [next]
      rw [ite_eq_right hld]
    exact Or.inl (Or.inl hnext)

/-- **The `extra_topk_length` read's step**: the `.nc` load fires and the local code reaches
the first Q copy. -/
theorem step_loadExtra (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.loadExtra, i⟩ t) (hinv : Inv P L g ⟨.loadExtra, i⟩)
    (hc : kernel.code[(Site.loadExtra).pc]? = some ins)
    (hf : Fires (Site.loadExtra).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.loadExtra, i⟩ e u := by
  have hpc : (Site.loadExtra).pc = 1886 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_16)
  rw [event_loadExtra (P := P) (L := L) (mem0 := mem0) (g := g) (d := ⟨.loadExtra, i⟩) hpre
    (atD_at hat)] at hf
  obtain ⟨bs, _len, he, hu⟩ := hf
  have hu' : u = afterLoad t [2958] bs := Option.some.inj hu
  cases hrb : rebuild 3 bs with
  | error f =>
    refine Or.inr ⟨?_, Machine.dead_of_fault (f := f) ?_⟩
    · rw [he]; simp [code, next, hrb]
    · rw [hu']; simp [afterLoad, hrb]
  | ok v =>
    by_cases hv : v = b32 (P.extraTopkLen (eOf L g))
    · have hrb' : rebuild 3 bs = Except.ok (b32 (len1 P L g)) := by
        rw [show len1 P L g = P.extraTopkLen (eOf L g) from rfl, ← hv]
        exact hrb
      have h1887 : At u 1887 (facts1887 P L g ⟨.loadExtra, i⟩) := by
        refine at_afterNC (d := ⟨.loadExtra, i⟩) (atD_at hat) hu' hrb' ?_ ?_ ?_
        · intro p hp
          simp only [factsFrom, List.mem_map] at hp
          obtain ⟨r, _hr, rfl⟩ := hp
          rfl
        · intro p hp
          simp only [factsFrom, List.mem_map] at hp
          obtain ⟨r, hr, rfl⟩ := hp
          rw [show Flow.live 1886 = [459, 460, 484, 3006, 3056, 3093] from by decide +kernel]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          tauto
        · intro p hp
          simp only [factsFrom, List.mem_map] at hp
          obtain ⟨r, hr, rfl⟩ := hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
      have hnext : next P L g ⟨.loadExtra, i⟩ e = some (some { site := .qLoad 0, i := i }) := by
        rw [he]
        simp only [next, hrb]
        rw [ite_eq_left hv]
      obtain ⟨t', hr, ht⟩ := len_tail (P := P) (L := L) (mem0 := mem0) (g := g)
        (d := ⟨.loadExtra, i⟩) hpre h1887
      refine Or.inl (Or.inr ⟨⟨.qLoad 0, i⟩, t', hnext, run_rtg hr,
        good_of_at ht (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))⟩)
    · have hnext : next P L g ⟨.loadExtra, i⟩ e = some none := by
        rw [he]
        simp only [next, hrb]
        rw [ite_eq_right hv]
      exact Or.inl (Or.inl hnext)

macro "q_copy_value" launch:term : tactic =>
  `(tactic| first
    | norm_bits [qCopyDesc, qCopyCol, qDescLo, descLo, tmemQ, Fin.val_mk, qUtccpAddr, Protocol.Mbar.off]
    | (nf_simp [qCopyDesc, qDescLo, Fin.coe_ofNat_eq_mod]
       rw [Nat.mod_eq_of_lt (show descLo ($launch).sharedBase < 18446744073709551616 by
         have := descLo_lt ($launch).sharedBase; omega),
         or_desc (descLo_lt ($launch).sharedBase)] <;> omega))

/-- **The Q copy's commit** (pc 1982): the commit fires and the wait follows. -/
theorem step_qCopyCommit (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.qCopyCommit, i⟩ t)
    (hinv : Inv P L g ⟨.qCopyCommit, i⟩) (hc : kernel.code[(Site.qCopyCommit).pc]? = some ins)
    (hf : Fires (Site.qCopyCommit).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qCopyCommit, i⟩ e u := by
  have hpc : (Site.qCopyCommit).pc = 1982 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_0)
  obtain hu := fires_tcCommit (A := asms) (pc := 1982) hf
  have h0 : At u 1983 (facts P L g ⟨.qCopyWait, i⟩) := by
    rw [hu]
    have hsame : facts P L g ⟨.qCopyCommit, i⟩ = facts P L g ⟨.qCopyWait, i⟩ := by
      simp only [facts, factsAt, Site.pc,
        show Flow.live 1982 = [62, 485, 812, 828, 843, 3093] from by decide +kernel,
        show Flow.live 1983 = [62, 485, 812, 828, 843, 3093] from by decide +kernel]
      all_goals rfl
    rw [← hsame]
    exact at_next hat
  refine Or.inl (Or.inr ⟨⟨.qCopyWait, i⟩, u, ?_, Relation.ReflTransGen.refl, ?_⟩)
  · rfl
  · exact good_of_at (d := ⟨.qCopyWait, i⟩) h0
      (inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))

/-- **The copy fence**: `tcgen05.fence::after_thread_sync` (pc 1934) and the shared descriptor
of the first copy (1935) reach the first copy. -/
theorem step_qFence (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.qFence, i⟩ t)
    (hinv : Inv P L g ⟨.qFence, i⟩) (hc : kernel.code[(Site.qFence).pc]? = some ins)
    (hf : Fires (Site.qFence).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qFence, i⟩ e u := by
  have hpc : (Site.qFence).pc = 1934 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_5)
  obtain hu := fires_async_next (A := asms) (op := .tcFenceAfter) trivial hf
  have h0 : At u 1935 (facts P L g ⟨.qFence, i⟩) := by
    rw [hu]; exact at_next hat
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 1936 (facts P L g ⟨.qCopy 0, i⟩) := by
    have hbase := sharedBase_lt hpre
    seg_fp h0 using
      all_goals (try wg1_values)
      all_goals q_copy_value L
  refine step_advance (d' := ⟨.qCopy 0, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
  · simp [code, next, nextSite]
  · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite])

macro "prove_copy_step " name:ident "," src:term "," pc:num "," after:num ","
    dst:term "," dest:num "," len:num "," op:term : command =>
  `(command| private theorem $name (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0}
      {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
      (hat : (code P L g).AtD ⟨$src, i⟩ t) (hinv : Inv P L g ⟨$src, i⟩)
      (hc : kernel.code[(Site.pc $src)]? = some ins)
      (hf : Fires (Site.pc $src) (eventTmpl asms L g t ins.op) e (some u)) :
      Step P L g ⟨$src, i⟩ e u := by
    have hpc : Site.pc $src = $pc := rfl
    rw [hpc] at hc hf
    have hins := Option.some.inj (hc.symm.trans $op)
    subst ins
    obtain hu := fires_tcCp_next (A := asms) hf
    have h0 : At u $after (facts P L g ⟨$src, i⟩) := by
      rw [hu]
      exact at_next hat
    have hbase := sharedBase_lt hpre
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g $len u = some t' ∧
        At t' $dest (facts P L g ⟨$dst, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals q_copy_value L
    refine step_advance (d' := ⟨$dst, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_prefix hinv (by simp [PrefixSite]) (by simp [PrefixSite]))

prove_copy_step step_qCopy_0, (.qCopy 0), 1936, 1937, (.qCopy 1), 1939, 2, Flow.code_tmemCopy_0

prove_copy_step step_qCopy_1, (.qCopy 1), 1939, 1940, (.qCopy 2), 1942, 2, Flow.code_tmemCopy_1

prove_copy_step step_qCopy_2, (.qCopy 2), 1942, 1943, (.qCopy 3), 1945, 2, Flow.code_tmemCopy_2

prove_copy_step step_qCopy_3, (.qCopy 3), 1945, 1946, (.qCopy 4), 1948, 2, Flow.code_tmemCopy_3

prove_copy_step step_qCopy_4, (.qCopy 4), 1948, 1949, (.qCopy 5), 1951, 2, Flow.code_tmemCopy_4

prove_copy_step step_qCopy_5, (.qCopy 5), 1951, 1952, (.qCopy 6), 1954, 2, Flow.code_tmemCopy_5

prove_copy_step step_qCopy_6, (.qCopy 6), 1954, 1955, (.qCopy 7), 1957, 2, Flow.code_tmemCopy_6

prove_copy_step step_qCopy_7, (.qCopy 7), 1957, 1958, (.qCopy 8), 1959, 1, Flow.code_tmemCopy_7

prove_copy_step step_qCopy_8, (.qCopy 8), 1959, 1960, (.qCopy 9), 1962, 2, Flow.code_tmemCopy_8

prove_copy_step step_qCopy_9, (.qCopy 9), 1962, 1963, (.qCopy 10), 1965, 2, Flow.code_tmemCopy_9

prove_copy_step step_qCopy_10, (.qCopy 10), 1965, 1966, (.qCopy 11), 1968, 2, Flow.code_tmemCopy_10

prove_copy_step step_qCopy_11, (.qCopy 11), 1968, 1969, (.qCopy 12), 1971, 2, Flow.code_tmemCopy_11

prove_copy_step step_qCopy_12, (.qCopy 12), 1971, 1972, (.qCopy 13), 1974, 2, Flow.code_tmemCopy_12

prove_copy_step step_qCopy_13, (.qCopy 13), 1974, 1975, (.qCopy 14), 1977, 2, Flow.code_tmemCopy_13

prove_copy_step step_qCopy_14, (.qCopy 14), 1977, 1978, (.qCopy 15), 1980, 2, Flow.code_tmemCopy_14

prove_copy_step step_qCopy_15, (.qCopy 15), 1980, 1981, .qCopyCommit, 1982, 1, Flow.code_tmemCopy_15

/-- **The sixteen shared-to-Tensor-Memory copies**: each `tcgen05.cp` of the query tile fires,
and the local instructions that follow form the next copy's descriptor and destination
column. -/
theorem step_qCopy (P : Params) (L : Launch) (g i : Nat) (k : Fin 16) {mem0 : Mem0}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.qCopy k, i⟩ t) (hinv : Inv P L g ⟨.qCopy k, i⟩)
    (hc : kernel.code[(Site.qCopy k).pc]? = some ins)
    (hf : Fires (Site.qCopy k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qCopy k, i⟩ e u := by
  revert hat hinv hc hf
  fin_cases k <;> intro hat hinv hc hf
  · exact step_qCopy_0 P L g i hpre hat hinv hc hf
  · exact step_qCopy_1 P L g i hpre hat hinv hc hf
  · exact step_qCopy_2 P L g i hpre hat hinv hc hf
  · exact step_qCopy_3 P L g i hpre hat hinv hc hf
  · exact step_qCopy_4 P L g i hpre hat hinv hc hf
  · exact step_qCopy_5 P L g i hpre hat hinv hc hf
  · exact step_qCopy_6 P L g i hpre hat hinv hc hf
  · exact step_qCopy_7 P L g i hpre hat hinv hc hf
  · exact step_qCopy_8 P L g i hpre hat hinv hc hf
  · exact step_qCopy_9 P L g i hpre hat hinv hc hf
  · exact step_qCopy_10 P L g i hpre hat hinv hc hf
  · exact step_qCopy_11 P L g i hpre hat hinv hc hf
  · exact step_qCopy_12 P L g i hpre hat hinv hc hf
  · exact step_qCopy_13 P L g i hpre hat hinv hc hf
  · exact step_qCopy_14 P L g i hpre hat hinv hc hf
  · exact step_qCopy_15 P L g i hpre hat hinv hc hf

/-! ## K/V descriptors and synchronization -/

/-- **The QK commit** (pc 2105): the commit of the sixteen QK MMAs to `bar_qk_done[phase]`
(2105) and the ready-mbarrier's address word (2106) reach the softmax wait. -/
theorem step_qkCommit (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.qkCommit, i⟩ t)
    (hinv : Inv P L g ⟨.qkCommit, i⟩) (hc : kernel.code[(Site.qkCommit).pc]? = some ins)
    (hf : Fires (Site.qkCommit).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qkCommit, i⟩ e u := by
  have hpc : (Site.qkCommit).pc = 2105 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_1)
  obtain hu := fires_tcCommit (A := asms) (pc := 2105) hf
  have h0 : At u 2106 (facts P L g ⟨.qkCommit, i⟩) := by
    rw [hu]; exact at_next hat
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 2107 (facts P L g ⟨.soWait, i⟩) := by
    have hbase := sharedBase_lt hpre
    seg_fp h0 using
      all_goals (try wg1_values)
      all_goals norm_bits [soReadyAddr_eq, phaseOf]
  refine step_advance (d' := ⟨.soWait, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
  · simp [code, next, nextSite]
  · exact inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite])

/-- **The dequant fence** (pc 2015): `tcgen05.fence::after_thread_sync` and the eleven local
instructions that form the first K descriptor, the Tensor-Memory columns and the first MMA's
enable reach the first QK MMA. -/
theorem step_kvFence (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.kvFence, i⟩ t)
    (hinv : Inv P L g ⟨.kvFence, i⟩) (hc : kernel.code[(Site.kvFence).pc]? = some ins)
    (hf : Fires (Site.kvFence).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.kvFence, i⟩ e u := by
  have hpc : (Site.kvFence).pc = 2015 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_7)
  obtain hu := fires_async_next (A := asms) (op := .tcFenceAfter) trivial hf
  have h0 : At u 2016 (facts P L g ⟨.kvFence, i⟩) := by
    rw [hu]; exact at_next hat
  have hbase := sharedBase_lt hpre
  have hdesc := descLo_lt (kvBase L i)
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 4 u = some t1 ∧
      At t1 2020 (factsAt P L g 2020 ⟨.kvFence, i⟩) := by
    seg_fp h0 using
      all_goals (try wg1_values)
      all_goals first
        | exact descLo_word_bits L.sharedBase (phaseOf i)
        | norm_bits [phaseOf, kvBase, descLo, land16383]
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 2021 (factsAt P L g 2021 ⟨.kvFence, i⟩) := by
    seg_fp h1 using
      all_goals (try wg1_values)
      all_goals first
        | (exact bitrunc_or (c := 4611756662049538048) (by omega) (by decide) (by decide))
        | rfl
  obtain ⟨t', hr3, ht⟩ : ∃ t', run kernel asms L g 6 t2 = some t' ∧
      At t' 2027 (facts P L g ⟨.qkMma 0, i⟩) := by
    seg_fp h2 using
      all_goals (try wg1_values)
      all_goals first
        | norm_bits [kDesc, qkBDelta, qkACol, tmemQ, tmemP, tmemO, qkIdesc]
        | (nf_simp [PTX.compare, Value.pred.injEq]; decide)
  have hr := run_comp (run_comp hr1 hr2) hr3
  refine step_advance (d' := ⟨.qkMma 0, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
  · simp [code, next, nextSite]
  · exact inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite])

/-- **The softmax fence** (pc 2110): the fence, the V descriptor of the first PV MMA, its Tensor
Memory column and the accumulate predicate of the first block (which accumulates only from the
second block on). -/
theorem step_soFence (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hat : (code P L g).AtD ⟨.soFence, i⟩ t)
    (hinv : Inv P L g ⟨.soFence, i⟩) (hc : kernel.code[(Site.soFence).pc]? = some ins)
    (hf : Fires (Site.soFence).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.soFence, i⟩ e u := by
  have hpc : (Site.soFence).pc = 2110 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_8)
  obtain hu := fires_async_next (A := asms) (op := .tcFenceAfter) trivial hf
  have h0 : At u 2111 (facts P L g ⟨.soFence, i⟩) := by
    rw [hu]; exact at_next hat
  have hdesc := descLo_lt (kvBase L i)
  have hi : i < 2 ^ 32 :=
    lt_trans (hinv.i_lt (by simp [LoopSite])) (blocks_lt_two_pow (g := g) hpre)
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
      At t1 2112 (factsAt P L g 2112 ⟨.soFence, i⟩) := by
    seg_fp h0 using
      all_goals (try wg1_values)
      all_goals first | exact pred_ne_zero i hi | rfl
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 2113 (factsAt P L g 2113 ⟨.soFence, i⟩) := by
    seg_fp h1 using
      all_goals (try wg1_values)
      all_goals first
        | (exact bitrunc_or (c := 4611756662083026944) (by omega) (by decide) (by decide))
        | rfl
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
      At t3 2114 ((63, .pred (i != 0)) ::
        factsFrom [152, 860, 862, 887, 888, 909, 910, 2959, 2960, 2961, 3093, 3094, 3096, 3099,
          3102] (valueOf P L g ⟨.soFence, i⟩)) := by
    seg_fp h2 using
      all_goals (try wg1_values)
      all_goals norm_bits [vDesc, pvBDelta]
  have hr := run_comp (run_comp hr1 hr2) hr3
  rcases hb : (i != 0) with _ | _
  · -- the first block: no accumulator to add to
    have hi0 : i = 0 := by
      by_contra h
      rw [show (i != 0) = true from (bne_iff_ne).mpr h] at hb
      exact absurd hb (by decide)
    rw [hb] at h3
    obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 3 t3 = some t4 ∧
        At t4 2117 (facts P L g ⟨.pvMma 0, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h3 using
        all_goals (try wg1_values)
        all_goals (first | (nf_simp [hb, PTX.compare, Value.pred.injEq]; decide) | norm_bits [sb, pvIdesc, ite_eq_left hi0])
    refine step_advance (d' := ⟨.pvMma 0, i⟩) ?_ hu ⟨_, run_comp hr hr4, h4⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite])
  · -- a later block: the O accumulator is added to
    have hi0 : i ≠ 0 := by
      simp only [bne_iff_ne] at hb
      exact hb
    rw [hb] at h3
    obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 3 t3 = some t4 ∧
        At t4 2117 (facts P L g ⟨.pvMma 0, i⟩) := by
      have hbase := sharedBase_lt hpre
      seg_fp h3 using
        all_goals (try wg1_values)
        all_goals (first | (nf_simp [hb, PTX.compare, Value.pred.injEq]; decide) | norm_bits [sb, pvIdesc, ite_eq_right hi0])
    refine step_advance (d' := ⟨.pvMma 0, i⟩) ?_ hu ⟨_, run_comp hr hr4, h4⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite])

/-! ## The main loop back edge -/

/-- The loop head stores the parity of the block about to run. -/
abbrev facts2003 (P : Params) (L : Launch) (g i : Nat) : List (Nat × Value) :=
  (453, b16 (parOf i)) :: factsFrom [2959, 2960, 2961, 3093, 3096, 3099, 3102]
    (valueOf P L g ⟨.kvWait, i⟩)

/-- Form the dequant barrier address and the wait parity from the loop-head words. -/
private theorem loop_head_to_wait {P : Params} {L : Launch} {mem0 : Mem0} {g i : Nat}
    {t : TState} (hpre : Pre P L mem0) (h : At t 2003 (facts2003 P L g i)) :
    ∃ t', run kernel asms L g 9 t = some t' ∧ At t' 2012 (factsAt P L g 2012 ⟨.kvWait, i⟩) := by
  have hbase := sharedBase_lt hpre
  have hpar := parOf_lt i
  have hphase : i % 2 < 2 := phaseOf_lt i
  seg_fp h using
    all_goals (try wg1_values)
    all_goals first
      | (rw [not_phase]; rfl)
      | norm_bits [b16, land255, dequantAddr_eq, phaseOf, sb]

private theorem advance_phase (i : Nat) :
    Value.bits 32 (truncBits 32
        (BitVec.ofNat 64 (if phaseOf i = 0 then 4294967295 else 4294967294)) &&&
      truncBits 32 (BitVec.ofInt 64 1)) = b32 (phaseOf (i + 1)) := by
  have hp := phaseOf_lt i
  rcases (by omega : phaseOf i = 0 ∨ phaseOf i = 1) with h0 | h1
  · rw [phaseOf_succ, h0]
    decide
  · rw [phaseOf_succ, h1]
    decide

private theorem advance_count (i n : Nat) :
    Value.bits 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (i32Bits ((i : Int) - (n : Int)))) +
        truncBits 32 (BitVec.ofInt 64 1))) =
      b32 (i32Bits (((i + 1 : Nat) : Int) - (n : Int))) := by
  nf_simp [i32Bits, Nat.cast_add, Nat.cast_one]
  omega

private theorem compare_count (i n : Nat) (h : i + 1 ≤ n) (hn : n < 2 ^ 32) :
    Value.pred (compare .ne .b 32 (truncBits 32
      (BitVec.ofNat 64 (i32Bits (((i + 1 : Nat) : Int) - (n : Int)))))
      (truncBits 32 (BitVec.ofInt 64 0))) = Value.pred (i + 1 != n) := by
  simp only [Value.pred.injEq, show (i + 1 != n) = decide (i + 1 ≠ n) from rfl]
  nf_simp [PTX.compare, i32Bits, decide_eq_decide, Nat.cast_add, Nat.cast_one]
  omega

abbrev facts2157 (P : Params) (L : Launch) (g i : Nat) : List (Nat × Value) :=
  (65, .pred (i + 1 != blocks P L g)) :: facts2003 P L g (i + 1)

private theorem next_block_words {P : Params} {L : Launch} {mem0 : Mem0} {g i : Nat}
    {t : TState} (hpre : Pre P L mem0) (hilt : i < blocks P L g)
    (h : At t 2149 (facts P L g ⟨.pvCommit, i⟩)) :
    ∃ t', run kernel asms L g 8 t = some t' ∧ At t' 2157 (facts2157 P L g i) := by
  have hpar := parOf_lt i
  have hphase := phaseOf_lt i
  have hib : i + 1 ≤ blocks P L g := hilt
  have hblocks := blocks_lt_two_pow (g := g) hpre
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 3 t = some t1 ∧
      At t1 2152 ((64, .pred (parOf i != phaseOf i)) ::
        factsFrom [888, 2959, 2960, 3093, 3096, 3099, 3102] (valueOf P L g ⟨.pvCommit, i⟩)) := by
    seg_fp h using
      all_goals (try wg1_values)
      all_goals
        simp only [Value.pred.injEq,
          show (parOf i != phaseOf i) = decide (parOf i ≠ phaseOf i) from rfl]
        nf_simp [PTX.compare, decide_eq_decide, land255]
        omega
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 2153 ((453, b16 (parOf (i + 1))) ::
        factsFrom [888, 2959, 2960, 3093, 3096, 3099, 3102] (valueOf P L g ⟨.pvCommit, i⟩)) := by
    cases hpick : (parOf i != phaseOf i) <;>
      rw [hpick] at h1 <;>
      (seg_fp h1 using
        all_goals rw [parOf_succ, ← toggle_eq, hpick]; rfl)
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 3 t2 = some t3 ∧
      At t3 2156 (facts2003 P L g (i + 1)) := by
    unfold facts2003
    seg_fp h2 using
      all_goals (try wg1_values)
      all_goals first
        | exact advance_phase i
        | exact advance_count i (blocks P L g)
        | norm_bits
  obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 1 t3 = some t4 ∧
      At t4 2157 (facts2157 P L g i) := by
    unfold facts2003 at h3
    unfold facts2157 facts2003
    seg_fp h3 using
      all_goals (try wg1_values)
      all_goals exact compare_count i (blocks P L g) hib hblocks
  exact ⟨t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, h4⟩

/-- **The PV commit's step** (pc 2148): the commit fires, the block loop's phase and parity
toggle advance, and the block counter selects the next block or the CTA barrier. -/
theorem step_pvCommit (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.pvCommit, i⟩ t) (hinv : Inv P L g ⟨.pvCommit, i⟩)
    (hc : kernel.code[(Site.pvCommit).pc]? = some ins)
    (hf : Fires (Site.pvCommit).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.pvCommit, i⟩ e u := by
  have hpc : (Site.pvCommit).pc = 2148 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_2)
  obtain hu := fires_tcCommit (A := asms) (pc := 2148) hf
  have h0 : At u 2149 (facts P L g ⟨.pvCommit, i⟩) := by
    rw [hu]; exact at_next hat
  have hilt : i < blocks P L g := hinv.i_lt (by simp [LoopSite])
  obtain ⟨t0, hr0, h0'⟩ := next_block_words hpre hilt h0
  by_cases hi : i + 1 < blocks P L g
  · -- the next block
    have hpick : (i + 1 != blocks P L g) = true := by
      simp only [bne_iff_ne, ne_eq]
      omega
    obtain ⟨t1, hr1, h1⟩ := run_bra_to (L := L) (g := g) (pc := 2157) (target := 2003)
      (p := 65) (pick := i + 1 != blocks P L g) Flow.code_2157 h0' (by simp) (b := 2003) (by
        rw [hpick]; rfl)
    have htail : At t1 2003 (facts2003 P L g (i + 1)) :=
      At.subset h1 (fun _ hp => List.mem_cons_of_mem _ hp)
    obtain ⟨t2, hr2, h2⟩ := loop_head_to_wait hpre htail
    refine Or.inl (Or.inr ⟨⟨.kvWait, i + 1⟩, t2, ?_,
      run_rtg (run_comp (run_comp hr0 hr1) hr2), ?_⟩)
    · simp only [code, next, hi, Bool.false_eq_true, ↓reduceIte]
    · refine good_of_at h2 ⟨hinv.warp, hinv.lane, hinv.blocks_pos, ?_, ?_, ?_, ?_,
        hinv.qmap, hinv.qk_desc, hinv.pv_desc, hinv.tmem_base, hinv.tmem_ranges⟩
      · show i + 1 ≤ blocks P L g
        omega
      · intro _
        exact hi
      · intro hp
        exact absurd hp (by simp [PrefixSite])
      · intro ho
        exact absurd ho (by simp)
  · -- the last block: the CTA barrier
    have hib : i + 1 = blocks P L g := by omega
    have hpick : (i + 1 != blocks P L g) = false := by
      simp [hib]
    obtain ⟨t1, hr1, h1⟩ := run_bra_to (L := L) (g := g) (pc := 2157) (target := 2003)
      (p := 65) (pick := i + 1 != blocks P L g) Flow.code_2157 h0' (by simp) (b := 2158) (by
        rw [hpick]; rfl)
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 2 t1 = some t2 ∧
        At t2 2160 (factsAt P L g 2160 (⟨.outBar, i + 1⟩ : D)) := by
      unfold facts2157 facts2003 at h1
      seg_fp h1 using
        all_goals (try wg1_values)
        all_goals norm_bits
    refine Or.inl (Or.inr ⟨⟨.outBar, i + 1⟩, t2, ?_,
      run_rtg (run_comp (run_comp hr0 hr1) hr2), ?_⟩)
    · simp only [code, next, hi, Bool.false_eq_true, ↓reduceIte]
    · refine good_of_at h2 ⟨hinv.warp, hinv.lane, hinv.blocks_pos, ?_, ?_, ?_, ?_,
        hinv.qmap, hinv.qk_desc, hinv.pv_desc, hinv.tmem_base, hinv.tmem_ranges⟩
      · show i + 1 ≤ blocks P L g
        omega
      · intro h
        exact absurd h (by simp [LoopSite])
      · intro hp
        exact absurd hp (by simp [PrefixSite])
      · intro _
        exact hib

/-! ## The first block -/

private theorem pack_words {lo hi : Nat} (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) :
    joinValue (b32 lo) (b32 hi) = b64 (lo + hi * 2 ^ 32) :=
  join_bits32 rfl rfl hlo hhi

private theorem toSigned32_ofNat {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  have h1 : (truncBits 32 (BitVec.ofNat 64 n)).toNat = n := by
    simp only [truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32]
  show toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) = (n : Int)
  unfold toSigned
  rw [h1]
  simp only [Nat.mod_eq_of_lt h32, h, ↓reduceIte]

/-- **The sign word**: `shr.s32` by 31 is zero for a padded count below `2 ^ 31`
(`ku::ceil`'s correction term). -/
private theorem shr31_value {n : Nat} (hn : n < 2 ^ 31) :
    Value.bits 32
      (truncBits 32
        (BitVec.ofInt 64
          (toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) /
            2 ^ min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32))) = b32 0 := by
  have hs : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := by decide +kernel
  rw [toSigned32_ofNat hn, hs]
  have hd : (n : Int) / 2 ^ 31 = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [hd]
  show Value.bits 32 _ = _
  nf_simp [b32]

/-- **The block count**: `shr.s32` by 6 is the padded count's ceiling in blocks,
`padded / 64` (`ku::ceil`'s shift). -/
private theorem shr6_value {n : Nat} (hn : n < 2 ^ 31) :
    Value.bits 32
      (truncBits 32
        (BitVec.ofInt 64
          (toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) /
            2 ^ min (truncBits 32 (BitVec.ofInt 64 6)).toNat 32))) = b32 (n / 64) := by
  have hs : min (truncBits 32 (BitVec.ofInt 64 6)).toNat 32 = 6 := by decide +kernel
  rw [toSigned32_ofNat hn, hs]
  have hd : (n : Int) / 2 ^ 6 = ((n / 64 : Nat) : Int) := by
    rw [Int.natCast_ediv n 64]
    norm_num
  rw [hd]
  show Value.bits 32 _ = _
  nf_simp [b32]
  omega

/-- **The block counter**: `neg.s32` is the negated block count, the loop
counter the back edge increments to zero. -/
private theorem neg_value {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (-truncBits 32 (BitVec.ofNat 64 n))) = b32 (2 ^ 32 - n) := by
  show Value.bits 32 _ = _
  nf_simp [b32]
  omega

private theorem countEncoding_neg {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 32) :
    i32Bits (-(n : Int)) = 2 ^ 32 - n := by
  unfold i32Bits
  change (-(n : Int) % 4294967296).toNat = 4294967296 - n
  change n < 4294967296 at hlt
  omega

private abbrev pPrepFacts (P : Params) (L : Launch) (g : Nat) (rs : List Nat) :
    List (Nat × Value) :=
  (846, b32 (descLo (L.sharedBase + 204800) + 4194304)) :: (847, b32 16392) ::
    factsFrom rs (valueOf P L g ⟨.qCopyFence, 0⟩)

private theorem init_p_descriptors {P : Params} {L : Launch} {g : Nat} {t : TState}
    (h : At t 1988 (factsAt P L g 1987 ⟨.qCopyFence, 0⟩)) :
    ∃ t', run kernel asms L g 7 t = some t' ∧
      At t' 1995 (factsAt P L g 1995 ⟨.qCopyFence, 0⟩) := by
  have hbase := descLo_lt (L.sharedBase + 204800)
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
      At t1 1989 (pPrepFacts P L g [485, 3093]) := by
    unfold pPrepFacts
    seg_fp h using
      all_goals (try wg1_values)
      all_goals norm_bits [pDesc]
  unfold pPrepFacts at h1
  have hlow384 : descLo (L.sharedBase + 204800) + 4194304 + 384 < 2 ^ 32 := by
    omega
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 1990 ((848, b32 (descLo (L.sharedBase + 204800) + 4194304 + 384)) ::
        pPrepFacts P L g [485, 3093]) := by
    unfold pPrepFacts
    seg_fp h1 using
      all_goals norm_bits
  unfold pPrepFacts at h2
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
      At t3 1991 (pPrepFacts P L g [485, 3093, 3102]) := by
    unfold pPrepFacts
    seg_fp h2 using
      all_goals (try wg1_values)
      all_goals
        rw [pack_words hlow384 (by decide : (16392 : Nat) < 2 ^ 32)]
        simp only [pDesc]
        exact congrArg b64 (by omega)
  unfold pPrepFacts at h3
  have hlow128 : descLo (L.sharedBase + 204800) + 4194304 + 128 < 2 ^ 32 := by
    omega
  obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 1 t3 = some t4 ∧
      At t4 1992 ((849, b32 (descLo (L.sharedBase + 204800) + 4194304 + 128)) ::
        pPrepFacts P L g [485, 3093, 3102]) := by
    unfold pPrepFacts
    seg_fp h3 using
      all_goals norm_bits
  unfold pPrepFacts at h4
  obtain ⟨t5, hr5, h5⟩ : ∃ t5, run kernel asms L g 1 t4 = some t5 ∧
      At t5 1993 (pPrepFacts P L g [485, 3093, 3096, 3102]) := by
    unfold pPrepFacts
    seg_fp h4 using
      all_goals (try wg1_values)
      all_goals
        rw [pack_words hlow128 (by decide : (16392 : Nat) < 2 ^ 32)]
        simp only [pDesc]
        exact congrArg b64 (by omega)
  unfold pPrepFacts at h5
  have hlow256 : descLo (L.sharedBase + 204800) + 4194304 + 256 < 2 ^ 32 := by
    omega
  obtain ⟨t6, hr6, h6⟩ : ∃ t6, run kernel asms L g 1 t5 = some t6 ∧
      At t6 1994 ((850, b32 (descLo (L.sharedBase + 204800) + 4194304 + 256)) ::
        pPrepFacts P L g [485, 3093, 3096, 3102]) := by
    unfold pPrepFacts
    seg_fp h5 using
      all_goals norm_bits
  unfold pPrepFacts at h6
  obtain ⟨t7, hr7, h7⟩ : ∃ t7, run kernel asms L g 1 t6 = some t7 ∧
      At t7 1995 (factsAt P L g 1995 ⟨.qCopyFence, 0⟩) := by
    seg_fp h6 using
      all_goals (try wg1_values)
      all_goals
        rw [pack_words hlow256 (by decide : (16392 : Nat) < 2 ^ 32)]
        simp only [pDesc]
        exact congrArg b64 (by omega)
  exact ⟨t7, run_comp (run_comp (run_comp hr1 hr2) (run_comp hr3 hr4))
    (run_comp (run_comp hr5 hr6) hr7), h7⟩

private theorem init_count {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}
    (hpre : Pre P L mem0) (h : At t 1995 (factsAt P L g 1995 ⟨.qCopyFence, 0⟩)) :
    ∃ t', run kernel asms L g 5 t = some t' ∧
      At t' 2000 (factsAt P L g 2000 ⟨.kvWait, 0⟩) := by
  have htotal : total P L g < 2 ^ 31 := total_lt hpre
  have hcount := blocks_lt_two_pow (g := g) hpre
  have hpos := blocks_pos P L g
  have hneg : i32Bits (((0 : Nat) : Int) - (blocks P L g : Int)) = 2 ^ 32 - blocks P L g := by
    simpa only [Nat.cast_zero, zero_sub] using countEncoding_neg hpos hcount
  let descs := factsFrom [3093, 3096, 3099, 3102] (valueOf P L g ⟨.kvWait, 0⟩)
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
      At t1 1996 ((851, b32 0) :: (485, b32 (total P L g)) :: descs) := by
    dsimp only [descs]
    seg_fp h using
      all_goals (try wg1_values)
      all_goals first | exact shr31_value htotal | rfl
  dsimp only [descs] at h1
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 2 t1 = some t2 ∧
      At t2 1998 ((853, b32 (total P L g)) :: descs) := by
    dsimp only [descs]
    seg_fp h1 using
      all_goals first | rfl | norm_bits
  dsimp only [descs] at h2
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
      At t3 1999 ((854, b32 (blocks P L g)) :: descs) := by
    dsimp only [descs]
    seg_fp h2 using
      all_goals first | exact shr6_value htotal | rfl
  dsimp only [descs] at h3
  obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 1 t3 = some t4 ∧
      At t4 2000 (factsAt P L g 2000 ⟨.kvWait, 0⟩) := by
    seg_fp h3 using
      all_goals (try wg1_values)
      all_goals first | rfl | (rw [hneg]; exact neg_value hpos hcount)
  exact ⟨t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, h4⟩

private theorem enter_loop {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}
    (hpre : Pre P L mem0) (h : At t 1988 (factsAt P L g 1987 ⟨.qCopyFence, 0⟩)) :
    ∃ t', run kernel asms L g 15 t = some t' ∧ At t' 2003 (facts2003 P L g 0) := by
  obtain ⟨t1, hr1, h1⟩ := init_p_descriptors h
  obtain ⟨t2, hr2, h2⟩ := init_count hpre h1
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 3 t2 = some t3 ∧
      At t3 2003 (facts2003 P L g 0) := by
    unfold facts2003
    seg_fp h2 using
      all_goals (try wg1_values)
      all_goals rfl
  exact ⟨t3, run_comp (run_comp hr1 hr2) hr3, h3⟩

/-- **The copy fence's step** (pc 1986): the fence, the padded total's test (which the total's
lower bound makes false) and the block loop's head reach the first block's dequant wait. -/
theorem step_qCopyFence (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.qCopyFence, i⟩ t) (hinv : Inv P L g ⟨.qCopyFence, i⟩)
    (hc : kernel.code[(Site.qCopyFence).pc]? = some ins)
    (hf : Fires (Site.qCopyFence).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qCopyFence, i⟩ e u := by
  have hpc : (Site.qCopyFence).pc = 1986 := rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_6)
  obtain hu := fires_async_next (A := asms) (op := .tcFenceAfter) trivial hf
  have hi : i = 0 := hinv.prefix_i (by simp [PrefixSite])
  subst i
  have h0 : At u 1987 (facts P L g ⟨.qCopyFence, 0⟩) := by
    rw [hu]; exact at_next hat
  have hlt : ¬ (total P L g < 64) := by
    have := total_ge P L g
    omega
  obtain ⟨t1, hr1, h1⟩ := run_bra_to (L := L) (g := g) (pc := 1987) (target := 2158)
    (p := 62) (pick := total P L g < 64) Flow.code_1987 h0
    (by
          apply mem_fact (pc := 1986) (r := 62)
          · change 62 ∈ Flow.live 1986
            decide +kernel
          · wg1_values)
    (b := 1988) (by rw [if_neg (by simpa using hlt)])
  obtain ⟨t2, hr2, h2⟩ := enter_loop hpre h1
  obtain ⟨t3, hr3, h3⟩ := loop_head_to_wait hpre h2
  have hinv' : Inv P L g ⟨.kvWait, 0⟩ := by
    refine ⟨hinv.warp, hinv.lane, hinv.blocks_pos, ?_, ?_, ?_, ?_, hinv.qmap,
      hinv.qk_desc, hinv.pv_desc, hinv.tmem_base, hinv.tmem_ranges⟩
    · show 0 ≤ blocks P L g
      omega
    · intro _
      exact hinv.blocks_pos
    · intro hp
      exact absurd hp (by simp [PrefixSite])
    · intro ho
      exact absurd ho (by simp)
  refine step_advance (d' := ⟨.kvWait, 0⟩) ?_ hu ⟨t3, run_comp (run_comp hr1 hr2) hr3, h3⟩ hinv'
  simp only [code, next, hlt, Bool.false_eq_true, ↓reduceIte]

/-! ## The QK and PV issue sequences -/

/-- Close the column, barrier address, or accumulation predicate written after an MMA. -/
macro "mma_value" block:term : tactic =>
  `(tactic| first
    | (show Value.pred _ = Value.pred true
       nf_simp [PTX.compare, Value.pred.injEq]
       decide)
    | (show Value.pred _ = _; by_cases h : $block = 0
       · have hb : ($block != 0) = false := by simp [h]
         nf_simp [h, hb, PTX.compare, Value.pred.injEq]
         decide
       · have hb : ($block != 0) = true := bne_iff_ne.mpr h
         nf_simp [h, hb, PTX.compare, Value.pred.injEq]
         decide)
    | (show Value.bits _ _ = _; norm_bits [qkACol, pvDest, tmemQ, tmemO, Fin.val_mk, phaseOf,
        qkDoneAddr_eq, svDoneAddr_eq, soReadyAddr_eq, sb]))

/-- Check the segment from the last MMA issue to its commit. -/
macro "prove_mma_step " name:ident "," src:term "," pc:num "," after:num ","
    dst:term "," dest:num "," len:num "," op:term "," fire:term : command =>
  `(command| private theorem $name (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0}
      {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
      (hat : (code P L g).AtD ⟨$src, i⟩ t) (hinv : Inv P L g ⟨$src, i⟩)
      (hc : kernel.code[(Site.pc $src)]? = some ins)
      (hf : Fires (Site.pc $src) (eventTmpl asms L g t ins.op) e (some u)) :
      Step P L g ⟨$src, i⟩ e u := by
    have hpc : Site.pc $src = $pc := rfl
    rw [hpc] at hc hf
    have hins := Option.some.inj (hc.symm.trans $op)
    subst ins
    obtain hu := $fire (A := asms) hf
    have h0 : At u $after (facts P L g ⟨$src, i⟩) := by
      rw [hu]
      exact at_next hat
    have hbase := sharedBase_lt hpre
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g $len u = some t' ∧
        At t' $dest (facts P L g ⟨$dst, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals mma_value i
    refine step_advance (d' := ⟨$dst, i⟩) ?_ hu ⟨t', hr, ht⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite]))

/-- Check one MMA issue and the add, pack, and local updates that prepare its successor. -/
macro "prove_mma_pack_step " name:ident "," src:term "," pc:num "," after:num ","
    dst:term "," dest:num "," tail:num "," op:term "," tmp:num "," add:num "," low:num "," fire:term : command =>
  `(command| private theorem $name (P : Params) (L : Launch) (g i : Nat) {mem0 : Mem0}
      {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
      (hat : (code P L g).AtD ⟨$src, i⟩ t) (hinv : Inv P L g ⟨$src, i⟩)
      (hc : kernel.code[(Site.pc $src)]? = some ins)
      (hf : Fires (Site.pc $src) (eventTmpl asms L g t ins.op) e (some u)) :
      Step P L g ⟨$src, i⟩ e u := by
    have hpc : Site.pc $src = $pc := rfl
    rw [hpc] at hc hf
    have hins := Option.some.inj (hc.symm.trans $op)
    subst ins
    obtain hu := $fire (A := asms) hf
    have h0 : At u $after (facts P L g ⟨$src, i⟩) := by
      rw [hu]
      exact at_next hat
    have hdesc := descLo_lt (kvBase L i)
    have hlow : descLo (kvBase L i) + $low + $add < 2 ^ 32 := by
      norm_num at hdesc ⊢
      omega
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
        At t1 ($after + 1) (($tmp, b32 (descLo (kvBase L i) + $low + $add)) ::
          facts P L g ⟨$src, i⟩) := by
      seg_fp h0 using
        all_goals (try wg1_values)
        all_goals norm_bits
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
        At t2 ($after + 2) (factsAt P L g ($after + 2) ⟨$src, i⟩) := by
      seg_fp h1 using
        all_goals (try wg1_values)
        all_goals
          rw [pack_words hlow (by decide : (1073758272 : Nat) < 2 ^ 32)]
          simp only [kDesc, vDesc, qkBDelta, pvBDelta]
          exact congrArg b64 (by omega)
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g $tail t2 = some t3 ∧
        At t3 $dest (facts P L g ⟨$dst, i⟩) := by
      seg_fp h2 using
        all_goals (try wg1_values)
        all_goals mma_value i
    refine step_advance (d' := ⟨$dst, i⟩) ?_ hu
      ⟨t3, run_comp (run_comp hr1 hr2) hr3, h3⟩ ?_
    · simp [code, next, nextSite]
    · exact inv_loop hinv (by simp [LoopSite]) (by simp [LoopSite]))

prove_mma_pack_step step_qkMma_0, (.qkMma 0), 2027, 2028, (.qkMma 1), 2033, 3, Flow.code_mma_0, 894, 2, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_1, (.qkMma 1), 2033, 2034, (.qkMma 2), 2038, 2, Flow.code_mma_1, 895, 4, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_2, (.qkMma 2), 2038, 2039, (.qkMma 3), 2043, 2, Flow.code_mma_2, 896, 6, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_3, (.qkMma 3), 2043, 2044, (.qkMma 4), 2048, 2, Flow.code_mma_3, 897, 1024, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_4, (.qkMma 4), 2048, 2049, (.qkMma 5), 2053, 2, Flow.code_mma_4, 898, 1026, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_5, (.qkMma 5), 2053, 2054, (.qkMma 6), 2058, 2, Flow.code_mma_5, 899, 1028, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_6, (.qkMma 6), 2058, 2059, (.qkMma 7), 2063, 2, Flow.code_mma_6, 900, 1030, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_7, (.qkMma 7), 2063, 2064, (.qkMma 8), 2068, 2, Flow.code_mma_7, 901, 2048, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_8, (.qkMma 8), 2068, 2069, (.qkMma 9), 2073, 2, Flow.code_mma_8, 902, 2050, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_9, (.qkMma 9), 2073, 2074, (.qkMma 10), 2078, 2, Flow.code_mma_9, 903, 2052, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_10, (.qkMma 10), 2078, 2079, (.qkMma 11), 2083, 2, Flow.code_mma_10, 904, 2054, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_11, (.qkMma 11), 2083, 2084, (.qkMma 12), 2088, 2, Flow.code_mma_11, 905, 3072, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_12, (.qkMma 12), 2088, 2089, (.qkMma 13), 2093, 2, Flow.code_mma_12, 906, 3074, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_13, (.qkMma 13), 2093, 2094, (.qkMma 14), 2098, 2, Flow.code_mma_13, 907, 3076, 65536, fires_tcMmaTs_ws
prove_mma_pack_step step_qkMma_14, (.qkMma 14), 2098, 2099, (.qkMma 15), 2103, 2, Flow.code_mma_14, 908, 3078, 65536, fires_tcMmaTs_ws
prove_mma_step step_qkMma_15, (.qkMma 15), 2103, 2104, .qkCommit, 2105, 1, Flow.code_mma_15, fires_tcMmaTs_ws

/-- **The sixteen QK MMAs** (pcs 2027-2103): each `tcgen05.mma.ws` fires and the local
instructions that follow form the next MMA's B descriptor, A column and enable predicate. -/
theorem step_qkMma (P : Params) (L : Launch) (g i : Nat) (k : Fin 16) {mem0 : Mem0}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.qkMma k, i⟩ t) (hinv : Inv P L g ⟨.qkMma k, i⟩)
    (hc : kernel.code[(Site.qkMma k).pc]? = some ins)
    (hf : Fires (Site.qkMma k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.qkMma k, i⟩ e u := by
  revert hat hinv hc hf
  fin_cases k <;> intro hat hinv hc hf
  · exact step_qkMma_0 P L g i hpre hat hinv hc hf
  · exact step_qkMma_1 P L g i hpre hat hinv hc hf
  · exact step_qkMma_2 P L g i hpre hat hinv hc hf
  · exact step_qkMma_3 P L g i hpre hat hinv hc hf
  · exact step_qkMma_4 P L g i hpre hat hinv hc hf
  · exact step_qkMma_5 P L g i hpre hat hinv hc hf
  · exact step_qkMma_6 P L g i hpre hat hinv hc hf
  · exact step_qkMma_7 P L g i hpre hat hinv hc hf
  · exact step_qkMma_8 P L g i hpre hat hinv hc hf
  · exact step_qkMma_9 P L g i hpre hat hinv hc hf
  · exact step_qkMma_10 P L g i hpre hat hinv hc hf
  · exact step_qkMma_11 P L g i hpre hat hinv hc hf
  · exact step_qkMma_12 P L g i hpre hat hinv hc hf
  · exact step_qkMma_13 P L g i hpre hat hinv hc hf
  · exact step_qkMma_14 P L g i hpre hat hinv hc hf
  · exact step_qkMma_15 P L g i hpre hat hinv hc hf

prove_mma_pack_step step_pvMma_0, (.pvMma 0), 2117, 2118, (.pvMma 1), 2122, 2, Flow.code_mma_16, 911, 2048, 33554432, fires_tcMma_ws
prove_mma_pack_step step_pvMma_1, (.pvMma 1), 2122, 2123, (.pvMma 2), 2126, 1, Flow.code_mma_17, 912, 128, 33554432, fires_tcMma_ws
prove_mma_pack_step step_pvMma_2, (.pvMma 2), 2126, 2127, (.pvMma 3), 2130, 1, Flow.code_mma_18, 913, 2176, 33554432, fires_tcMma_ws
prove_mma_pack_step step_pvMma_3, (.pvMma 3), 2130, 2131, (.pvMma 4), 2134, 1, Flow.code_mma_19, 914, 256, 33554432, fires_tcMma_ws
prove_mma_pack_step step_pvMma_4, (.pvMma 4), 2134, 2135, (.pvMma 5), 2138, 1, Flow.code_mma_20, 915, 2304, 33554432, fires_tcMma_ws
prove_mma_pack_step step_pvMma_5, (.pvMma 5), 2138, 2139, (.pvMma 6), 2142, 1, Flow.code_mma_21, 916, 384, 33554432, fires_tcMma_ws
prove_mma_pack_step step_pvMma_6, (.pvMma 6), 2142, 2143, (.pvMma 7), 2146, 1, Flow.code_mma_22, 917, 2432, 33554432, fires_tcMma_ws
prove_mma_step step_pvMma_7, (.pvMma 7), 2146, 2147, .pvCommit, 2148, 1, Flow.code_mma_23, fires_tcMma_ws

/-- **The eight PV MMAs** (pcs 2117-2146): each fires and the local instructions that follow form
the next MMA's V descriptor and its enable predicate. -/
theorem step_pvMma (P : Params) (L : Launch) (g i : Nat) (k : Fin 8) {mem0 : Mem0}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD ⟨.pvMma k, i⟩ t) (hinv : Inv P L g ⟨.pvMma k, i⟩)
    (hc : kernel.code[(Site.pvMma k).pc]? = some ins)
    (hf : Fires (Site.pvMma k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g ⟨.pvMma k, i⟩ e u := by
  revert hat hinv hc hf
  fin_cases k <;> intro hat hinv hc hf
  · exact step_pvMma_0 P L g i hpre hat hinv hc hf
  · exact step_pvMma_1 P L g i hpre hat hinv hc hf
  · exact step_pvMma_2 P L g i hpre hat hinv hc hf
  · exact step_pvMma_3 P L g i hpre hat hinv hc hf
  · exact step_pvMma_4 P L g i hpre hat hinv hc hf
  · exact step_pvMma_5 P L g i hpre hat hinv hc hf
  · exact step_pvMma_6 P L g i hpre hat hinv hc hf
  · exact step_pvMma_7 P L g i hpre hat hinv hc hf

/-! ## The role machine -/

/-- Every event instruction preserves the role invariant at its successor or terminates. -/
theorem stepAt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (d : D) : (code P L g).StepAt d := by
  obtain ⟨s, i⟩ := d
  refine ⟨fun _ => site_event P L g ⟨s, i⟩, ?_⟩
  intro t e u ins hat hinv hc hf
  cases s with
  | head =>
    have hi : i = 0 := hinv.prefix_i (by simp [PrefixSite])
    subst i
    exact (step_head hpre).step (ins := ins) hat hinv hc hf
  | elect => exact step_elect P L g i hpre hat hinv hc hf
  | loadTopk => exact step_loadTopk P L g i hpre hat hinv hc hf
  | loadExtra => exact step_loadExtra P L g i hpre hat hinv hc hf
  | qLoad k => exact step_qLoad P L g i k hpre hat hinv hc hf
  | qArrive => exact step_qArrive P L g i hpre hat hinv hc hf
  | qWait => exact step_qWait P L g i hpre hat hinv hc hf
  | qFence => exact step_qFence P L g i hpre hat hinv hc hf
  | qCopy k => exact step_qCopy P L g i k hpre hat hinv hc hf
  | qCopyCommit => exact step_qCopyCommit P L g i hpre hat hinv hc hf
  | qCopyWait => exact step_qCopyWait P L g i hpre hat hinv hc hf
  | qCopyFence => exact step_qCopyFence P L g i hpre hat hinv hc hf
  | kvWait => exact step_kvWait P L g i hpre hat hinv hc hf
  | kvFence => exact step_kvFence P L g i hpre hat hinv hc hf
  | qkMma k => exact step_qkMma P L g i k hpre hat hinv hc hf
  | qkCommit => exact step_qkCommit P L g i hpre hat hinv hc hf
  | soWait => exact step_soWait P L g i hpre hat hinv hc hf
  | soFence => exact step_soFence P L g i hpre hat hinv hc hf
  | pvMma k => exact step_pvMma P L g i k hpre hat hinv hc hf
  | pvCommit => exact step_pvCommit P L g i hpre hat hinv hc hf
  | outBar => exact step_outBar P L g i hpre hat hinv hc hf
  | exit => exact step_exit P L g i hat hc hf

/-- The site's soundness obligations for the kernel's hand-off machine. -/
theorem steps {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    ∀ d, (code P L g).StepAt d :=
  stepAt hpre

/-! ## The launch prefix and role hand-off -/

/-- The shared launch prefix of the warp-4 machine. -/
abbrev prologueCode (L : Launch) (g : Nat) :=
  _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.code L g

/-- States before the MMA role receives control. -/
abbrev LaunchSite :=
  _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Site

/-- A warp-4 thread enters the MMA role at the warpgroup-1 register-limit event. -/
def launchNext (P : Params) (L : Launch) (g : Nat) :
    Sum LaunchSite D → Event → Option (Option (Sum LaunchSite D))
  | .inl s, e =>
    match (prologueCode L g).next s e with
    | none => none
    | some (some s') => some (some (.inl s'))
    | some none => if s = .handoff 1 then some (some (.inr init)) else some none
  | .inr d, e => ((code P L g).next d e).map (Option.map Sum.inr)

/-- The actual launch prefix followed by the warp-4 MMA role. -/
def launchCode (P : Params) (L : Launch) (g : Nat) : PTX.Flow.Code kernel asms L g where
  D := Sum LaunchSite D
  init := .inl (prologueCode L g).init
  pc := Sum.elim (prologueCode L g).pc (code P L g).pc
  sub := Sum.elim (prologueCode L g).sub (code P L g).sub
  acc := Sum.elim (prologueCode L g).acc (code P L g).acc
  facts := Sum.elim (prologueCode L g).facts (code P L g).facts
  inv := Sum.elim (prologueCode L g).inv (code P L g).inv
  next := launchNext P L g

/-- The warp-4 machine starts in the empty thread state and runs the shared prologue. -/
def machine (P : Params) (L : Launch) (g : Nat) : PTX.Flow.Machine kernel asms L g :=
  (launchCode P L g).toMachine

end Wg1Mma
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

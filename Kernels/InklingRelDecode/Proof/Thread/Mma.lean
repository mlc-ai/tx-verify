-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Sites
public import Kernels.InklingRelDecode.Flow.Code
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Next
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.RegBits
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Lemmas.Flow.Tc
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Join
public import Lemmas.Flow.BitForms
public import Lemmas.Flow.TcMmaTs
public import Mathlib.Tactic.FinCases
public import Kernels.InklingRelDecode.Proof.Thread.RawWord

@[expose] public section

/-! # The MMA warp (warp 7) as a code machine

The MMA warp is worker warp 7 of the dispatch table (index 1, pcs 2422-2556). It lowers its
register count (`setmaxnreg.dec 24`), reads `num_iters` from shared memory (`[global_smem+212996]`),
meets the default partition at `barrier.sync 1`, and runs the source's `_verify_mma` loop: for
`i = 0 .. num_iters` it issues `S = Q Kᵀ` for block `i` when `i < num_iters` (wait on
`kv_ready[i % 3]`, eight `tcgen05.mma` into `s_tmem[i % 2]`, commit to `s_ready[i % 2]`), and
`O += P V` for block `i - 1` when `i > 0` (wait on `p_ready[(i - 1) % 2]`, eight `tcgen05.mma`
into `o_tmem`, commits to `kv_empty[(i - 1) % 3]` and `o_done`). After the loop one commit to
`o_final`, `barrier.sync 1` and `setmaxnreg.inc 256` return to the worker dispatch.

All 32 lanes run the role. Each wait is preceded by `bar.warp.sync` and followed by a broadcast of
the warp index (`shfl.sync.idx` of `%r3`, lane 0) and a second `bar.warp.sync`; after it the code
branches past the half when the received word is not 7 (`setp.ne.b32`, `@%p8 bra`, `@%p13 bra`).
The machine follows both branches: a lane whose word is 7 reaches `qkBar2` (`pvBar2`), any other
word with bits reaches `qkSkip` (`pvSkip`), the same barrier on the branch that skips the half;
a word without bits faults at the comparison. The machine does not depend on the warp: the
broadcast operand is the inherited warp index (`pro 464`), so it runs on any warp the role byte
sends to it. In warp 7 the received word is lane 0's operand, 7, unless lane 0 exited before the
broadcast: the layers above show that this never happens.
The MMA blocks and the commits are guarded by an `elect.sync` predicate: the elected lane performs
the eight MMAs and the commits; the other lanes skip them as local steps.

A state is the next event with the iteration `i`, `num_iters` (`n`, read from memory), the Tensor
Memory base (`tm`, the value of `%r2` the prologue allocated) and the registers the prologue set
that this role only carries (`pro`). Every address, parity, descriptor and predicate the code
computes is a function of `(i, n, tm)` and the shared base in the value table. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### Assumptions -/

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ### Descriptors -/

/-- The fixed high word of every shared-memory descriptor (`0x40004040`). -/
abbrev descHi : Nat := 1073758272

/-- A 64-bit shared-memory descriptor of an MMA operand with low word `lo` (the Q and K
descriptors). -/
def desc (lo : Nat) : Value := b64 (lo + descHi * 2 ^ 32)

/-- A 64-bit descriptor of a V operand: the same high word with bit 26 of the low word set (the
leading-dimension byte offset field). -/
def vdesc (lo : Nat) : Value := b64 (lo + 2 ^ 26 + descHi * 2 ^ 32)

/-- The start address field of the Q tile's descriptor: `(sharedBase + 196608) >> 4`. -/
def qLo (L : Launch) : Nat := (L.sharedBase + 196608) / 16

/-- The start address field of the K tile of ring slot `s`. -/
def kLo (L : Launch) (s : Nat) : Nat := (L.sharedBase + 32768 * s) / 16

/-- The start address field of the V tile of ring slot `s`. -/
def vLo (L : Launch) (s : Nat) : Nat := (L.sharedBase + 98304 + 32768 * s) / 16

/-- The QK and PV instruction descriptors. -/
abbrev qkIdesc : Nat := 69207184
abbrev pvIdesc : Nat := 69272720

/-! ### Sites -/

/-- The event instructions of the MMA warp. -/
inductive Site where
  /-- `setmaxnreg.dec`, then the read of `num_iters` and `barrier.sync 1`. -/
  | setMaxReg | ldNum | bar0
  /-- Iteration `i < n`: `bar.warp.sync`, the `kv_ready` poll, the broadcast of the warp index,
  `bar.warp.sync`, the election, the eight QK MMAs and the `s_ready` commit. -/
  | qkBar | kvWait | qkShfl | qkBar2 | qkElect
  | qk (j : Fin 8) | qkCommit
  /-- The QK half's second `bar.warp.sync` of a lane whose broadcast word was not 7: the branch
  after it skips the half's MMAs and commit. -/
  | qkSkip
  /-- Iteration `i > 0`: the same for the PV MMAs, with two commits. -/
  | pvBar | pWait | pvShfl | pvBar2 | pvElect
  | pv (j : Fin 8) | pvCommit1 | pvCommit2
  /-- The PV half's second `bar.warp.sync` of a lane whose broadcast word was not 7. -/
  | pvSkip
  /-- After the loop: `bar.warp.sync`, the election, the `o_final` commit, `barrier.sync 1`,
  `setmaxnreg.inc` and the return to the dispatch. -/
  | finBar | finElect | finCommit | bar1 | setMaxRegInc
  deriving DecidableEq

/-- The `tcgen05.mma` of the QK block, and of the PV block. -/
def qkPc : Fin 8 → Nat
  | 0 => Flow.mma_0 | 1 => Flow.mma_1 | 2 => Flow.mma_2 | 3 => Flow.mma_3
  | 4 => Flow.mma_4 | 5 => Flow.mma_5 | 6 => Flow.mma_6 | 7 => Flow.mma_7

def pvPc : Fin 8 → Nat
  | 0 => Flow.mma_8 | 1 => Flow.mma_9 | 2 => Flow.mma_10 | 3 => Flow.mma_11
  | 4 => Flow.mma_12 | 5 => Flow.mma_13 | 6 => Flow.mma_14 | 7 => Flow.mma_15

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_7 | .ldNum => Flow.load_207 | .bar0 => Flow.bar_30
  | .qkBar => Flow.warpBar_5 | .kvWait => Flow.mbarWait_3 | .qkShfl => Flow.shfl_13
  | .qkBar2 => Flow.warpBar_6 | .qkElect => Flow.elect_28 | .qk j => qkPc j
  | .qkCommit => Flow.tcCommit_0 | .qkSkip => Flow.warpBar_6
  | .pvBar => Flow.warpBar_7 | .pWait => Flow.mbarWait_4 | .pvShfl => Flow.shfl_14
  | .pvBar2 => Flow.warpBar_8 | .pvElect => Flow.elect_29 | .pv j => pvPc j
  | .pvCommit1 => Flow.tcCommit_1 | .pvCommit2 => Flow.tcCommit_2 | .pvSkip => Flow.warpBar_8
  | .finBar => Flow.warpBar_9 | .finElect => Flow.elect_30 | .finCommit => Flow.tcCommit_3
  | .bar1 => Flow.bar_31 | .setMaxRegInc => Flow.setMaxReg_8

/-- The barrier of a lane whose broadcast word was not 7. -/
def Site.isSkip : Site → Bool
  | .qkSkip | .pvSkip => true
  | _ => false

/-- Two sites at one program counter are one site, except a barrier after a broadcast and the
same barrier on the branch that skips the half. -/
theorem Site.eq_of_pc {a b : Site} (ha : a.isSkip = false) (hb : b.isSkip = false)
    (h : a.pc = b.pc) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | (exfalso; revert ha hb h; decide +kernel)
    | (rename_i j j'; revert ha hb h; revert j j'; decide +kernel)
    | (exfalso; rename_i j; revert ha hb h; revert j; decide +kernel)

/-! ### Abstract states and values -/

structure D where
  site : Site
  /-- The iteration of the loop. -/
  i : Nat
  /-- `num_iters`, as read from shared memory. -/
  n : Nat
  /-- The Tensor Memory base (`%r2`). -/
  tm : Nat
  /-- The registers the prologue set that this role only carries. -/
  pro : Nat → Value

/-- The value of every register the MMA warp's code uses, at iteration `i` (decoder register
ids: `%rK` is `461 + K`, `%rdK` is `1948 + K`, `%pK` is `K`). Registers of the iteration are
valued at the iteration `i`; the registers of the PV half are valued by the block `i - 1` they
work on. The two predicates of the tests of the broadcast word (`%p8`, `%p13`) are true exactly at
the barrier of a lane that skips the half (`qkSkip`, `pvSkip`). -/
def values (L : Launch) (d : D) : List (Nat × Value) :=
  let sb := L.sharedBase
  let i := d.i
  let n := d.n
  let q := qLo L
  let kl := kLo L (i % 3)
  let vl := vLo L ((i - 1) % 3)
  [ (8, .pred (decide (d.site = .qkSkip))), (13, .pred (decide (d.site = .pvSkip))),
    -- the prologue registers this role reads: Tensor Memory base, warp index (the inherited
    -- word: the role runs on any warp), shared base
    (463, b32 d.tm), (464, d.pro 464), (534, b32 sb),
    -- the loop state (`%r10`, the loaded `num_iters` word, is `pro 471`)
    (472, b32 (n + 1)), (564, b32 (d.tm + 256)),
    (1911, b32 i), (1910, b32 ((sb + 213216 + 8 * i) % 2 ^ 32)),
    (1909, b32 ((sb + 32768 * i) % 2 ^ 32)), (1908, b32 ((sb + 213240 + 8 * i) % 2 ^ 32)),
    (1907, b32 ((i + 4294967295) % 2 ^ 32)), (1906, b32 ((sb + 65536 + 32768 * i) % 2 ^ 32)),
    -- the Q descriptors
    (2027, desc q), (2029, desc (q + 2)), (2031, desc (q + 4)), (2033, desc (q + 6)),
    (2035, desc (q + 512)), (2037, desc (q + 514)), (2039, desc (q + 516)),
    (2041, desc (q + 518)),
    -- the QK half: ring slot, parity, barrier addresses, accumulator column, K descriptors
    (473, b32 (i / 3)), (474, b32 (sb + 213216 + 8 * (i % 3))), (545, b32 (i / 3 % 2)),
    (475, b32 (sb + 32768 * (i % 3))), (547, b32 (d.tm + 128 * (i % 2))),
    (549, b32 (sb + 213280 + 8 * (i % 2))), (548, b32 qkIdesc),
    (2043, b64 kl), (2028, desc kl), (2030, desc (kl + 2)), (2032, desc (kl + 4)),
    (2034, desc (kl + 6)), (2036, desc (kl + 1024)), (2038, desc (kl + 1026)),
    (2040, desc (kl + 1028)), (2042, desc (kl + 1030)),
    -- the PV half: parity, barrier addresses, P column, V descriptors
    (477, b32 ((i - 1) % 2)), (557, b32 (sb + 213296 + 8 * ((i - 1) % 2))),
    (558, b32 ((i - 1) / 2 % 2)), (561, b32 sb), (476, b32 (sb + 98304 + 32768 * ((i - 1) % 3))),
    (565, b32 (d.tm + 128 * ((i - 1) % 2))), (567, b32 (sb + 213248 + 8 * ((i - 1) % 3))),
    (566, b32 pvIdesc), (2052, b64 vl), (2044, vdesc vl), (2045, vdesc (vl + 128)),
    (2046, vdesc (vl + 256)), (2047, vdesc (vl + 384)), (2048, vdesc (vl + 512)),
    (2049, vdesc (vl + 640)), (2050, vdesc (vl + 768)), (2051, vdesc (vl + 896)),
    (568, b32 (sb + 213312)), (572, b32 (sb + 213328)),
    -- the predicates: the lane is elected where the MMAs and commits run (the other lanes'
    -- segments state their own), the enable flags
    (6, .pred (decide (2147483646 < n))), (7, .pred (decide (n ≤ i))),
    (9, .pred false), (10, .pred true), (11, .pred true),
    (12, .pred (decide (i = 0))), (14, .pred (decide (i ≠ 1))),
    (15, .pred true), (16, .pred true), (17, .pred (decide (n + 1 ≠ i))), (18, .pred true) ]

def valueOf (L : Launch) (d : D) (r : Nat) : Value :=
  ((values L d).lookup r).getD (d.pro r)

/-- Only the two predicates of the broadcast tests depend on the site. -/
theorem valueOf_site (L : Launch) (d : D) (s : Site) {r : Nat} (h8 : r ≠ 8) (h13 : r ≠ 13) :
    valueOf L { d with site := s } r = valueOf L d r := by
  have e8 : (r == 8) = false := by simpa using h8
  have e13 : (r == 13) = false := by simpa using h13
  simp only [valueOf, values, List.lookup_cons, e8, e13]

def factsAt (L : Launch) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L d)

abbrev facts (L : Launch) (d : D) : List (Nat × Value) := factsAt L d.site.pc d

/-- The sites of an iteration's QK half. -/
def QkSite : Site → Prop
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => True
  | _ => False

/-- The sites of an iteration's PV half. -/
def PvSite : Site → Prop
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2
  | .pvSkip => True
  | _ => False

/-- The sites before the loop. -/
def PreSite : Site → Prop
  | .setMaxReg | .ldNum | .bar0 => True
  | _ => False

/-- The sites after the loop. -/
def EndSite : Site → Prop
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc => True
  | _ => False

/-- The invariant of a state: `num_iters` and the Tensor Memory base are 32-bit values with
room for the 512 columns, and the base's column field (its low 16 bits) has room for them too
(`col`: the dispatch enters the role only with such a base word, `WComp.roleStart`); the sites
before the loop are at iteration 0; a QK site is in an iteration below `num_iters`, a PV site in
an iteration from 1 to `num_iters`, and `num_iters + 1` fits the signed 32-bit loop counter.
The register `%r10` (`pro 471`) holds the loaded word, which
the code reads as the 32-bit number `n` (`wd`); at `barrier.sync 1` it may hold a value without
bits (`wd0`), which the next local instruction faults on. After the loop the iteration is 0 only
when the loop did not run (`fin0`: `num_iters` is 0 or not below `2 ^ 31 - 1`). -/
structure Inv (d : D) : Prop where
  n : d.n < 2 ^ 32
  tm : d.tm + 512 < 2 ^ 32
  col : d.tm + 512 ≤ 2 ^ 16
  pre : PreSite d.site → d.i = 0
  qk : QkSite d.site → d.i < d.n ∧ d.n ≤ 2147483646
  pv : PvSite d.site → 1 ≤ d.i ∧ d.i ≤ d.n ∧ d.n ≤ 2147483646
  wd : ¬ PreSite d.site → Raw.word32Of (d.pro 471) = some d.n
  wd0 : d.site = .bar0 → ∀ m, Raw.word32Of (d.pro 471) = some m → m = d.n
  fin0 : EndSite d.site → d.i = 0 → d.n = 0 ∨ 2147483646 < d.n

/-! ### Transitions -/

/-- The state at the top of iteration `i + 1`, after the end of iteration `i`: the loop ends
at `i = n`; otherwise the QK half runs when `i + 1 < n`, and the PV half alone when
`i + 1 = n`. -/
def iterNext (d : D) : D :=
  { d with
    site := if d.i = d.n then .finBar else if d.i + 1 < d.n then .qkBar else .pvBar,
    i := d.i + 1 }

/-- The state after the QK half of iteration `i`: the PV half, except in iteration 0. -/
def afterQk (d : D) : D := if d.i = 0 then iterNext d else { d with site := .pvBar }

/-- The state after the QK MMA `j`, or after the QK commit. -/
def qkNext (d : D) (j : Fin 8) : D :=
  if h : j.val + 1 < 8 then { d with site := .qk ⟨j.val + 1, h⟩ } else { d with site := .qkCommit }

/-- The state after the PV MMA `j`. -/
def pvNext (d : D) (j : Fin 8) : D :=
  if h : j.val + 1 < 8 then { d with site := .pv ⟨j.val + 1, h⟩ } else { d with site := .pvCommit1 }

/-- The first state of the loop, or the end when the loop does not run (`n` is zero, or at least
`2 ^ 31 - 1`, which the code compares as an unsigned number). -/
def start (d : D) : D :=
  if d.n = 0 ∨ 2147483646 < d.n then { d with site := .finBar } else { d with site := .qkBar }

/-- The loaded `num_iters` word as the state keeps it: the value of `%r10` (`pro 471`). The layers
above name it by this function. -/
def numWord (d : D) : Value := d.pro 471

theorem numWord_def (d : D) : numWord d = d.pro 471 := rfl

/-- The abstract successor after event `e`. The loaded `num_iters` word is followed for every
value: it is kept in `%r10` (`pro 471`) and `n` is the 32-bit number the code reads it as; a
word without bits faults at the first instruction after `barrier.sync 1` (`none`), an unreadable
word at the load (`none`). The broadcast word is followed for every value: read as a 32-bit
number it is compared with 7, the lane goes on to the half's MMAs when it is 7 and past them
otherwise (`qkSkip`, `pvSkip`); a word without bits faults at the comparison (`none`). After the
last event the thread returns to the worker dispatch, which this role
does not follow (`some none`). -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg => some (some { d with site := .ldNum })
  | .ldNum =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        some (some ⟨.bar0, d.i, (Raw.word32Of v).getD 0, d.tm, Function.update d.pro 471 v⟩)
      | .error _ => none
    | _ => none
  | .bar0 =>
    match Raw.word32Of (d.pro 471) with
    | some _ => some (some (start d))
    | none => none
  | .qkBar => some (some { d with site := .kvWait })
  | .kvWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .qkShfl } else d))
    | _ => none
  | .qkShfl =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match Raw.word32Of v with
      | some m => some (some { d with site := if m = 7 then .qkBar2 else .qkSkip })
      | none => none
    | _ => none
  | .qkSkip => some (some (afterQk d))
  | .qkBar2 => some (some { d with site := .qkElect })
  | .qkElect =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if laneOf L g = ld then { d with site := .qk 0 } else afterQk d))
    | _ => none
  | .qk j => some (some (qkNext d j))
  | .qkCommit => some (some (afterQk d))
  | .pvBar => some (some { d with site := .pWait })
  | .pWait =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .pvShfl } else d))
    | _ => none
  | .pvShfl =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match Raw.word32Of v with
      | some m => some (some { d with site := if m = 7 then .pvBar2 else .pvSkip })
      | none => none
    | _ => none
  | .pvSkip => some (some (iterNext d))
  | .pvBar2 => some (some { d with site := .pvElect })
  | .pvElect =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if laneOf L g = ld then { d with site := .pv 0 } else iterNext d))
    | _ => none
  | .pv j => some (some (pvNext d j))
  | .pvCommit1 => some (some { d with site := .pvCommit2 })
  | .pvCommit2 => some (some (iterNext d))
  | .finBar => some (some { d with site := .finElect })
  | .finElect =>
    match e.kind with
    | .elect _ _ ld =>
      some (some { d with site := if laneOf L g = ld then .finCommit else .bar1 })
    | _ => none
  | .finCommit => some (some { d with site := .bar1 })
  | .bar1 => some (some { d with site := .setMaxRegInc })
  | .setMaxRegInc => some none

/-- The event is no broadcast, or a broadcast whose received word reads as 7 (the word of warp 7,
which the branch after the broadcast does not skip on). -/
def BcastOk (e : Event) : Prop :=
  ∀ m av bv cv recv ok, e.kind = .shfl m av bv cv recv ok → Raw.word32Of recv = some 7

/-- Every broadcast among the events received a word that reads as 7 (`BcastOk`). -/
def BcastRun (es : List Event) : Prop := ∀ e ∈ es, BcastOk e

theorem BcastRun.take {es : List Event} (h : BcastRun es) (k : Nat) : BcastRun (es.take k) :=
  fun e he => h e (List.mem_of_mem_take he)

/-- **Every broadcast of a thread of warp 7 receives a word that reads as 7**: the received word
is lane 0's operand, the warp index (proved in `Protocol/MmBcast.lean`). -/
def MmaBcast (L : Launch) (X : Execution) : Prop :=
  ∀ g, g < L.threads → g % L.block / 32 = 7 → BcastRun (X.tr g)

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **After a broadcast whose word reads as 7 the machine is not at a skip site.** -/
theorem next_not_skip {L : Launch} {g : Nat} {d d' : D} {e : Event} (hB : BcastOk e)
    (hs : d.site.isSkip = false) (h : next L g d e = some (some d')) : d'.site.isSkip = false := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [Site.isSkip, Bool.true_eq_false] at hs <;>
    simp only [next, iterNext, afterQk, qkNext, start, pvNext] at h <;>
    (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (obtain rfl := Option.some.inj (Option.some.inj h)
       (repeat' split) <;> first
         | rfl
         | (exfalso
            exact ‹¬ _ = 7› (Option.some.inj
              ((‹Raw.word32Of _ = some _›).symm.trans (hB _ _ _ _ _ _ ‹e.kind = _›)))))

/-- The MMA role as a code machine. -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) (tm : Nat)
    (pro : Nat → Value) : Flow.Code kernel A L g where
  D := D
  init := ⟨.setMaxReg, 0, 0, tm, pro⟩
  pc := (·.site.pc)
  facts := facts L
  inv := Inv
  next := next L g

end
end PTX.Kernels.InklingRelDecode.Proof.Mma

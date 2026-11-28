-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Sites
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Facts
public import Lemmas.Flow.RegBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section
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

inductive Site where
  | setMaxReg | ldNum | bar0
  | qkBar | kvWait | qkShfl | qkBar2 | qkSkip | qkElect | qk (j : Fin 8) | qkCommit
  | pvBar | pWait | pvShfl | pvBar2 | pvSkip | pvElect | pv (j : Fin 8) | pvCommit1 | pvCommit2
  | finBar | finElect | finCommit | bar1 | setMaxRegInc | dispatch
  deriving DecidableEq

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
  | .dispatch => 2337

structure D where
  site : Site := .setMaxReg
  i : Nat := 0
  word : Value := b32 0

def low (v : Value) : Nat := (truncBits 32 (v.regBits.getD 0)).toNat
def D.limit (d : D) := low d.word

/-- Value of an address sum whenever the scalar instruction succeeds. -/
def addBase (w : Value) (delta : Nat) : Value :=
  match w with
  | .ptr _ gen target off => .ptr 32 gen target (BitVec.ofInt 64 ((off.toNat : Int) + delta))
  | _ => b32 ((low w + delta) % 2 ^ 32)

def values (L : Launch) (regs : Nat → Value) (w : Value) (d : D) : List (Nat × Value) :=
  let sb := L.sharedBase
  let i := d.i
  let n := d.limit
  let q := qLo L
  let kl := kLo L (i % 3)
  let vl := vLo L ((i - 1) % 3)
  [ (8, .pred (decide (d.site = .qkSkip))), (13, .pred (decide (d.site = .pvSkip))),
    -- the prologue registers this role reads: Tensor Memory base, warp index (the inherited
    -- word: the role runs on any warp), shared base
    (463, w), (464, regs 464), (471, d.word), (534, b32 sb),
    -- the loop state (`%r10`, the loaded `num_iters` word, is `pro 471`)
    (472, b32 (n + 1)), (564, addBase w 256),
    (1911, b32 i), (1910, b32 ((sb + 213216 + 8 * i) % 2 ^ 32)),
    (1909, b32 ((sb + 32768 * i) % 2 ^ 32)), (1908, b32 ((sb + 213240 + 8 * i) % 2 ^ 32)),
    (1907, b32 ((i + 4294967295) % 2 ^ 32)), (1906, b32 ((sb + 65536 + 32768 * i) % 2 ^ 32)),
    -- the Q descriptors
    (2027, desc q), (2029, desc (q + 2)), (2031, desc (q + 4)), (2033, desc (q + 6)),
    (2035, desc (q + 512)), (2037, desc (q + 514)), (2039, desc (q + 516)),
    (2041, desc (q + 518)),
    -- the QK half: ring slot, parity, barrier addresses, accumulator column, K descriptors
    (550, b32 (i % 2)), (551, b32 (128 * (i % 2))),
    (473, b32 (i / 3)), (474, b32 (sb + 213216 + 8 * (i % 3))), (545, b32 (i / 3 % 2)),
    (475, b32 (sb + 32768 * (i % 3))), (547, addBase w (128 * (i % 2))),
    (549, b32 (sb + 213280 + 8 * (i % 2))), (548, b32 qkIdesc),
    (2043, b64 kl), (2028, desc kl), (2030, desc (kl + 2)), (2032, desc (kl + 4)),
    (2034, desc (kl + 6)), (2036, desc (kl + 1024)), (2038, desc (kl + 1026)),
    (2040, desc (kl + 1028)), (2042, desc (kl + 1030)),
    -- the PV half: parity, barrier addresses, P column, V descriptors
    (569, b32 (128 * ((i - 1) % 2))),
    (477, b32 ((i - 1) % 2)), (557, b32 (sb + 213296 + 8 * ((i - 1) % 2))),
    (558, b32 ((i - 1) / 2 % 2)), (561, b32 sb), (476, b32 (sb + 98304 + 32768 * ((i - 1) % 3))),
    (565, addBase w (128 * ((i - 1) % 2))), (567, b32 (sb + 213248 + 8 * ((i - 1) % 3))),
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

def valueOf (L : Launch) (regs : Nat → Value) (w : Value) (d : D) (r : Nat) : Value :=
  ((values L regs w d).lookup r).getD (regs r)

def iterNext (d : D) : D :=
  { d with i := d.i + 1, site := if d.i = d.limit then .finBar
      else if d.i + 1 < d.limit then .qkBar else .pvBar }

def afterQk (d : D) : D :=
  if d.i = 0 then iterNext d else { d with site := .pvBar }

def issueNext (f : Fin 8 → Site) (commit : Site) (j : Fin 8) : Site :=
  if h : j.val + 1 < 8 then f ⟨j.val + 1, h⟩ else commit

def startSite (n : Nat) : Site := if n = 0 ∨ 2147483646 < n then .finBar else .qkBar

def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  let go := fun s => some (some {d with site := s})
  let emit := fun x => some (some x)
  let poll := fun s => match e.kind with
    | .wait _ _ ok _ _ => if ok then go s else emit d
    | _ => none
  let broadcast := fun yes no => match e.kind with
    | .shfl _ _ _ _ v _ => go (if low v = 7 then yes else no)
    | _ => none
  let elect := fun yes other => match e.kind with
    | .elect _ _ lead => if laneOf L g = lead then go yes else emit other
    | _ => none
  match d.site with
  | .setMaxReg => go .ldNum
  | .ldNum => do
    let .rd _ bs := e.kind | none
    let v ← (rebuild 3 bs).toOption
    emit { d with word := v, site := .bar0 }
  | .bar0 => go (startSite d.limit)
  | .qkBar => go .kvWait
  | .kvWait => poll .qkShfl
  | .qkShfl => broadcast .qkBar2 .qkSkip
  | .qkSkip | .qkCommit => emit (afterQk d)
  | .qkBar2 => go .qkElect
  | .qkElect => elect (.qk 0) (afterQk d)
  | .qk j => go (issueNext .qk .qkCommit j)
  | .pvBar => go .pWait
  | .pWait => poll .pvShfl
  | .pvShfl => broadcast .pvBar2 .pvSkip
  | .pvSkip | .pvCommit2 => emit (iterNext d)
  | .pvBar2 => go .pvElect
  | .pvElect => elect (.pv 0) (iterNext d)
  | .pv j => go (issueNext .pv .pvCommit1 j)
  | .pvCommit1 => go .pvCommit2
  | .finBar => go .finElect
  | .finElect => elect .finCommit {d with site := .bar1}
  | .finCommit => go .bar1
  | .bar1 => go .setMaxRegInc
  | .setMaxRegInc => go .dispatch
  | .dispatch => some none

def Inv (d : D) : Prop :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => d.i = 0
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkSkip | .qkElect | .qk _ | .qkCommit =>
    d.i < d.limit ∧ d.limit ≤ 2147483646
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvSkip | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 =>
    0 < d.i ∧ d.i ≤ d.limit ∧ d.limit ≤ 2147483646
  | _ => True

@[reducible] def code (L : Launch) (g : Nat) (regs : Nat → Value) (w : Value) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := {}
  pc := (·.site.pc)
  facts := fun d => factsFrom (Flow.live d.site.pc) (valueOf L regs w d)
  next := next L g
  inv := Inv

end
end PTX.Kernels.InklingRelDecode.Proof.Mma

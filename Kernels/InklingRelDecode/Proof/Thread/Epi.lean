-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Sites
public import Kernels.InklingRelDecode.Flow.Code
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Thread.LaneWord
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
public import Lemmas.Flow.SignedBits
public import Lemmas.Flow.PackMul
public import Lemmas.Flow.MulPairCore
public import Lemmas.Flow.RcpCore
public import Lemmas.Flow.SetpCore
public import Lemmas.Flow.FloatOutcome
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The default partition's epilogue (warps 0-3) as a code machine

After the softmax loop the default partition's warps 0-3 normalize and store the result
(`_verify_softmax`, `attention.py:807-849`; PTX pcs 2560-2855). A thread

* waits on the `o_final` barrier (`mbarrier.try_wait.parity`, pc 2565; a failed poll polls
  again; every thread polls, also the one with `num_iters < 1`), tests the row sum against zero
  (`setp.equ`, pc 2568), takes the reciprocal of the row sum `l` (`selp` of `1.0` on `l == 0`,
  `rcp.approx.ftz`, pcs 2601-2602), broadcasts the warp index (`shfl.sync.idx`, pc 2603), forms
  the Tensor Memory address of its 16 lanes (pcs 2604-2606) and loads its 64 words of the `O`
  tile (`tcgen05.ld.16x32bx2.x64`, pc 2607), then waits for the load (`tcgen05.wait::ld`,
  pc 2608);
* packs the 64 words into 32 pairs (pcs 2609-2640), multiplies every pair by the pair
  `(inv_l, inv_l)` (`mul.f32x2`, pcs 2641-2673) and computes the addresses
  (`LsePart[row]` at pc 2677, `OPart[row][d0 ..]` at pcs 2683-2749);
* stores `LsePart` (one word, by the lane whose bit 4 is clear, pc 2682) and the 64 words of
  `OPart` (pcs 2751-2845, each the half of a product pair), each guarded by the row-valid
  predicate `%p175`;
* meets the other default-partition warps and the workers at the named barrier 1, raises its
  register budget (`setmaxnreg.inc 256`, pc 2847), writes `0x03030303` to the dispatch table
  (`global_smem + 213336`, pc 2848), meets them again, waits at `bar.sync 0`, frees the Tensor
  Memory (`tcgen05.dealloc`, pc 2851, guarded by `%p3`) and returns (pc 2855).

If `num_iters < 1` (`%p173`, `setp.lt.s32 %p173, %r25, 1` at pc 2560) the code, after the poll
and the 33 local instructions of pcs 2567-2599 (the zero pair `%rd531`, the zero test, the 31
copies of the pair), skips the load (`@%p173 bra 2674`, pc 2600): every product is the zero pair
and the thread enters the stores at pc 2682 (`D.sk`).

The abstract state is the next event (`site`), the registers the softmax region leaves and this
region only carries or reads (`Prm`), the 64 words the load returned (`o`, raw values: the
protocol layer ties them to the Tensor Memory cells through the load event) and the branch flag
`sk`. Every register of the code is a function of these (`valueOf`), independent of the site:
the registers a site does not yet or no longer use are dead there and are never read. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

abbrev M32 : Nat := 4294967296
abbrev M64 : Nat := 18446744073709551616

/-! ### Sites -/

/-- The event instructions of the epilogue. -/
inductive Site where
  /-- The poll of the `o_final` barrier. -/
  | wait
  /-- The broadcast of the warp index. -/
  | shfl
  /-- `tcgen05.ld` of the 64 words of the `O` tile, and its `tcgen05.wait::ld`. -/
  | ld | waitLd
  /-- The store of `LsePart[row]`. -/
  | stLse
  /-- The store of word `k` of `OPart[row][d0 ..]`. -/
  | stO (k : Fin 64)
  /-- `barrier.sync 1`, `setmaxnreg.inc 256`, the write of the dispatch table, `barrier.sync 1`,
  `bar.sync 0`. -/
  | bar1 | setMaxInc | stTab | bar2 | bar3
  /-- The guarded `tcgen05.dealloc`, and the return. -/
  | dealloc | exit
  deriving DecidableEq

/-- The pc of store `k` of `OPart`: the pairs' unpacks sit between the stores `2 j + 1` and
`2 j + 2`. -/
def stPc (k : Nat) : Nat := 2751 + k + k / 2

def Site.pc : Site → Nat
  | .wait => Flow.mbarWait_5 | .shfl => Flow.shfl_15 | .ld => Flow.tmemLoad_2
  | .waitLd => Flow.tmemWait_4 | .stLse => Flow.store_11 | .stO k => stPc k.val
  | .bar1 => Flow.bar_34 | .setMaxInc => Flow.setMaxReg_9 | .stTab => Flow.store_76
  | .bar2 => Flow.bar_35 | .bar3 => Flow.bar_36 | .dealloc => Flow.tmemDealloc_0
  | .exit => Flow.exit_0

/-! ### The registers the epilogue inherits -/

/-- The 32-bit pattern of `1.0` and `0.0` as values. -/
abbrev one32 : Value := b32 1065353216
abbrev zero32 : Value := b32 0

/-- The registers the softmax region leaves live at pc 2560 (decoder ids: `%rK` is `461 + K`,
`%rdK` is `1948 + K`, `%pK` is `K`), as the thread's values:

* `%p3` (`p3`): the guard of the Tensor Memory release; `%p175` (`rv`): the row is valid, the
  guard of every store;
* `%r1` (`tid`): the thread index; `%r2` (`tm`): the Tensor Memory base; `%r3` (`w`): the warp
  index (below 4); `%r30` (`c0`): the column base of the `O` tile; `%r163` (`mb`): the address of
  the `o_final` barrier;
* `%r72`, `%r17`, `%r35`, `%r149`, `%r36` (`a b c dd e`): the factors of the output row index
  `((a * b + c) + dd) * 12 + e`, that is `(split * num_tokens + token) * H + head`;
* `%rd8` (`d0`): the first column of the thread's half row; `%rd75`, `%rd76` (`ob`, `lb`): the
  bases of `OPart` and `LsePart`;
* `%r1454` (`l`): the row sum; `%r63` (`lse`): `fma(scale_log2, m, log2 l)`, the value `LsePart`
  takes for a non-empty row. `%p178` (`eq0`), `setp.equ.f32 %p178, l, 0f0`, is computed by the
  epilogue after the poll (pc 2568): `Prm.eq0` is its outcome. -/
structure Prm where
  p3 : Bool
  rv : Bool
  tid : Nat
  tm : Nat
  w : Nat
  c0 : Nat
  mb : Nat
  a : Nat
  b : Nat
  c : Nat
  dd : Nat
  e : Nat
  d0 : Nat
  ob : Nat
  lb : Nat
  l : Value
  lse : Value
  /-- Not a register the softmax region leaves: the lane bits the epilogue's broadcast returned,
  `m % 4` where the received word reads as `m` (`shl.b32 %r1368, %r1367, 21`,
  `and.b32 %r1369, %r1368, 0x600000`), the lane field of the load's address in units of 32
  lanes; 0 before the broadcast. -/
  bw : Nat := 0

/-- The zero test of the row sum, `setp.equ.f32 %p178, %r1454, 0f0` (pc 2568): its outcome (the
`ideal` rule, `Assumptions.idealArith`; `false` where it faults, see `Prm.setpOk`). -/
def Prm.eq0 (p : Prm) : Bool :=
  match setpE (.unord .eq) false p.l zero32 with
  | .ok b => b
  | .error _ => false

/-- The zero test does not fault. -/
def Prm.setpOk (p : Prm) : Bool := (setpE (.unord .eq) false p.l zero32).toBool

/-- Output row `%r1897`: `mad.lo.s32 %r1897, %r534, %r479, %r497`. -/
def Prm.r1897 (p : Prm) : Nat := (p.a * p.b + p.c) % M32

/-- `%r1898`: `add.s32 %r1898, %r1897, %r611`. -/
def Prm.r1898 (p : Prm) : Nat := (p.r1897 + p.dd) % M32

/-- The output row index `%r1899`: `mad.lo.s32 %r1899, %r1898, 12, %r498`. -/
def Prm.row (p : Prm) : Nat := (p.r1898 * 12 + p.e) % M32

/-- The lane that stores `LsePart`: bit 4 of the thread index is clear (`%p176`). -/
def Prm.lead (p : Prm) : Bool := decide (p.tid % M32 &&& 16 = 0)

/-- The Tensor Memory address of the load, `%r1366`: the lane bits the broadcast returned
(`bw`, the warp index where lane 0 broadcast it) shifted to bit 21, plus the column base. -/
def Prm.taddr (p : Prm) : Nat := (p.bw * 2097152 + p.c0) % M32

/-- The address of `LsePart[row]` (`%rd431`) and of the first word of `OPart[row][d0 ..]`
(`%rd432`). -/
def Prm.lAddr (p : Prm) : Nat := (p.row * 4 + p.lb) % M64
def Prm.oAddr (p : Prm) : Nat := (p.row * 512 + p.ob + p.d0 * 4) % M64

/-- The reciprocal of the row sum (`%r1300`): `1.0` replaces `l` where `%p178` holds, then
`rcp.approx.ftz.f32` (`rcpE`, the exact `1 / x` of a finite nonzero number by `Assumptions.approx`).
-/
def Prm.inv (p : Prm) : Value := okVal (b32 0) (rcpE true (if p.eq0 then one32 else p.l))

/-- The pair `(inv_l, inv_l)` (`%rd430`). -/
def Prm.cpair (p : Prm) : Value := joinValue p.inv p.inv

/-- The `LsePart` word (`%r1370`): the pattern of `-inf` where `%p178` holds, else `lse`. -/
def Prm.lseWord (p : Prm) : Value := if p.eq0 then b32 4286578688 else p.lse

/-! ### The product pairs and the words -/

/-- The packed multiplication `mul.f32x2 d, c, w` without rounding modifier. -/
abbrev mulI : FloatInstr :=
  { op := .mul, ty := ⟨.f32, 2⟩, rnd := none, ftz := false, dsts := [], srcs := [] }

/-- The pair a multiplication of `c` by `w` writes (a pair of zeros where it faults). -/
def mulOut (c w : Value) : Value := okVal (.pair (b32 0) (b32 0)) (floatE mulI [c, w])

/-- The state of the epilogue. -/
structure D where
  site : Site
  pr : Prm
  /-- The 64 words the load returned (empty before it). -/
  o : List Value := []
  /-- The `num_iters < 1` branch (`%p173`): no load, every product is the zero pair. -/
  sk : Bool := false

/-- Product pair `q`: `(inv_l, inv_l) * (o[2 q], o[2 q + 1])`. -/
def D.prod (d : D) (q : Nat) : Value :=
  if d.sk then joinValue (b32 0) (b32 0)
  else mulOut d.pr.cpair (joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)))

/-- Word `k` of the normalized `O` row: the low half of product pair `k / 2` for even `k`, the
high half for odd `k`. -/
def D.word (d : D) (k : Nat) : Value :=
  if k % 2 = 0 then (splitValue 64 (d.prod (k / 2))).1 else (splitValue 64 (d.prod (k / 2))).2

/-- The registers that are not an array: id, value. -/
def D.scalars (d : D) : List (Nat × Value) :=
  let p := d.pr
  [ (3, .pred p.p3), (175, .pred p.rv), (176, .pred p.lead), (178, .pred p.eq0),
    (174, .pred (p.lead && p.rv)), (173, .pred d.sk), (462, b32 p.tid), (463, b32 p.tm),
    (464, b32 p.w),
    (478, b32 p.b), (491, b32 p.c0), (496, b32 p.c), (497, b32 p.e), (524, p.lse),
    (533, b32 p.a), (610, b32 p.dd), (624, b32 p.mb), (1760, zero32), (1761, p.inv),
    (1827, b32 p.taddr), (1831, p.lseWord), (1896, b32 p.r1897), (1897, b32 p.r1898),
    (1898, b32 p.row), (1899, b32 (p.tid % M32 &&& 16)), (1915, p.l), (1956, b64 p.d0),
    (2023, b64 p.ob), (2024, b64 p.lb), (2379, b64 p.lAddr), (2378, p.cpair) ]

/-- The register table of a state: its scalar registers, then the loaded words `r1764 …`
(`o`), the packed pairs `rd2347 …`, the words of the
stores `r1833 …`, the addresses `rd2381 …` of the stores of `OPart` and the product pairs
`rd2480 …`. -/
def D.table (d : D) : List (Nat × Value) :=
  d.scalars ++ (List.range 64).map (fun k => (1763 + k, d.o.getD k (b32 0))) ++
    (List.range 32).map (fun q => (2346 + q,
      joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)))) ++
    (List.range 64).map (fun k => (1832 + k, d.word k)) ++
    (List.range 64).map (fun k => (2380 + k, b64 ((d.pr.oAddr + 4 * k) % M64))) ++
    (List.range 32).map (fun k => (2479 + k, d.prod k))

/-- The value of every register of the epilogue's code, as a function of the state's data (not
its site): the registers a site does not yet or no longer use are dead there. -/
def valueOf (d : D) (r : Nat) : Value := ((d.table).lookup r).getD (b32 0)

def factsAt (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf d)

abbrev facts (d : D) : List (Nat × Value) := factsAt d.site.pc d

/-! ### Invariant -/

/-- The numeric fields are the 32-bit and 64-bit numbers the registers hold. -/
structure Prm.Ok (p : Prm) : Prop where
  tid : p.tid < M32
  tm : p.tm < M32
  w : p.w < 4
  c0 : p.c0 < M32
  mb : p.mb < M32
  a : p.a < M32
  b : p.b < M32
  c : p.c < M32
  dd : p.dd < M32
  e : p.e < M32
  d0 : p.d0 < M64
  ob : p.ob < M64
  lb : p.lb < M64
  /-- The row index is a non-negative 32-bit integer whose 128-fold is too. -/
  row : p.row < 2 ^ 24
  /-- The row sum is an `f32` word. -/
  l : p.l.bytes = 4
  /-- So is the value `LsePart` takes for a non-empty row. -/
  lse : p.lse.bytes = 4
  /-- The barrier is 8-aligned and the two pointers are aligned to the 4 bytes of an `f32`. -/
  mb8 : p.mb % 8 = 0
  ob4 : p.ob % 4 = 0
  lb4 : p.lb % 4 = 0
  /-- The column base of the load of `O` leaves room for its 256 columns. -/
  c0col : p.c0 + 256 ≤ 2 ^ 16

/-- The recorded lane bits do not enter `Prm.Ok`. -/
theorem Prm.Ok.bw {p : Prm} (h : p.Ok) (b : Nat) : ({ p with bw := b } : Prm).Ok := by
  cases h
  constructor <;> assumption

/-- The sites from the load's wait to the end of the stores: the loaded words are in `o`
(unless the load was skipped). -/
def LoadedSite : Site → Prop
  | .waitLd | .stLse | .stO _ => True
  | _ => False

/-- The sites that store: the row is valid. -/
def StoreSite : Site → Prop
  | .stLse | .stO _ => True
  | _ => False

/-- The invariant of a state: the inherited registers are numbers of their widths; the words
of a load are 64 values; a store is of a valid row; `LsePart` is stored by its lane. -/
structure Inv (d : D) : Prop where
  ok : d.pr.Ok
  len : LoadedSite d.site → d.sk = false → d.o.length = 64
  sk : d.sk = true → d.o = []
  pre : d.site = .shfl ∨ d.site = .ld ∨ d.site = .waitLd → d.sk = false
  rv : StoreSite d.site → d.pr.rv = true
  lead : d.site = .stLse → d.pr.lead = true
  /-- The Tensor Memory release is reached by the threads whose guard `%p3` holds. -/
  dealloc : d.site = .dealloc → d.pr.p3 = true
  /-- The lane bits of the load's address are 0 or the warp index (THREAD-TC-DATA-ADDRESS
  accepts no others: `next` kills the thread at the broadcast). -/
  lane : d.pr.bw = 0 ∨ d.pr.bw = d.pr.w

/-! ### Transitions -/

/-- The reciprocal does not fault. -/
def Prm.rcpOk (p : Prm) : Bool := (rcpE true (if p.eq0 then one32 else p.l)).toBool

/-- The packs of the epilogue: pair `q` of the loaded words into `rd2347 + q`
(`mov.b64 d, {a, b}`, pcs 2609-2640) and the pair `(inv_l, inv_l)` into `rd2379` (pc 2641). -/
def packsAll : List (Nat × Nat × Nat) :=
  (List.range 32).map (fun q => (2346 + q, 1763 + 2 * q, 1764 + 2 * q)) ++ [(2378, 1761, 1761)]

/-- The multiplications of the epilogue (`mul.f32x2 d, c, s`, pcs 2642-2673): product pair
`rd2480 + q` is the pair `rd2347 + q` times `c = rd2379`. -/
def mulsAll : List (Nat × Nat) := (List.range 32).map (fun j => (2510 - j, 2377 - j))

/-- No multiplication of the run faults. -/
def mulsOkC (v : Nat → Value) (vc : Value) (ms : List (Nat × Nat)) : Bool :=
  ms.all fun m => (floatE mulI [vc, v m.2]).toBool

/-- The loaded words pack (four-byte words) and the products do not fault. -/
def D.loadOk (d : D) : Bool :=
  packsOk (valueOf d) packsAll && mulsOkC (valueOf d) (valueOf d 2378) mulsAll

/-- The first store site: `LsePart` by its lane, else `OPart`, none for an invalid row. -/
def D.stores (d : D) : Site :=
  if d.pr.rv then (if d.pr.lead then .stLse else .stO 0) else .bar1

/-- The state after store `k` of `OPart`: the next store, or the barrier. -/
def stNext (d : D) (k : Fin 64) : D :=
  if h : k.val + 1 < 64 then { d with site := .stO ⟨k.val + 1, h⟩ } else { d with site := .bar1 }

/-- The abstract successor after event `e`. Every word the broadcast returns is followed: the
load's lane bits are recorded (`Prm.bw`) where the load accepts them (`Raw.laneOk`); otherwise the
shift faults (a word without bits) or the load is undefined behaviour (its lane field leaves the
warp's lanes), and the thread is dead (`none`). A load of other than 64 words is not followed
(`some none`); a thread whose zero test, reciprocal, packs or products would fault is dead
(`none`). After the return no event continues. The
successor of a successful poll is the first store site (`D.stores`) when `num_iters < 1` (`sk`: the
branch of pc 2600 is taken), else the broadcast. -/
def next (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .wait =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      if ok then
        (if d.pr.setpOk then
          (if d.sk then some (some { d with site := d.stores })
           else if d.pr.rcpOk then some (some { d with site := .shfl }) else none)
        else none)
      else some (some d)
    | _ => none
  | .shfl =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match Raw.laneOk d.pr.w v with
      | some b => some (some { d with site := .ld, pr := { d.pr with bw := b } })
      | none => none
    | _ => none
  | .ld =>
    match e.kind with
    | .tc (.ld _ vals _) =>
      if vals.length = 64 then some (some { d with site := .waitLd, o := vals }) else some none
    | _ => none
  | .waitLd => if d.loadOk then some (some { d with site := d.stores }) else none
  | .stLse => some (some { d with site := .stO 0 })
  | .stO k => some (some (stNext d k))
  | .bar1 => some (some { d with site := .setMaxInc })
  | .setMaxInc => some (some { d with site := .stTab })
  | .stTab => some (some { d with site := .bar2 })
  | .bar2 => some (some { d with site := .bar3 })
  | .bar3 => some (some { d with site := if d.pr.p3 then .dealloc else .exit })
  | .dealloc => some (some { d with site := .exit })
  | .exit => none

/-- The epilogue as a code machine from the state `d0` (its entry is the poll of `o_final`,
`D.start`, or `D.startSk` for `num_iters < 1`). The invariant adds that the warp register is the
thread's warp (the broadcast's dead branch needs it). -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) (d0 : D) :
    Flow.Code kernel A L g where
  D := D
  init := d0
  pc := (·.site.pc)
  facts := facts
  inv := fun d => Inv d ∧ d.pr.w = g % L.block / 32
  next := next

/-- The entry state of the epilogue: the poll of the `o_final` barrier, with the branch flag
`%p173` (`num_iters < 1`). -/
def D.entry (p : Prm) (sk : Bool) : D := { site := .wait, pr := p, sk := sk }

/-- The entry state for `num_iters >= 1`. -/
def D.start (p : Prm) : D := D.entry p false

/-- The entry state for `num_iters < 1`: the poll is followed by no wait of the load and no load,
and the stores write the zero pair. -/
def D.startSk (p : Prm) : D := D.entry p true

end
end PTX.Kernels.InklingRelDecode.Proof.Epi

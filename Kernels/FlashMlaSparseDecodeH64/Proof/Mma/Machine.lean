-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamObj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Arith
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Idle
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Arith32Wide

@[expose] public section

/-! # The MMA warp as a control machine

Warp 4 of warpgroup 1 enters the role at its election (pc 1853, after the head's three moves at
1850–1852, `elect`). The lanes that lose the election walk through the idle code's local prefix
(pcs 2587–2595) to its first event (`leave (idleFirst P L g)`, `Lib/Idle.lean`), where they are
handed back to warpgroup 1 with the idle code's register table. The elected lane reads the
batch and the two length budgets from `param_0` and returns for a CTA beyond the batch
(`exit`); otherwise it reads the row's two lengths where their pointers are set (`loadTopk`,
`loadExtra`, `ld.global.nc`) and forms the padded total `max(64, pad64 len0) + pad64 len1`
(`r27`). A total below 64 reaches the `trap` (pc 1896, a site: the machine does not decide the
lengths). Then:

* the query tile: eight rank-4 TMA copies (`qLoad k`), the `expect_tx 65536` arrival
  (`qArrive`) and the wait on `bar_q_tma` (`qWait`), the fence (`qFence`), sixteen
  `tcgen05.cp` into Tensor Memory columns 256–383 (`qCopy k`), their commit to `bar_q_utccp`
  (`qCopyCommit`), its wait (`qCopyWait`) and the fence (`qCopyFence`);
* per 64-token block: the wait on `bar_dequant_ready[pha]` (`kvWait`), the fence (`kvFence`),
  sixteen QK `tcgen05.mma.ws` (`qk k`), their commit to `bar_qk_done[pha]` (`qkCommit`), the wait
  on `bar_so_ready[pha]` (`soWait`), the fence (`soFence`), eight PV MMAs (`pv k`) and their
  commit to `bar_sv_done[pha]` (`pvCommit`);
* the CTA barrier `barrier.sync 12, 384` (`outBar`) and the `ret` (`exit`).

The machine follows every outcome of the code: a failed poll stays, every branch is the code's
test on the recorded words. A length load whose bytes are not one 32-bit word stops it (the
`.nc` words are the initial memory's). A state records the two length words (`l0`, `l1`), the
loop's negative block counter (`neg`, `%r2501`), block counter (`cnt`, `%r2502`), phase (`pha`,
`%r2503`) and 16-bit parity word (`par`, `%rs314`). The value table mirrors the code: each
register's entry is the code's term over the launch, the parameters and these fields. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-! ### Sites -/

inductive Site where
  | elect
  | loadTopk
  | loadExtra
  | trap
  | qLoad (k : Fin 8)
  | qArrive
  | qWait
  | qFence
  | qCopy (k : Fin 16)
  | qCopyCommit
  | qCopyWait
  | qCopyFence
  | kvWait
  | kvFence
  | qk (k : Fin 16)
  | qkCommit
  | soWait
  | soFence
  | pv (k : Fin 8)
  | pvCommit
  | outBar
  | exit
  /-- An unelected lane at an event of the idle code: handed back to warpgroup 1. -/
  | leave (s : IdleSite)
  deriving DecidableEq

def Site.pc : Site → Nat
  | .elect => 1853
  | .loadTopk => 1876
  | .loadExtra => 1886
  | .trap => 1896
  | .qLoad k => 1906 + 3 * k.val
  | .qArrive => 1929
  | .qWait => 1931
  | .qFence => 1934
  | .qCopy k => if k.val < 8 then 1936 + 3 * k.val else 1935 + 3 * k.val
  | .qCopyCommit => 1982
  | .qCopyWait => 1983
  | .qCopyFence => 1986
  | .kvWait => 2012
  | .kvFence => 2015
  | .qk k => if k.val = 0 then 2027 else 2028 + 5 * k.val
  | .qkCommit => 2105
  | .soWait => 2107
  | .soFence => 2110
  | .pv k => if k.val = 0 then 2117 else 2118 + 4 * k.val
  | .pvCommit => 2148
  | .outBar => 2160
  | .exit => 3611
  | .leave s => s.pc

/-- A state: the site, the two length words and the block loop's four registers. -/
structure D where
  site : Site
  l0 : BitVec 64 := 0
  l1 : BitVec 64 := 0
  neg : BitVec 64 := 0
  cnt : BitVec 64 := 0
  pha : BitVec 64 := 0
  par : BitVec 64 := 0

/-! ### The code's terms -/

abbrev w32 (x : BitVec 64) : Value := .bits 32 x
abbrev b64v (x : BitVec 64) : Value := .bits 64 x
/-- A 32-bit word of `param_0` at its first byte, and a 64-bit one. -/
abbrev pw (x : Nat) : BitVec 64 := BitVec.ofNat 64 (leNat x 0 4)
abbrev pw8 (x : Nat) : BitVec 64 := BitVec.ofNat 64 (leNat x 0 8)
/-- `%ctaid.x`, `%ctaid.y` and the dynamic shared base as words. -/
abbrev r1W (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (ctaidX L g)
abbrev r2W (L : Launch) (g : Nat) : BitVec 64 := BitVec.ofNat 64 (ctaidY L g)
abbrev sbw (L : Launch) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0))
/-- `or.b64` with an immediate. -/
abbrev ori64 (x : BitVec 64) (n : Int) : BitVec 64 := r64 x ||| truncBits 64 (BitVec.ofInt 64 n)
/-- `and.b16` with an immediate, and the parity word's low byte. -/
abbrev andi16 (x : BitVec 64) (n : Int) : BitVec 64 := truncBits 16 x &&& i16 n
/-- The two halves of a 64-bit word (`mov.b64 {lo, hi}`), and their join. -/
abbrev lo32 (x : BitVec 64) : BitVec 64 := truncBits 32 x
abbrev hi32 (x : BitVec 64) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (x.toNat / 2 ^ 32))
abbrev join (lo hi : BitVec 64) : BitVec 64 := lo ||| hi <<< 32

/-- The padded length arithmetic (pcs 1878–1893): `pad64 a` and the padded total `r27`. -/
abbrev pad (a : BitVec 64) : BitVec 64 :=
  andi (add32 (addi a 63) (shru (shrs (addi a 63) 31) 26)) (-64)
abbrev r27 (a b : BitVec 64) : BitVec 64 := add32 (pad b) (max32 (pad a) (i32 64))
/-- The block count `r27 / 64` (pcs 1995–1998). -/
abbrev nblk (a b : BitVec 64) : BitVec 64 :=
  shrs (add32 (r27 a b) (shru (shrs (r27 a b) 31) 26)) 6

/-- The shared P tile's descriptor (`%rd104`): the A operand of the PV MMAs. -/
abbrev rd104 (L : Launch) : BitVec 64 :=
  ori64 (zext (andi (shru (addi (sbw L) 204800) 4) 16383)) 70403108110336
/-- The shared query tile's descriptor base (`%rd87`). -/
abbrev rd87 (L : Launch) : BitVec 64 := zext (andi (shru (sbw L) 4) 16383)
/-- The barrier base of the phase (`%r429`). -/
abbrev bb (L : Launch) (pha : BitVec 64) : BitVec 64 := add32 (sbw L) (shl pha 3)
/-- The K/V tile's descriptor base of the phase (`%rd116`). -/
abbrev rd116 (L : Launch) (pha : BitVec 64) : BitVec 64 :=
  zext (andi (shru (mad32 pha (i32 65528) (bb L pha)) 4) 16383)
/-- The QK B descriptor (`%rd88`) and the PV B descriptor (`%rd105`). -/
abbrev kd (L : Launch) (pha : BitVec 64) : BitVec 64 := ori64 (rd116 L pha) 4611756662049538048
abbrev vd (L : Launch) (pha : BitVec 64) : BitVec 64 := ori64 (rd116 L pha) 4611756662083026944

/-- The descriptor offsets of the sixteen QK MMAs and of the eight PV MMAs. -/
def qkOff (k : Nat) : Int := 1024 * (k / 4 : Nat) + 2 * (k % 4 : Nat)
def pvOff (k : Nat) : Int := [0, 2048, 128, 2176, 256, 2304, 384, 2432].getD k 0
/-- The copy descriptor offsets of the sixteen `tcgen05.cp` (from `%rd87`). -/
def cpOff (k : Nat) : Int := 4611756662049538048 + qkOff k

/-- The parity word after a block (pcs 2149–2152). -/
abbrev parNext (d : D) : BitVec 64 :=
  sel (PTX.compare .ne .b 16 (truncBits 16 (andi16 d.par 255))
    (truncBits 16 (andi16 (truncBits 16 (r32 d.pha)) 255))) (i16 1) (i16 0)

/-! ### Transitions -/

section
variable (P : Params) (L : Launch) (g : Nat)

/-- After the two lengths `a`, `b` (pcs 1887–1895): the trap for a total below 64, else the
first Q load. -/
def lensD (d : D) (a b : BitVec 64) : D :=
  if scmpi .gt .s (r27 a b) 63 then { d with site := .qLoad 0, l0 := a, l1 := b }
  else { d with site := .trap, l0 := a, l1 := b }

/-- After the first length `a` (pcs 1877–1883): the second length's load if its pointer is
set. -/
def afterTopk (d : D) (a : BitVec 64) : D :=
  if eqz64 (pw8 (P.extraTopkLenBase.getD 0)) then lensD d a d.l1
  else { d with site := .loadExtra, l0 := a }

/-- The elected lane after its parameters (pcs 1854–1873): the return for a CTA beyond the
batch, else the length loads the set pointers ask for. -/
def leadNext (d : D) : D :=
  if scmp .ge .s (r2W L g) (pw P.b) then
    { d with site := .exit, l0 := pw P.topk, l1 := pw P.extra_topk }
  else if eqz64 (pw8 (P.topkLenBase.getD 0)) then
    afterTopk P { d with l1 := pw P.extra_topk } (pw P.topk)
  else { d with site := .loadTopk, l0 := pw P.topk, l1 := pw P.extra_topk }
end

/-- The block loop's entry (pcs 1987–2011): none for a total below 64, else block 0. -/
def loopEntry (d : D) : D :=
  if scmpi .lt .s (r27 d.l0 d.l1) 64 then { d with site := .outBar }
  else
    { d with
        site := .kvWait, neg := neg32 (nblk d.l0 d.l1), cnt := i32 0, pha := i32 0, par := i16 0 }

/-- The end of a block (pcs 2149–2157): the next block or the CTA barrier. -/
def loopEnd (d : D) : D :=
  let d' := { d with
    par := parNext d, pha := andi (not32 d.pha) 1, cnt := addi d.cnt 1, neg := addi d.neg 1 }
  if scmpi .ne .b (addi d.neg 1) 0 then { d' with site := .kvWait } else { d' with site := .outBar }

/-- A length load: a 32-bit word continues, any other value stops the machine. -/
def ncWord (e : Event) (f : BitVec 64 → D) : Option (Option D) :=
  match e.kind with
  | .nc _ bs =>
    match rebuild 3 bs with
    | .ok v => match v with
      | .bits 32 x => some (some (f x))
      | _ => some none
    | .error _ => none
  | _ => none

/-- A poll: the successful one continues to `s`, the failed one stays. -/
def poll (d : D) (e : Event) (s : Site) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (if ok then { d with site := s } else d))
  | _ => none

/-- The successor after event `e`. -/
def succ (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .elect =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if PTX.laneOf L g = ld then leadNext P L g d
        else { d with site := .leave (idleFirst P L g) }))
    | _ => none
  | .loadTopk => ncWord e fun x => afterTopk P d x
  | .loadExtra => ncWord e fun x => lensD d d.l0 x
  | .trap => none
  | .qLoad k => some (some { d with site := if k.val = 7 then .qArrive else .qLoad (k + 1) })
  | .qArrive => some (some { d with site := .qWait })
  | .qWait => poll d e .qFence
  | .qFence => some (some { d with site := .qCopy 0 })
  | .qCopy k =>
    some (some { d with site := if k.val = 15 then .qCopyCommit else .qCopy (k + 1) })
  | .qCopyCommit => some (some { d with site := .qCopyWait })
  | .qCopyWait => poll d e .qCopyFence
  | .qCopyFence => some (some (loopEntry d))
  | .kvWait => poll d e .kvFence
  | .kvFence => some (some { d with site := .qk 0 })
  | .qk k => some (some { d with site := if k.val = 15 then .qkCommit else .qk (k + 1) })
  | .qkCommit => some (some { d with site := .soWait })
  | .soWait => poll d e .soFence
  | .soFence => some (some { d with site := .pv 0 })
  | .pv k => some (some { d with site := if k.val = 7 then .pvCommit else .pv (k + 1) })
  | .pvCommit => some (some (loopEnd d))
  | .outBar => some (some { d with site := .exit })
  | .exit => none
  | .leave _ => some none

/-! ### Register values -/

section
variable (P : Params) (L : Launch) (g : Nat) (d : D)

/-- The launch registers the role keeps: `%ctaid.x`, `%ctaid.y` and the parameter pointers. -/
def valuesLaunch : List (Nat × Value) :=
  [(459, w32 (r1W L g)), (460, w32 (r2W L g)),
   (2990, .ptr 64 false (.param (param "1")) 0), (2991, .ptr 64 false (.param (param "0")) 0)]

/-- The registers of the length loads (pcs 1854–1895). -/
def valuesLens : List (Nat × Value) :=
  [(793, w32 (i32 0)), (794, w32 (i32 (-1))), (2957, w32 d.l0), (2958, w32 d.l1),
   (3004, b64v (pw8 (P.topkLenBase.getD 0))),
   (3005, b64v (pw8 (P.extraTopkLenBase.getD 0))), (3006, .ptr 64 true (.param (param "1")) 0),
   (3054, b64v (add64 (pw8 (P.topkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3056, b64v (add64 (pw8 (P.extraTopkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3093, b64v (rd104 L)), (484, w32 (pad d.l0)), (485, w32 (r27 d.l0 d.l1))]

/-- The registers of the query's TMA loads and Tensor-Memory copies (pcs 1897–1986). -/
def valuesQ : List (Nat × Value) :=
  [(62, .pred (scmpi .lt .s (r27 d.l0 d.l1) 64)), (485, w32 (r27 d.l0 d.l1)),
   (810, w32 (sbw L)), (811, w32 (addi (sbw L) 222776)), (812, w32 (i32 0)),
   (3006, .ptr 64 true (.param (param "1")) 0),
   (3058, b64v (BitVec.ofNat 64 (P.param1Base + 128))), (3059, b64v 1364590687093260288),
   (3076, b64v (rd87 L)), (3093, b64v (rd104 L)),
   (813, w32 (addi (sbw L) 8192)), (814, w32 (i32 64)),
   (815, w32 (addi (sbw L) 16384)), (816, w32 (i32 128)),
   (817, w32 (addi (sbw L) 24576)), (818, w32 (i32 192)),
   (819, w32 (addi (sbw L) 32768)), (820, w32 (i32 256)),
   (821, w32 (addi (sbw L) 40960)), (822, w32 (i32 320)),
   (823, w32 (addi (sbw L) 49152)), (824, w32 (i32 384)),
   (825, w32 (addi (sbw L) 57344)), (826, w32 (i32 448)),
   (827, w32 (i32 65536)), (828, w32 (i32 10000000)),
   (3060, b64v (ori64 (rd87 L) (cpOff 0))), (3061, b64v (addi64 (rd87 L) (cpOff 1))),
   (3062, b64v (addi64 (rd87 L) (cpOff 2))), (3063, b64v (addi64 (rd87 L) (cpOff 3))),
   (3064, b64v (addi64 (rd87 L) (cpOff 4))), (3065, b64v (addi64 (rd87 L) (cpOff 5))),
   (3066, b64v (addi64 (rd87 L) (cpOff 6))), (3067, b64v (addi64 (rd87 L) (cpOff 7))),
   (3068, b64v (addi64 (rd87 L) (cpOff 8))), (3069, b64v (addi64 (rd87 L) (cpOff 9))),
   (3070, b64v (addi64 (rd87 L) (cpOff 10))), (3071, b64v (addi64 (rd87 L) (cpOff 11))),
   (3072, b64v (addi64 (rd87 L) (cpOff 12))), (3073, b64v (addi64 (rd87 L) (cpOff 13))),
   (3074, b64v (addi64 (rd87 L) (cpOff 14))), (3075, b64v (addi64 (rd87 L) (cpOff 15))),
   (829, w32 (i32 264)), (830, w32 (i32 272)), (831, w32 (i32 280)), (832, w32 (i32 288)),
   (833, w32 (i32 296)), (834, w32 (i32 304)), (835, w32 (i32 312)), (836, w32 (i32 328)),
   (837, w32 (i32 336)), (838, w32 (i32 344)), (839, w32 (i32 352)), (840, w32 (i32 360)),
   (841, w32 (i32 368)), (842, w32 (i32 376)), (843, w32 (addi (sbw L) 222784))]

/-- The block loop's registers that keep one value through a block (pcs 2003–2148). -/
def valuesLoop : List (Nat × Value) :=
  let b := bb L d.pha
  let k := kd L d.pha
  let v := vd L d.pha
  let a := rd104 L
  [(2959, w32 d.neg), (2960, w32 d.cnt), (2961, w32 d.pha), (152, .bits 16 (andi16 d.par 255)),
   (855, w32 (addi b 222792)), (856, w32 (i32 10000000)),
   (879, w32 (andi (zext16 d.par) 255)), (887, w32 b), (888, w32 (not32 d.pha)),
   (3093, b64v a), (3096, b64v (join (addi (lo32 a) 128) (hi32 a))),
   (3099, b64v (join (addi (lo32 a) 256) (hi32 a))),
   (3102, b64v (join (addi (lo32 a) 384) (hi32 a))),
   (3105, b64v (rd116 L d.pha)), (3077, b64v k),
   (892, w32 (lo32 k)), (893, w32 (hi32 k)),
   (857, w32 (i32 400)), (858, w32 (i32 256)), (859, w32 (i32 69207184)), (860, w32 (i32 0)),
   (862, w32 (i32 1)), (877, w32 (addi b 222904)), (878, w32 (addi b 222920)),
   (880, w32 (i32 71369872)), (881, w32 (sel (scmpi .ne .b d.cnt 0) (i32 1) (i32 0))),
   (882, w32 (i32 128)), (3094, b64v v), (909, w32 (lo32 v)), (910, w32 (hi32 v)),
   (883, w32 (addi b 222936))]

/-- The registers of QK MMA `k` (`k ≥ 1`): its A column, its B descriptor and its accumulate
predicate. -/
def valuesQk (k : Nat) : List (Nat × Value) :=
  let x := kd L d.pha
  [(if k = 1 then 861 else 861 + k, w32 (i32 (256 + 8 * k))),
   (3077 + k, b64v (join (addi (lo32 x) (qkOff k)) (hi32 x))),
   (4091 + k, .pred true)]

/-- The registers of PV MMA `k`: its B descriptor and accumulate predicate. -/
def pvReg (k : Nat) : Nat := [3094, 3095, 3097, 3098, 3100, 3101, 3103, 3104].getD k 0

def valuesPv (k : Nat) : List (Nat × Value) :=
  let x := vd L d.pha
  [(pvReg k, if k = 0 then b64v x else b64v (join (addi (lo32 x) (pvOff k)) (hi32 x))),
   (4108 + k, .pred (if k < 2 then scmpi .ne .b (sel (scmpi .ne .b d.cnt 0) (i32 1) (i32 0)) 0
     else true))]

/-- The registers at state `d`. -/
def values : List (Nat × Value) :=
  match d.site with
  | .elect => valuesLens P L g d
  | .loadTopk | .loadExtra | .trap => valuesLens P L g d
  | .qLoad _ | .qArrive | .qWait | .qFence | .qCopy _ | .qCopyCommit | .qCopyWait
  | .qCopyFence => valuesQ P L d
  | .qk k =>
    (if k.val = 0 then [(4091, .pred false)] else valuesQk L d k.val) ++
      valuesLoop L d
  | .pv k => valuesPv L d k.val ++ valuesLoop L d
  | .outBar => [(918, w32 (i32 12)), (919, w32 (i32 384))]
  | .leave _ => idleVals P L g
  | _ => valuesLoop L d
end

/-- The value of register `r` at state `d`. -/
def valueOf (P : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values P L g d).lookup r).getD (((valuesLaunch L g).lookup r).getD (.pred false))

abbrev facts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live d.site.pc) (valueOf P L g d)

/-- **The hand-back's facts are the idle code's** at each of its events. -/
theorem facts_leave (P : Params) (L : Launch) (g : Nat) (s : IdleSite)
    (l0 l1 neg cnt pha par : BitVec 64) :
    facts P L g ⟨.leave s, l0, l1, neg, cnt, pha, par⟩ = idleEnd P L g s := by
  cases s <;> rfl

/-- The first state: the election. -/
def init : D := { site := .elect }

/-- **The MMA warp as a code machine.** -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := init
  pc := (·.site.pc)
  facts := facts P L g
  inv := fun _ => True
  next := succ P L g

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

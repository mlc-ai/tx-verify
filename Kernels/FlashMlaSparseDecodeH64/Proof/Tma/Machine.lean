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

/-! # The TMA warp as a control machine

Warp 5 of warpgroup 1 enters the role at its election (pc 2165). The lanes that lose the election
walk through the idle code's local prefix (pcs 2587–2595) to its first event
(`leave (idleFirst P L g)`, `Lib/Idle.lean`), where they are handed back to warpgroup 1 with the
idle code's register table. The elected lane reads the batch and the two length budgets from
`param_0` and returns for a CTA beyond the batch (`exit`); otherwise it reads the row's two
lengths where their pointers are set (`loadTopk`, `loadExtra`, `ld.global.nc`), waits on
`bar_q_utccp` (`qWait`) and on `bar_last_store_done` (`storeWait`), and, for a padded total of at
least 64, runs one loop over the row's 64-token blocks. Per block:

* the wait on the coordinate ring's `valid_coord_ready[slot]` (`coordWait`) and on the raw tile's
  `raw_free[buf]` (`rawWait`);
* the 16 shared loads of the slot's coordinate quadruples (`coord0 k` … `coord3 k`, four `b32`
  elements each)
  and the 16 four-row TMA gathers of 2,304 bytes each (`gather k`) naming `raw_ready[buf]`; the
  load of quadruple `k + 1` comes before the gather of quadruple `k`;
* the arrival on `raw_ready[buf]` with `expect_tx 36864` (`rawArrive`) and on
  `valid_coord_free[slot]` (`coordFree`).

Then the CTA barrier `barrier.sync 12, 384` (`outBar`) and the `ret` (`exit`).

The machine follows every outcome of the code: a failed poll stays, every branch is the code's
test on the recorded words. A length load whose value is not one 32-bit word stops it. The
coordinate words are data: in the code they feed only the coordinate operands of the gathers (no
branch, address or mbarrier operand reads them), so a coordinate element continues on any payload
(`rdAny`) and the coordinate registers' words are kept (`cp`, `cq`); with a payload that
is not a 32-bit word the gather may fault, which the UB-tolerant obligations accept. A state
records the two length words (`l0`, `l1`), the loop's registers (negative block counter `neg`,
block counter `cnt`, tile slot `buf`, ring slot `slot`, the two parity words `pf`, `pr`) and the
elements of the coordinate load that already fired (`ac`). The value table mirrors the code: each
register's entry is the code's term over the launch, the parameters and these fields. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-! ### Sites -/

inductive Site where
  | elect
  | loadTopk
  | loadExtra
  | qWait
  | storeWait
  | coordWait
  | rawWait
  /-- The four elements of the load of coordinate quadruple `k`. -/
  | coord0 (k : Fin 16)
  | coord1 (k : Fin 16)
  | coord2 (k : Fin 16)
  | coord3 (k : Fin 16)
  | gather (k : Fin 16)
  | rawArrive
  | coordFree
  | outBar
  | exit
  /-- An unelected lane at an event of the idle code: handed back to warpgroup 1. -/
  | leave (s : IdleSite)
  deriving DecidableEq

/-- The pc of the load of coordinate quadruple `k`. -/
def coordPc (k : Fin 16) : Nat :=
  if k.val = 0 then 2250 else if k.val = 1 then 2254 else 2254 + 3 * k.val

def Site.pc : Site → Nat
  | .elect => 2165
  | .loadTopk => 2181
  | .loadExtra => 2191
  | .qWait => 2205
  | .storeWait => 2209
  | .coordWait => 2234
  | .rawWait => 2245
  | .coord0 k | .coord1 k | .coord2 k | .coord3 k => coordPc k
  | .gather k => if k.val = 15 then 2303 else 2259 + 3 * k.val
  | .rawArrive => 2305
  | .coordFree => 2308
  | .outBar => 2330
  | .exit => 3611
  | .leave s => s.pc

/-- An element of a coordinate load is its instruction's `e`-th step. -/
def Site.sub : Site → Nat
  | .coord1 _ => 1
  | .coord2 _ => 2
  | .coord3 _ => 3
  | _ => 0

/-- The four words of a coordinate quadruple (the elements of its load). -/
structure Quad where
  w0 : Value := .pred false
  w1 : Value := .pred false
  w2 : Value := .pred false
  w3 : Value := .pred false

/-- The words of a quadruple, in order. -/
def Quad.list (q : Quad) : List Value := [q.w0, q.w1, q.w2, q.w3]

/-- A state: the site, the two lengths, the loop's registers and a coordinate load's elements. -/
structure D where
  site : Site
  l0 : BitVec 64 := 0
  l1 : BitVec 64 := 0
  /-- The negative block counter (`%r2964`). -/
  neg : BitVec 64 := 0
  /-- The block counter (`%r2965`). -/
  cnt : BitVec 64 := 0
  /-- The raw tile's slot (`%r2966`). -/
  buf : BitVec 64 := 0
  /-- The coordinate ring's slot (`%r2967`). -/
  slot : BitVec 64 := 0
  /-- The raw tile's parity word (`%rs454`). -/
  pf : BitVec 64 := 0
  /-- The coordinate ring's parity word (`%rs455`). -/
  pr : BitVec 64 := 0
  /-- The elements of the coordinate load that already fired (`w0` .. `w2`). -/
  ac : Quad := {}
  /-- The words of the last quadruple but one that was loaded (live until its gather). -/
  cp : Quad := {}
  /-- The words of the last quadruple that was loaded. -/
  cq : Quad := {}

/-! ### The code's terms -/

/-- `and.b16` with an immediate. -/
abbrev andi16 (x : BitVec 64) (n : Int) : BitVec 64 := truncBits 16 x &&& i16 n

/-- The padded length arithmetic (pcs 2183–2200): `pad64 a` (`%r486`), `max(64, pad64 a)`
(`%r487`), the padded total (`%r488`), the block count (`%r2964`'s negation) and the main
blocks (`%r489`). -/
abbrev padA (a : BitVec 64) : BitVec 64 :=
  andi (add32 (addi a 63) (shru (shrs (addi a 63) 31) 26)) (-64)
abbrev maxA (a : BitVec 64) : BitVec 64 := max32 (padA a) (i32 64)
abbrev padB (b : BitVec 64) : BitVec 64 :=
  andi (add32 (addi b 63) (shru (shrs (addi b 63) 31) 26)) (-64)
abbrev tot (a b : BitVec 64) : BitVec 64 :=
  add32 (add32 (addi b 63) (maxA a)) (sub32 (padB b) (addi b 63))
abbrev nblk (a b : BitVec 64) : BitVec 64 :=
  shrs (add32 (tot a b) (shru (shrs (tot a b) 31) 26)) 6
abbrev nmain (a : BitVec 64) : BitVec 64 := shru (maxA a) 6

section
variable (L : Launch) (d : D)

/-- The coordinate ring slot's barrier base `wksp + 8 * slot` (`%r777`). -/
abbrev ringB : BitVec 64 := add32 (sbw L) (shl d.slot 3)
/-- The tile slot's barrier base `wksp + 8 * buf` (`%r780`). -/
abbrev tileB : BitVec 64 := add32 (sbw L) (shl d.buf 3)
/-- The coordinate quadruples' base (`%r782`). -/
abbrev crdB : BitVec 64 := mad32 d.slot (i32 248) (ringB L d)
/-- The raw tile's base (`%r783`). -/
abbrev rawB : BitVec 64 := mad32 d.buf (i32 36856) (tileB L d)
/-- The loop's test of the main cache (`%p52`). -/
abbrev isMain : Bool := scmp .lt .u d.cnt (nmain d.l0)
end

/-- The registers of quadruple `k`'s four words. -/
def ldRegs : Nat → List Nat
  | 0 => [692, 693, 694, 695]
  | 1 => [698, 699, 700, 701]
  | 2 => [703, 704, 705, 706]
  | 3 => [708, 709, 710, 711]
  | 4 => [713, 714, 715, 716]
  | 5 => [718, 719, 720, 721]
  | 6 => [723, 724, 725, 726]
  | 7 => [728, 729, 730, 731]
  | 8 => [733, 734, 735, 736]
  | 9 => [738, 739, 740, 741]
  | 10 => [743, 744, 745, 746]
  | 11 => [748, 749, 750, 751]
  | 12 => [753, 754, 755, 756]
  | 13 => [758, 759, 760, 761]
  | 14 => [763, 764, 765, 766]
  | 15 => [768, 769, 770, 771]
  | _ => []

/-- The registers of the 16 coordinate quadruples. -/
def crdRegs : List Nat := (List.range 16).flatMap ldRegs

/-- The registers whose values the facts at `pc` name: the live ones, the coordinate words
among them (at the pcs from the second quadruple's load to the last gather, 2254-2303). -/
def tmaLive (pc : Nat) : List Nat := Flow.live pc

/-- The destination addresses of the 16 gathers: the raw tile's base plus 2304 bytes per gather
(`%r690`, `%r697`, ...). -/
def dstVals (b : BitVec 64) : List (Nat × Value) :=
  [(690, w32 (addi b 131072)), (697, w32 (addi b 133376)), (702, w32 (addi b 135680)),
   (707, w32 (addi b 137984)), (712, w32 (addi b 140288)), (717, w32 (addi b 142592)),
   (722, w32 (addi b 144896)), (727, w32 (addi b 147200)), (732, w32 (addi b 149504)),
   (737, w32 (addi b 151808)), (742, w32 (addi b 154112)), (747, w32 (addi b 156416)),
   (752, w32 (addi b 158720)), (757, w32 (addi b 161024)), (762, w32 (addi b 163328)),
   (767, w32 (addi b 165632))]

/-! ### Transitions -/

/-- After the two lengths (pcs 2192–2204): the wait on `bar_q_utccp`. -/
def lensD (d : D) (a b : BitVec 64) : D := { d with site := .qWait, l0 := a, l1 := b }

/-- After the first length `a` (pcs 2182–2190): the second length's load if its pointer is
set. -/
def afterTopk (P : Params) (d : D) (a : BitVec 64) : D :=
  if eqz64 (pw8 (P.extraTopkLenBase.getD 0)) then lensD d a d.l1
  else { d with site := .loadExtra, l0 := a }

/-- The elected lane after its parameters (pcs 2166–2178): the return for a CTA beyond the
batch, else the length loads the set pointers ask for. -/
def leadNext (P : Params) (L : Launch) (g : Nat) (d : D) : D :=
  if scmp .ge .s (r2W L g) (pw P.b) then
    { d with site := .exit, l0 := pw P.topk, l1 := pw P.extra_topk }
  else if eqz64 (pw8 (P.topkLenBase.getD 0)) then
    afterTopk P { d with l1 := pw P.extra_topk } (pw P.topk)
  else { d with site := .loadTopk, l0 := pw P.topk, l1 := pw P.extra_topk }

/-- The loop's entry after the set-up waits (pcs 2212–2224): the CTA barrier for a total below
64, else the first block with the counters, slots and parities at zero. -/
def loopEntry (d : D) : D :=
  if scmpi .lt .s (tot d.l0 d.l1) 64 then { d with site := .outBar }
  else
    { d with
      site := .coordWait, neg := neg32 (nblk d.l0 d.l1), cnt := i32 0, buf := i32 0,
      slot := i32 0, pf := i16 0, pr := i16 0 }

/-- The raw tile's parity word after a block (pcs 2309–2312). -/
abbrev pfNext (d : D) : BitVec 64 :=
  sel (PTX.compare .ne .b 16 (truncBits 16 (andi16 d.pf 255))
    (truncBits 16 (andi16 (truncBits 16 (r32 d.buf)) 255))) (i16 1) (i16 0)
/-- The coordinate ring's parity word after a block (pcs 2314–2317). -/
abbrev prNext (d : D) : BitVec 64 :=
  sel (PTX.compare .ne .b 16 (truncBits 16 (andi16 d.pr 255))
    (truncBits 16 (sel (scmpi .eq .b d.slot 3) (i16 1) (i16 0)))) (i16 1) (i16 0)
/-- The coordinate ring's next slot (pcs 2318–2323). -/
abbrev slotNext (s : BitVec 64) : BitVec 64 :=
  sub32 (addi s 1) (andi (add32 (addi s 1) (shru (shrs (addi s 1) 31) 30)) (-4))

/-- The end of a block (pcs 2309–2327): the next block or the CTA barrier. -/
def loopEnd (d : D) : D :=
  let d' := { d with
    pf := pfNext d, buf := andi (not32 d.buf) 1, pr := prNext d, slot := slotNext d.slot,
    cnt := addi d.cnt 1, neg := addi d.neg 1 }
  if scmpi .ne .b (addi d.neg 1) 0 then { d' with site := .coordWait }
  else { d' with site := .outBar }

/-- The site after the load of quadruple `k`: the second quadruple's load after the first, else
the gather of the quadruple before. -/
def afterCoord (k : Fin 16) : Site :=
  if k.val = 0 then .coord0 1 else .gather ⟨k.val - 1, by omega⟩

/-- The state after the fourth word `v` of quadruple `k`: its words are the last loaded, the
ones before them the last but one. -/
def afterQuad (d : D) (k : Fin 16) (v : Value) : D :=
  { d with site := afterCoord k, cp := d.cq, cq := { d.ac with w3 := v } }

@[simp] theorem afterQuad_site (d : D) (k : Fin 16) (v : Value) :
    (afterQuad d k v).site = afterCoord k := rfl

/-- The site after gather `k`: the load of quadruple `k + 2`, the last gather, or the arrival on
the raw tile's barrier. -/
def afterGather (k : Fin 16) : Site :=
  if k.val = 15 then .rawArrive else if k.val = 14 then .gather 15 else .coord0 (k + 2)

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- A length load: a 32-bit word continues, any other value stops the machine. -/
def ncWord (e : Event) (f : BitVec 64 → D) : Option (Option D) :=
  match e.kind with
  | .nc _ bs =>
    match rebuild 3 bs with
    | .ok v => word32 v f
    | .error _ => none
  | _ => none

/-- A coordinate element: any payload continues (a payload that does not rebuild faults the
thread; the machine goes on with the default value). -/
def rdAny (e : Event) (f : Value → D) : Option (Option D) :=
  match e.kind with
  | .rd _ bs => some (some (f ((rebuild 3 bs).toOption.getD (.pred false))))
  | _ => none

/-- A poll: the successful one continues to `d'`, the failed one stays. -/
def poll (d : D) (e : Event) (d' : D) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (if ok then d' else d))
  | _ => none

/-- The election: the elected lane continues with its parameters, the others leave. -/
def electNext (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match e.kind with
  | .elect _ _ ld =>
    some (some (if PTX.laneOf L g = ld then leadNext P L g d
      else { d with site := .leave (idleFirst P L g) }))
  | _ => none

/-- The successor after event `e`. -/
def succ (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .qWait => poll d e { d with site := .storeWait }
  | .elect => electNext P L g d e
  | .loadTopk => ncWord e fun x => afterTopk P d x
  | .loadExtra => ncWord e fun x => lensD d d.l0 x
  | .storeWait => poll d e (loopEntry d)
  | .coordWait => poll d e { d with site := .rawWait }
  | .rawWait => poll d e { d with site := .coord0 0 }
  | .coord0 k => rdAny e fun v => { d with site := .coord1 k, ac := { d.ac with w0 := v } }
  | .coord1 k => rdAny e fun v => { d with site := .coord2 k, ac := { d.ac with w1 := v } }
  | .coord2 k => rdAny e fun v => { d with site := .coord3 k, ac := { d.ac with w2 := v } }
  | .coord3 k => rdAny e (afterQuad d k)
  | .gather k => some (some { d with site := afterGather k })
  | .rawArrive => some (some { d with site := .coordFree })
  | .coordFree => some (some (loopEnd d))
  | .outBar => some (some { d with site := .exit })
  | .exit => none
  | .leave _ => some none

/-! ### Register values -/

section
variable (P : Params) (L : Launch) (g : Nat) (d : D)

/-- The launch registers the role keeps: `%ctaid.y` and the parameter pointers. -/
def valuesLaunch : List (Nat × Value) :=
  [(460, w32 (r2W L g)), (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0)]

/-- The registers of the election, the lengths and the set-up waits (pcs 2165–2224). -/
def valuesPre : List (Nat × Value) :=
  [(662, w32 (i32 0)), (663, w32 (i32 (-1))), (2962, w32 d.l0), (2963, w32 d.l1),
   (3007, .bits 64 (pw8 (P.topkLenBase.getD 0))),
   (3008, .bits 64 (pw8 (P.extraTopkLenBase.getD 0))),
   (3045, .bits 64 (add64 (pw8 (P.topkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (3047, .bits 64 (add64 (pw8 (P.extraTopkLenBase.getD 0)) (mulWide .u (r2W L g) 4))),
   (486, w32 (padA d.l0)), (487, w32 (maxA d.l0)), (488, w32 (tot d.l0 d.l1)),
   (680, w32 (sbw L)), (669, w32 (addi (sbw L) 222784)), (670, w32 (i32 0)),
   (671, w32 (i32 10000000)), (672, w32 (addi (sbw L) 222768)),
   (790, w32 (i32 12)), (791, w32 (i32 384))]

/-- The loop's registers. -/
def valuesLoop : List (Nat × Value) :=
  [(2964, w32 d.neg), (2965, w32 d.cnt), (2966, w32 d.buf), (2967, w32 d.slot),
   (489, w32 (nmain d.l0)), (52, .pred (isMain d)), (454, .bits 16 d.pf),
   (455, .bits 16 d.pr), (146, .bits 16 (andi16 d.pr 255)),
   (686, w32 (andi (zext16 d.pr) 255)), (776, w32 (sbw L)), (777, w32 (ringB L d)),
   (685, w32 (addi (ringB L d) 222840)), (687, w32 (i32 10000000)),
   (147, .bits 16 (andi16 d.pf 255)), (689, w32 (andi (zext16w (xor16 d.pf)) 255)),
   (780, w32 (tileB L d)), (781, w32 (not32 d.buf)), (688, w32 (addi (tileB L d) 222824)),
   (782, w32 (crdB L d)), (3051, .bits 64 (sel (isMain d) 768 896)),
   (783, w32 (rawB L d)), (696, w32 (addi (tileB L d) 222808)), (691, w32 (i32 0)),
   (3052, .ptr 64 true (.param (param "1")) 0),
   (3049, .bits 64 (BitVec.ofNat 64 (P.param1Base + (sel (isMain d) 768 896).toNat))),
   (3050, .bits 64 1364590687093260288), (772, w32 (i32 36864)),
   (773, w32 (addi (mad32 d.slot (i32 (-248)) (crdB L d)) 222872))]

/-- The registers at state `d`. -/
def values : List (Nat × Value) :=
  match d.site with
  | .leave _ => idleVals P L g
  | _ => dstVals (rawB L d) ++ valuesLoop P L d ++ valuesPre P L g d
end

/-- The quadruple that quadruple `j`'s registers hold at `d`: the last loaded (`cq`), but for the
one before it while its gather is to come (`cp`). -/
def crdSrc (d : D) (j : Nat) : Quad :=
  match d.site with
  | .gather k => if j = k.val ∧ k.val < 15 then d.cp else d.cq
  | _ => d.cq

/-- The quadruple and element a coordinate register holds (`ldRegs`): quadruple `0` in `692` ..
`695`, quadruple `j` in `698 + 5 (j - 1)` ..  `+ 3`. -/
def crdSlot (r : Nat) : Option (Nat × Nat) :=
  if 692 ≤ r ∧ r < 696 then some (0, r - 692)
  else if 698 ≤ r ∧ r < 773 ∧ (r - 698) % 5 < 4 then some (1 + (r - 698) / 5, (r - 698) % 5)
  else none

/-- The coordinate word register `r` holds at `d`. -/
def crdWord (d : D) (r : Nat) : Value :=
  match crdSlot r with
  | some (j, i) => (crdSrc d j).list.getD i (.pred false)
  | none => .pred false

/-- The value of register `r` at state `d`: the tables', else the coordinate word it holds. -/
def valueOf (P : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values P L g d).lookup r).getD (((valuesLaunch L g).lookup r).getD (crdWord d r))

abbrev facts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (tmaLive d.site.pc) (valueOf P L g d)

/-- **The hand-back's facts are the idle code's** at each of its events. -/
theorem facts_leave (P : Params) (L : Launch) (g : Nat) (d : D) (s : IdleSite)
    (hs : d.site = .leave s) : facts P L g d = idleEnd P L g s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := d
  subst hs
  cases s <;> rfl

/-- The elements of a coordinate load that already fired, in order. -/
def accOf (d : D) : List Value :=
  match d.site with
  | .coord1 _ => [d.ac.w0]
  | .coord2 _ => [d.ac.w0, d.ac.w1]
  | .coord3 _ => [d.ac.w0, d.ac.w1, d.ac.w2]
  | _ => []

/-- The first state: the election. -/
def init : D := { site := .elect }

/-- **The TMA warp as a code machine.** -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := init
  pc := (·.site.pc)
  facts := facts P L g
  sub := (·.site.sub)
  acc := accOf
  inv := fun _ => True
  next := succ P L g

end

set_option hygiene false in
/-- `tma_state d`: the fields of state `d`, its site `s`. -/
macro "tma_state " d:ident : tactic => `(tactic|
  obtain ⟨s, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := $d)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma

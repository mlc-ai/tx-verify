-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Flow.Code

@[expose] public section

/-! # The startup of every thread as a site machine

Every thread runs pcs 0 to 102. The ABI prefix (parameter pointers and launch registers, no
event) ends at the first shuffle (pc 6). Two full-warp shuffles from lane 0 follow: the
warpgroup index `tid >> 7` (`sh 0`, recorded as `x1`) and the warp index `tid >> 5` (`sh 1`,
recorded as `x2`). On warp 0 (`x2 = 0`) a first election lets one lane prefetch the three
tensor-map descriptors, a second lets one lane initialize the 23 mbarriers (`init n`, the
family `initFam n` of `Iface/Objects.lean`) and fence them (`fence`); the warp allocates Tensor
Memory (`alloc`; lane 0's store of the address is the instruction's second step, `allocSt`),
reads the allocated address back (`ld`), traps on a nonzero word (`trap`) and relinquishes the
allocation permit (`relinq`). Every thread meets the others at the CTA barrier (`bar`), and the
dispatch on `x1` reaches the `setmaxnreg` of warpgroup 0 (pc 103), 1 (1842) or 2 (2606)
(`enter r`, the fragment's exits).

A control machine: it follows every value an event returns. A shuffle records the word it
returns (a value that is not a 32-bit word is a pending fault), an election goes to both
outcomes, and the read-back goes to the relinquishment on a zero word and to the `trap` on any
other word (`afterLd`, the word Core's comparison reads from any value with a bit pattern); `trap`,
and the comparison's fault on a value without one, are undefined behaviour, the thread's last
event, after which the machine has no successor (`none`: a followed thread is not followed past
it). The
registers are the entry table (`Lib/Entry.lean`) and the startup's own terms (`values`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The warpgroups the dispatch reaches. -/
inductive Target where
  | wg0 | wg1 | wg2
  deriving DecidableEq

/-- The first instruction of each warpgroup's code: its `setmaxnreg`. -/
def Target.pc : Target → Nat
  | .wg0 => 103 | .wg1 => 1842 | .wg2 => 2606

inductive Site where
  | sh (j : Fin 2)
  | elect (j : Fin 2)
  | init (n : Fin 23)
  | fence
  | alloc
  | allocSt
  | ld
  | trap
  | relinq
  | bar
  | enter (r : Target)
  deriving DecidableEq

/-- The pcs of the 23 initializations. -/
def initPc (n : Fin 23) : Nat :=
  [39, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 71, 74, 76, 78, 80, 82, 84,
    86].getD n.val 0

/-- The mbarrier family initialization `n` initializes, in program order. -/
abbrev initFam (n : Fin 23) : MbarFam := MbarFam.ofInit n

def Site.pc : Site → Nat
  | .sh j => [6, 9].getD j.val 0
  | .elect j => [16, 31].getD j.val 0
  | .init n => initPc n
  | .fence => 87
  | .alloc | .allocSt => 91
  | .ld => 92
  | .trap => 95
  | .relinq => 96
  | .bar => 97
  | .enter r => r.pc

/-- Lane 0's address store is `tcgen05.alloc`'s second step. -/
def Site.sub : Site → Nat
  | .allocSt => 1
  | _ => 0

/-- A state: the site and the two words the shuffles returned. -/
structure D where
  site : Site
  x1 : BitVec 64 := 0
  x2 : BitVec 64 := 0

/-! ### Transitions -/

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- The state after the barrier: the dispatch's entry, the code's comparisons on `x1`. -/
def enterOf (d : D) : D :=
  if scmpi .eq .b d.x1 1 then { d with site := .enter .wg1 }
  else if scmpi .ne .b d.x1 0 then { d with site := .enter .wg2 }
  else { d with site := .enter .wg0 }

/-- The site after initialization `n`. -/
def initSucc (n : Fin 23) : Site :=
  if h : n.val + 1 < 23 then .init ⟨n.val + 1, h⟩ else .fence

/-- The word the comparison `setp.eq.b32` at pc 93 reads from the value the read-back rebuilds
to, before truncation to 32 bits: Core's `readBits` of a register reads an integer's bits and any
other value's bit pattern, and faults (`none`) on a pointer, a cache policy and a value without a
bit pattern. -/
def ldWord : Value → Option (BitVec 64)
  | .bits _ x => some x
  | .ptr .. | .policy => none
  | v => v.bitPattern.map (BitVec.ofNat 64)

/-- After the read-back of the allocated address (pcs 93–94): a zero word continues to the
relinquishment, any other word to the `trap`; a value the comparison cannot read faults at pc
93, undefined behaviour after which the machine has no successor (`none`). -/
def afterLd (d : D) (v : Value) : Option (Option D) :=
  match ldWord v with
  | some w =>
    if scmpi .eq .b w 0 then some (some { d with site := .relinq })
    else some (some { d with site := .trap })
  | none => none

/-- The successor after event `e`. -/
def succ (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .sh j =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      match j with
      | 0 => { d with site := .sh 1, x1 := x }
      | 1 => if scmpi .ne .b x 0 then { d with site := .bar, x2 := x }
        else { d with site := .elect 0, x2 := x }
    | _ => none
  | .elect j =>
    match e.kind with
    | .elect _ _ ld =>
      match j with
      | 0 => some (some { d with site := .elect 1 })
      | 1 => some (some (if PTX.laneOf (L := L) g = ld then { d with site := .init 0 }
          else { d with site := .alloc }))
    | _ => none
  | .init n => some (some { d with site := initSucc n })
  | .fence => some (some { d with site := .alloc })
  | .alloc => some (some (if PTX.laneOf (L := L) g = 0 then { d with site := .allocSt }
      else { d with site := .ld }))
  | .allocSt => some (some { d with site := .ld })
  | .ld =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v => afterLd d v
      | .error _ => none
    | _ => none
  | .trap => none
  | .relinq => some (some { d with site := .bar })
  | .bar => some (some (enterOf d))
  | .enter _ => none

/-! ### Register values -/

/-- The registers the startup computes beyond the entry table: the recorded words, the election
masks and the mbarrier addresses and counts. -/
def values (L : Launch) (d : D) : List (Nat × Value) :=
  [(462, w32 d.x1), (465, w32 d.x2),
   (521, w32 (i32 0)), (522, w32 (i32 (-1))), (524, w32 (i32 0)), (525, w32 (i32 (-1))),
   (526, w32 (i32 128)), (528, w32 (i32 1)), (543, w32 (i32 32)), (545, w32 (i32 129)),
   (553, sb L 0), (555, w32 (i32 512)), (2880, w32 (BitVec.ofNat 64 4286578688)),
   (527, sb L 222768), (529, sb L 222776),
   (530, sb L 222784), (531, sb L 222792),
   (532, sb L 222808), (533, sb L 222824),
   (534, sb L 222904), (535, sb L 222920),
   (536, sb L 222936), (537, sb L 222800),
   (538, sb L 222816), (539, sb L 222832),
   (540, sb L 222912), (541, sb L 222928),
   (542, sb L 222944), (544, sb L 222840),
   (546, sb L 222872), (547, sb L 222848),
   (548, sb L 222880), (549, sb L 222856),
   (550, sb L 222888), (551, sb L 222864),
   (552, sb L 222896), (554, sb L 222752)]

/-- The value of register `r` at state `d`: the startup's term, else the entry table's. -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values L d).lookup r).getD (entryVal L g r)

/-- The registers live at a site, without the two the program never writes. -/
abbrev liveAt (pc : Nat) : List Nat := (Flow.live pc).filter (fun r => !skipRegs.contains r)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (liveAt d.site.pc) (valueOf L g d)

/-- The startup as a code machine. -/
@[reducible] def code (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g where
  D := D
  init := ⟨.sh 0, 0, 0⟩
  pc := (·.site.pc)
  facts := facts L g
  sub := (·.site.sub)
  inv := fun _ => True
  next := succ L g

/-- The exits: the states at a warpgroup's first instruction. -/
def exitOf (d : D) : Option Target :=
  match d.site with
  | .enter r => some r
  | _ => none

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

-- SPDX-License-Identifier: Apache-2.0
module

public import Init.Data.Nat.ToString
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Kernels.TmlFa4Fwd.Proof.Startup.AbiFacts
public import Lemmas.Flow.ParamObject
import Kernels.TmlFa4Fwd.Proof.Startup.Transparency

@[expose] public section

/-! # The startup of every thread as a site machine

Every thread runs the same code from its first instruction to the role dispatch. The ABI prefix
(parameter loads, no event) ends at the first shuffle (pc 25). Three full-warp shuffles follow:
the dynamic shared base from lane 0 (`sh 0`, recorded as `x1`), then the warp index twice (`sh 1`,
`sh 2`, recorded as `x2`, `x3`). On warp 0 (`x3 = 0`) sixteen elections each let one lane
initialize two or three mbarriers (`elect j`, `init n`). Every thread then fences the
initializations (`fence`), meets the others at the CTA barrier (`bar`), and the dispatch on `x3`
reaches the first instruction of its role (`enter r`): the loader (warps 14, 15), the MMA warp
(12), the output warp (13), the softmax warps (0 to 7), the correction warps (8 to 11), or the
return when `x3` is no warp index of the CTA.

The machine follows every value an event returns (plan rule M1): a shuffle records the word it
returns, a value that is not a 32-bit word stops it (`some none`), and an election goes to both
outcomes. The registers live at each site are a function of the launch and the recorded words
(`values`); the dispatch is the code's own comparisons on `x3` (`enterOf`). The states `enter r`
are the fragment's exits: the glue (`Proof/Common/Roles.lean`) replaces each by its role's first
state. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Startup
open PTX PTX.Proof PTX.Flow
open Epilogue (r32 i32 addi andi scmpi mad32 shru)

noncomputable section

/-- The roles the dispatch reaches. `none`: the return, for a warp index outside `0 … 15`. -/
inductive Entry where
  | loader | mma | epilogue | softmax | correction | none
  deriving DecidableEq

/-- The first instruction of each role. -/
def Entry.pc : Entry → Nat
  | .loader => 179 | .mma => 1907 | .epilogue => 2769 | .softmax => 3102
  | .correction => 7746 | .none => 9205

inductive Site where
  | sh (j : Fin 3)
  | elect (j : Fin 16)
  | init (n : Fin 34)
  | fence
  | bar
  | enter (r : Entry)
  deriving DecidableEq

/-- The elections, and the mbarrier initializations (two per election, three after elections
2 and 3). -/
def electPc (j : Fin 16) : Nat :=
  [46, 56, 62, 73, 80, 90, 96, 105, 111, 119, 125, 135, 141, 151, 157, 166].getD j.val 0

def initPc (n : Fin 34) : Nat :=
  [50, 51, 60, 61, 66, 67, 68, 77, 78, 79, 84, 85, 94, 95, 100, 101, 109, 110, 115, 116, 123,
    124, 129, 130, 139, 140, 145, 146, 155, 156, 161, 162, 170, 171].getD n.val 0

def Site.pc : Site → Nat
  | .sh j => [25, 34, 35].getD j.val 0
  | .elect j => electPc j
  | .init n => initPc n
  | .fence => 172
  | .bar => 173
  | .enter r => r.pc

/-- A state: the site and the three words the shuffles returned. -/
structure D where
  site : Site
  x1 : BitVec 64 := 0
  x2 : BitVec 64 := 0
  x3 : BitVec 64 := 0

/-! ### Transitions -/

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- After the initializations of election `j`, or after election `j` on a lane it did not
elect: the next election, or the fence after the last (`afterSite`, a site of the code). After
elections `0`, `2`, …, `14` the code tests `x3 ≠ 0` again (`nonzeroSite`). -/
def afterSite (j : Fin 16) : Site :=
  [Site.elect 1, .elect 2, .elect 3, .elect 4, .elect 5, .elect 6, .elect 7, .elect 8, .elect 9,
    .elect 10, .elect 11, .elect 12, .elect 13, .elect 14, .elect 15, .fence].getD j.val .fence

/-- Where the code goes after block `j` when `x3 ≠ 0`: the fence after a group's last block
(elections `0`, `2`, …, `14`, after which the code tests `x3` again), else the next election. -/
def nonzeroSite (j : Fin 16) : Site :=
  [Site.fence, .elect 2, .fence, .elect 4, .fence, .elect 6, .fence, .elect 8, .fence, .elect 10,
    .fence, .elect 12, .fence, .elect 14, .fence, .fence].getD j.val .fence

def afterBlock (d : D) (j : Fin 16) : D :=
  if scmpi .ne .b d.x3 0 then { d with site := nonzeroSite j } else { d with site := afterSite j }

/-- The first initialization of each election's block. -/
def firstInit (j : Fin 16) : Site :=
  [Site.init 0, .init 2, .init 4, .init 7, .init 10, .init 12, .init 14, .init 16, .init 18,
    .init 20, .init 22, .init 24, .init 26, .init 28, .init 30, .init 32].getD j.val .fence

/-- The site after an initialization: the block's next one, or, after the block's last, the
election whose block it ends (read by `succ` as "after the block of"). -/
def initSucc (n : Fin 34) : Site :=
  [Site.init 1, .elect 0, .init 3, .elect 1, .init 5, .init 6, .elect 2, .init 8, .init 9,
    .elect 3, .init 11, .elect 4, .init 13, .elect 5, .init 15, .elect 6, .init 17, .elect 7,
    .init 19, .elect 8, .init 21, .elect 9, .init 23, .elect 10, .init 25, .elect 11, .init 27,
    .elect 12, .init 29, .elect 13, .init 31, .elect 14, .init 33, .elect 15].getD n.val .fence

/-- The state after the barrier: the dispatch's entry, the code's comparisons as a chain. -/
def enterOf (d : D) : D :=
  if scmpi .ne .b (andi d.x3 (-2)) 14 then
    if scmpi .eq .b d.x3 13 then { d with site := .enter .epilogue }
    else if scmpi .ne .b d.x3 12 then
      if scmpi .gt .s d.x3 7 then
        if scmpi .ne .b (andi d.x3 (-4)) 8 then { d with site := .enter .none }
        else { d with site := .enter .correction }
      else { d with site := .enter .softmax }
    else { d with site := .enter .mma }
  else { d with site := .enter .loader }

/-- The successor after event `e`. -/
def succ (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .sh j =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      match j with
      | 0 => { d with site := .sh 1, x1 := x }
      | 1 => { d with site := .sh 2, x2 := x }
      | 2 => if scmpi .ne .b x 0 then { d with site := .fence, x3 := x }
        else { d with site := .elect 0, x3 := x }
    | _ => none
  | .elect j =>
    match e.kind with
    | .elect _ _ ld =>
      some (some (if laneOf L g = ld then { d with site := firstInit j }
        else afterBlock d j))
    | _ => none
  | .init n =>
    match initSucc n with
    | .elect j => some (some (afterBlock d j))
    | s => some (some { d with site := s })
  | .fence => some (some { d with site := .bar })
  | .bar => some (some (enterOf d))
  | .enter _ => none

/-! ### Register values -/

/-- A 32-bit word in a register. -/
abbrev w32 (x : BitVec 64) : Value := .bits 32 x

/-- A special register's word, as `mov.u32` reads it. -/
abbrev sreg (n : Nat) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 n)

/-- The thread's warp in its CTA, as the code computes it from the thread and block indices. -/
abbrev warpW (L : Launch) (g : Nat) : BitVec 64 :=
  shru (mad32 (mad32 (sreg (L.ntid.get .y)) (sreg ((L.tidOf g).get .z)) (sreg ((L.tidOf g).get .y)))
    (sreg (L.ntid.get .x)) (sreg ((L.tidOf g).get .x))) 5

/-- The CTA index as the dispatch reads it, under the launch with the parameters the startup reads
made explicit (`Epilogue.params`); it is the launch's own (`Epilogue.params` rewrites it). -/
abbrev ctaX (p : Params) (L : Launch) (g : Nat) : Nat :=
  ((explicitParams L (Epilogue.ps p)).ctaidOf (g / (explicitParams L (Epilogue.ps p)).block)).get .x

/-- The registers the startup computes, as functions of the recorded words. The ABI registers
(parameter loads before the first event) are `Prologue.abiFacts`. -/
def values (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  [(2535, w32 d.x1), (1673, w32 d.x2), (1062, w32 d.x3),
   (1061, w32 (sreg ((L.tidOf g).get .x))), (1672, w32 (warpW L g)),
   (1063, w32 (addi d.x1 32)), (1064, w32 (addi d.x1 16)), (1065, w32 (addi d.x1 80)),
   (1066, w32 (addi d.x1 56)), (1067, w32 (addi d.x1 112)), (1068, w32 (addi d.x1 96)),
   (1069, w32 (addi d.x1 192)), (1070, w32 (addi d.x1 320)), (1071, w32 (addi d.x1 336)),
   (6495, w32 (addi d.x1 144)), (6497, w32 (addi d.x1 224)), (2390, w32 (addi d.x1 208)),
   (1178, w32 (addi d.x1 68608)),
   (1675, w32 (i32 1)), (1677, w32 (i32 1)), (1679, w32 (i32 64)), (1681, w32 (i32 1)),
   (1683, w32 (i32 1)), (1685, w32 (i32 256)), (1687, w32 (i32 4)), (1689, w32 (i32 1)),
   (1691, w32 (i32 1)), (1693, w32 (i32 128)), (1695, w32 (i32 128)), (1697, w32 (i32 128)),
   (1699, w32 (i32 128)), (1701, w32 (i32 32)), (1703, w32 (i32 1)), (1705, w32 (i32 4)),
   (1072, w32 (sreg (ctaX p L g))),
   (7170, w32 (sreg p.batch)), (7203, w32 (sreg p.batch)), (7228, w32 (sreg p.batch)),
   (7247, w32 (sreg p.batch)), (7277, w32 (sreg p.batch))]

/-- The value of register `r` at state `d`. -/
def valueOf (p : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((values p L g d).lookup r).getD (((Prologue.abiFacts p L).lookup r).getD (.pred false))

abbrev facts (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live d.site.pc) (valueOf p L g d)

/-- The startup as a code machine. -/
@[reducible] def code (p : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g
    where
  D := D
  init := ⟨.sh 0, 0, 0, 0⟩
  pc := (·.site.pc)
  facts := facts p L g
  inv := fun _ => True
  next := succ L g

end
end PTX.Kernels.TmlFa4Fwd.Proof.Startup

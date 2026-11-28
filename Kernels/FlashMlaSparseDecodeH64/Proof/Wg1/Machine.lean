-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Idle
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexVal
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Flow.Code

@[expose] public section

/-! # Warpgroup 1's head and idle code as site machines

**The head** (pcs 1842–1849). The four warps of warpgroup 1 enter at `setmaxnreg.dec 72`
(`smr`), shuffle lane 0's warp index (`hsh`, pc 1843) and dispatch on the word (pcs
1844–1849): `4` to the MMA code, `5` to the TMA code, `7` to the index code, any other word to the
idle code. A control machine: it follows the code's dispatch on the word it receives. Its exits
are the sub-roles' first events: the MMA and TMA elections (pcs 1853 and 2165, after the masks'
moves, `mma`, `tma`) and the idle code's first event (`idle`), which depends on the launch
(`idleFirst`). On the word `7` the head walks the index warp's parameter prefix (pcs 2332–2359) to
its first event (`index`, at `ixFirst`, with the index role's control table `ixFacts`).

**The idle code** (pcs 2587–2605, warp 6 and the lanes of warps 4 and 5 that lose their
election). A CTA beyond the batch returns (`ret`); else the code loads the row's top-k length when
its pointer is set (`ldA`, pc 2596) and the extra length when that pointer is set (`ldB`, pc
2601), meets the other roles at named barrier 12 (`bar`, pc 2604) and returns. The loads' values
are not used. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-! ### The idle code -/

section
variable (P : Params) (L : Launch) (g : Nat)

/-- After a length load: the next site, unless the loaded bytes make no value (the thread
faults). -/
def afterNc (e : Event) (s : IdleSite) : Option (Option IdleSite) :=
  match e.kind with
  | .nc _ bs =>
    match rebuild 3 bs with
    | .ok _ => some (some s)
    | .error _ => none
  | _ => none

/-- The successor after an event of the idle code. -/
def isucc (s : IdleSite) (e : Event) : Option (Option IdleSite) :=
  match s with
  | .ldA => afterNc e (idleAfterA P)
  | .ldB => afterNc e .bar
  | .bar => some (some .ret)
  | .ret => none

end

/-- The idle code as a code machine. -/
@[reducible] def idle (P : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := IdleSite
  init := idleFirst P L g
  pc := IdleSite.pc
  facts := fun s => Flow.factsFrom (Flow.live s.pc) (idleVal P L g)
  inv := fun _ => True
  next := isucc P

/-! ### The head -/

inductive Site where
  | smr | hsh | mma | tma | index | idle
  deriving DecidableEq

/-- The sub-roles the head's exits pass to. -/
inductive Exit where
  | mma | tma | index | idle
  deriving DecidableEq

section
variable (P : Params) (L : Launch) (g : Nat)

def Site.pc : Site → Nat
  | .smr => 1842 | .hsh => 1843 | .mma => 1853 | .tma => 2165
  | .index => (ixFirst P L g).1.pc
  | .idle => (idleFirst P L g).pc

/-- The registers' values: the idle code's table at its first event, else the entry table. -/
def headVal : Site → Nat → Value
  | .idle => idleVal P L g
  | _ => entryVal L g

/-- The facts at a site: the index exit's are the index role's control table at its first
event (`ixFacts`), every other site's the live registers of `headVal`'s table. -/
abbrev headFacts : Site → List (Nat × Value)
  | .index => ixFacts P L g (ixFirst P L g).2 (ixFirst P L g).1
  | .smr => Flow.factsFrom (Flow.live 1842) (entryVal L g)
  | .hsh => Flow.factsFrom (Flow.live 1843) (entryVal L g)
  | .mma => Flow.factsFrom (Flow.live 1853) (entryVal L g)
  | .tma => Flow.factsFrom (Flow.live 2165) (entryVal L g)
  | .idle => Flow.factsFrom (Flow.live (idleFirst P L g).pc) (idleVal P L g)

/-- The dispatch on the shuffled word (pcs 1844–1849). -/
def dispatch (v : Value) : Option (Option Site) :=
  match v with
  | .bits 32 x =>
    if scmpi .eq .b x 7 then some (some .index)
    else if scmpi .eq .b x 5 then some (some .tma)
    else if scmpi .ne .b x 4 then some (some .idle) else some (some .mma)
  | _ => some none

/-- The successor after event `e`; the exits have none (the sub-roles follow them). -/
def succ (s : Site) (e : Event) : Option (Option Site) :=
  match s with
  | .smr => some (some .hsh)
  | .hsh =>
    match e.kind with
    | .shfl _ _ _ _ v _ => dispatch v
    | _ => none
  | _ => none

/-- The exits. -/
def exitOf : Site → Option Exit
  | .mma => some .mma
  | .tma => some .tma
  | .index => some .index
  | .idle => some .idle
  | _ => none

end

/-- Warpgroup 1's head as a code machine. -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := Site
  init := .smr
  pc := Site.pc P L g
  facts := headFacts P L g
  inv := fun _ => True
  next := succ

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1

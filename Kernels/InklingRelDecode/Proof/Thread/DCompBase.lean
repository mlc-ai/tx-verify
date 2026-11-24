-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartAll
public import Kernels.InklingRelDecode.Proof.Thread.ProAExit
public import Kernels.InklingRelDecode.Proof.Thread.SmEntryAll
public import Kernels.InklingRelDecode.Proof.Thread.SmAll
public import Kernels.InklingRelDecode.Proof.Thread.BrAll
public import Kernels.InklingRelDecode.Proof.Thread.EpiAll
public import Kernels.InklingRelDecode.Proof.Thread.DCompTail
public import Lemmas.Flow.Compose

@[expose] public section

/-!
# The default-partition thread (warps 0 to 3) as one code machine: states and successors

A thread of warp 0 to 3 (`tid < 128`) runs, in this order, five regions that exist as separate
machines:

* the common start (`DStart`, pc 0 to 27): the Tensor Memory allocation, two `bar.sync 0`, the
  load of the base word, the warp-index broadcast, and the branch to the default path;
* the prologue (`ProA`, pc 27 to 573): mbarrier initialization, the loads of `cu_seqlens_q`,
  `seq_lens`, the block table and `Q`, the K/V preloads, and the last `barrier.sync 1`;
* the softmax loop (`Sm`, pc 574 to 2332 and the loop test at pc 1050);
* the bridge's first part (`Br`, pc 2560 to 2564): five local instructions (`setp.lt`,
  `griddepcontrol`, `lg2`, `fma`, `mov`) that none of the regions' events cover;
* the epilogue (`Epi`, pc 2565 to 2855): its first event is the poll of `o_final` that every
  thread executes (also with `num_iters < 1`); the local code after the poll (the zero test, the
  zero pairs, the branch of pc 2600) is the epilogue's.

This file states the thread's composed machine `code L g Q`: the abstract states `St`, the registers
live at each (`facts`), the invariant (`Inv`), and the successor (`next`). The five regions' own
`next` functions are used unchanged except at the four places where the thread passes from one
region to the next:

* **the common start to the prologue.** The last event of the common start is the shuffle of
  pc 17; its successor `DStart.Site.toProA` is the prologue's first site (`setmaxnreg.inc`,
  pc 27), so the composed machine has no state for `toProA`: the shuffle's successor is
  `ProA.D.start (DStart.inh L g Q (ProA.shW w)) w`, with `w` the loaded base word.
* **the prologue to the softmax region.** The prologue's last site `bar18` is the `barrier.sync 1`
  of pc 573. Its successor is `SmEntry.d0 (SmEntry.entOf Q L g dt)` (`SmEntry.ProA_to_Sm`), where
  `dt` holds the three loaded words; the machine follows only if they are the words of the
  request (`ProA.WordsMatch`, a premise of the protocol layer).
* **the softmax region to the epilogue, through the bridge.** The loop leaves the region at the
  test of pc 1050 (`@%p91 bra 2560`), after one of four events (`leaves`: the `bar.sync 1` of
  pc 575 for a masked lane, the last preload, the `bar.sync` of pc 1012 for a thread other than
  thread 0, the arrival of pc 1013). Pc 2560 to 2564 contain no event, so the bridge's first part
  is not a state of a code machine: it is part of the transition. The successor of such an event
  is the epilogue's first state, the poll of `o_final` (`Epi.D.entry`): `Epi.D.start`
  (`num_iters >= 1`) or `Epi.D.startSk` (`num_iters < 1`) on `Br.prm (exitIn L g d)`, where the
  `lg2`/`fma` outcomes exist (`In.NoFault`); where a float step of the bridge has no outcome the
  thread is dead (`next = none`).
* **the epilogue's end** is the epilogue's own: its last state is the `ret` (pc 2855), which no
  event follows.

`exitIn L g d` reads the registers live at pc 2560 off the softmax region's register table
(`DCompTail.lean` proves that `Br.exitFacts (exitIn L g d)` is `Sm.factsAt L g 2560 d`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000


/-! ### The states -/

/-- A default-partition thread's states: the common start (`.dstart`, never at its last site
`toProA`, which is the prologue's first state), the prologue, the softmax region and the
epilogue. -/
inductive St where
  | dstart (d : DStart.D)
  | pro (d : ProA.D)
  | sm (d : Sm.D)
  | epi (d : Epi.D)

/-- The program counter of a state. -/
def pc : St → Nat
  | .dstart d => d.site.pc
  | .pro d => d.site.pc
  | .sm d => d.site.pc
  | .epi d => d.site.pc

/-- The sub-step of a state: nonzero only at the second step of the allocation's instruction. -/
def sub : St → Nat
  | .dstart d => d.site.sub
  | .pro d => ProA.sub d
  | .sm _ => 0
  | .epi _ => 0

/-- The accumulator of a state: no vector load is in progress in any region. -/
def acc : St → List Value
  | .pro d => ProA.acc d
  | _ => []

/-- The registers live at a state, with their values. -/
def facts (L : Launch) (g : Nat) (Q : Params) : St → List (Nat × Value)
  | .dstart d => DStart.facts L g Q d
  | .pro d => ProA.facts L g d
  | .sm d => Sm.facts L g d
  | .epi d => Epi.facts d

/-! ### The invariant -/

/-- The invariant of the composed states: the region's own, and for the prologue that the
inherited registers are the common start's (`DStart.inh L g Q tm`, with `tm` the 32-bit number
of the Tensor Memory base word), which the softmax region's entry needs (the word is good there,
`ProA.Inv.wd`); the common start is not at its
last site, which is the prologue's first state; the epilogue's warp register is the thread's warp
(set by `exitIn`, kept because the epilogue does not change `pr`). -/
def Inv (L : Launch) (g : Nat) (Q : Params) : St → Prop
  | .dstart d => DStart.Inv L g Q d ∧ d.site ≠ DStart.Site.toProA
  | .pro d => ProA.Inv L g d ∧ ∃ tm, tm < 2 ^ 32 ∧ d.dt.pro = DStart.inh L g Q tm
  | .sm d => Sm.Inv L g d
  | .epi d => Epi.Inv d ∧ d.pr.w = g % L.block / 32

/-! ### The loop's exit and the bridge -/

open scoped Classical in
/-- The successor of the event that ends the loop: through the bridge's first part, the
epilogue's first state, the poll of `o_final` with the flag `num_iters < 1`; where a float step of
the bridge has no outcome, the thread is dead. -/
def exitNext (L : Launch) (g : Nat) (d : Sm.D) : Option (Option St) :=
  if (exitIn L g d).NoFault then
    some (some (.epi (if (exitIn L g d).skip then Epi.D.startSk (Br.prm (exitIn L g d))
      else Epi.D.start (Br.prm (exitIn L g d)))))
  else none

/-! ### The successors -/

/-- The common start's successor: the shuffle's successor `toProA` is the prologue's first
state. -/
def dstartNext (L : Launch) (g : Nat) (Q : Params) (d : DStart.D) (e : Event) :
    Option (Option St) :=
  (DStart.next L g d e).map (Option.map fun d' =>
    if d'.site = DStart.Site.toProA then
      .pro (ProA.D.start (DStart.inh L g Q (ProA.shW d'.w)) d'.w)
    else .dstart d')

open scoped Classical in
/-- The prologue's successor: its own, except at its last site, whose successor is the softmax
region's first state when the three loaded words are the request's and the base word is good
(`ProA.wGood`; on any other word the machine stops there). -/
def proNext (L : Launch) (g : Nat) (Q : Params) (d : ProA.D) (e : Event) :
    Option (Option St) :=
  if d.site = ProA.Site.bar18 then
    if ProA.WordsMatch Q (ProA.cta L g .z) d.dt ∧ ProA.wGood d.dt = true then
      some (some (.sm (SmEntry.d0 (SmEntry.entOf Q L g d.dt))))
    else some none
  else (ProA.next L g d e).map (Option.map .pro)

open scoped Classical in
/-- The softmax region's successor: its own, except at the events that end the loop. -/
def smNext (L : Launch) (g : Nat) (d : Sm.D) (e : Event) : Option (Option St) :=
  if leaves L g d e then exitNext L g d else (Sm.next L g d e).map (Option.map .sm)

/-- The abstract successor after event `e`. -/
def next (L : Launch) (g : Nat) (Q : Params) : St → Event → Option (Option St)
  | .dstart d, e => dstartNext L g Q d e
  | .pro d, e => proNext L g Q d e
  | .sm d, e => smNext L g d e
  | .epi d, e => (Epi.next d e).map (Option.map .epi)

/-- **The default-partition thread of the launch `L` with parameters `Q` as one code machine.** -/
@[reducible] def code (L : Launch) (g : Nat) (Q : Params) : Flow.Code kernel asms L g where
  D := St
  init := .dstart (DStart.D.start L g)
  pc := pc
  facts := facts L g Q
  sub := sub
  acc := acc
  inv := Inv L g Q
  next := next L g Q

/-- **The common start's machine follows the thread** at every state but the broadcast of the
warp index (`shfl`) and the hand-off site `toProA` (never a state: the step into it is the
prologue's first state); at the read of the base word it follows every loaded word. -/
theorem dstart_next_follows {d : DStart.D} {e : Event} (h2 : d.site ≠ .shfl)
    (h3 : d.site ≠ .toProA) : next L g Q (.dstart d) e ≠ some none := by
  obtain ⟨s, tm⟩ := d
  cases s <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false] at h2 h3 <;>
    simp only [next, dstartNext, DStart.next] <;> (repeat' split) <;> simp_all

/-- **The epilogue's machine follows the thread** at every state but the 64-word load (`ld`, a
shape condition on the loaded words); at the broadcast it follows every received word. -/
theorem epi_next_follows {d : Epi.D} {e : Event} (h2 : d.site ≠ .ld) :
    next L g Q (.epi d) e ≠ some none := by
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false] at h2 <;>
    simp only [next, Epi.next, Epi.stNext] <;> (repeat' split) <;> simp_all

end
end PTX.Kernels.InklingRelDecode.Proof.DComp

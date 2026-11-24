-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompTail

@[expose] public section

/-! # The softmax region, the bridge and the epilogue as one fragment

After the prologue's exit (pc 574) a thread of warps 0 to 3 runs the softmax loop (pc 574 to
2330, the loop test at pc 1050), the five local instructions of the bridge (pc 2560 to 2564) and
the epilogue (pc 2565 to its return at pc 2855). This fragment is these three regions with the
flat machines of the first tree (`Proof.Sm`, `Proof.Epi`), glued where the loop ends:

* a softmax state steps by `Sm.next`, except after an event that ends the loop
  (`DComp.leaves`), whose successor is the epilogue's first state (the poll of `o_final`,
  `Epi.D.entry`) on the numbers the loop hands the bridge (`DComp.exitIn`), or `none` where a
  float step of the bridge has no outcome (the thread is dead there);
* an epilogue state steps by `Epi.next`; its return (pc 2855) has no successor.

Both flat machines follow every value (rule M1): the only stops are kinds of returned values (a
bias word that is no `bf16` number, `Sm.isBf16`; a Tensor Memory load of another length than 64,
`Epi.next`); a load whose bytes do not rebuild, a float step without an outcome and a Tensor Memory
lane field outside the warp's lanes are deaths (`none`). The fragment's steps are the flat
machines' (`Tail/Steps.lean`); its states are regrouped into site families already
(`Sm.Site.pre j`, `Sm.Site.nxt j`, `Epi.Site.stO k`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2.Tail
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

/-- A state: a softmax state or an epilogue state. -/
inductive St where
  | sm (d : Proof.Sm.D)
  | epi (d : Proof.Epi.D)

/-- The program counter of a state. -/
def pc : St → Nat
  | .sm d => d.site.pc
  | .epi d => d.site.pc

/-- The registers of a state, by the flat machines' tables. -/
def facts (L : Launch) (g : Nat) : St → List (Nat × Value)
  | .sm d => Proof.Sm.facts L g d
  | .epi d => Proof.Epi.facts d

/-- The invariant: the flat machines', and at an epilogue state that its warp register is the
thread's warp. -/
def Inv (L : Launch) (g : Nat) : St → Prop
  | .sm d => Proof.Sm.Inv L g d
  | .epi d => Proof.Epi.Inv d ∧ d.pr.w = g % L.block / 32

open scoped Classical in
/-- The successor of an event that ends the loop: through the bridge, the epilogue's first state,
or death where a float step of the bridge has no outcome. -/
def exitNext (L : Launch) (g : Nat) (d : Proof.Sm.D) : Option (Option St) :=
  if (Proof.DComp.exitIn L g d).NoFault then
    some (some (.epi (Proof.Epi.D.entry (Proof.Br.prm (Proof.DComp.exitIn L g d))
      (Proof.DComp.exitIn L g d).skip)))
  else none

open scoped Classical in
/-- **The successor after event `e`.** -/
def next (L : Launch) (g : Nat) : St → Event → Option (Option St)
  | .sm d, e =>
    if Proof.DComp.leaves L g d e then exitNext L g d
    else (Proof.Sm.next L g d e).map (Option.map .sm)
  | .epi d, e => (Proof.Epi.next d e).map (Option.map .epi)

/-- **The fragment** from the softmax state `d0`. -/
@[reducible] def code (L : Launch) (g : Nat) (d0 : Proof.Sm.D) :
    Flow.Code kernel Assumptions.all L g where
  D := St
  init := .sm d0
  pc := pc
  facts := facts L g
  inv := Inv L g
  next := next L g

end
end PTX.Kernels.InklingRelDecode.Proof2.Tail

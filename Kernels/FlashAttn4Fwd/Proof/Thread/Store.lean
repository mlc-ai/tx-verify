-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Flow.Sites
public import Kernels.FlashAttn4Fwd.Flow.Code
public import Kernels.FlashAttn4Fwd.Assumptions
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWork
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint

@[expose] public section

/-! # The epilogue store warp as abstract states

Warp 13 of both CTAs (all 32 lanes) walks the static schedule of its cluster (`Work`). For
item `i` it handles the two output stages `st = 0, 1`: it waits for the correction warps to
have staged the stage (`oStaged st`, `+256 + 8 st`, parity `i % 2`), issues the stage's two
TMA stores (one per 64-column half `h`), commits them as a bulk group; after both stages it
waits until at most one group still reads shared memory (`wait_group.read 1`), frees stage 0
(`oFree 0`, `+272`), waits for the last group and frees stage 1 (`+280`). Then it moves to the
next item or leaves.

A state is the next event and the item index `i`; every register is a function of the
site and `i` (`table`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Store
open PTX PTX.Proof PTX.Flow
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000

/-- The store warp's next event. -/
inductive Site where
  /-- `setmaxnreg.dec 72`, the role's first instruction. -/
  | setMaxReg
  /-- The poll of stage `st`'s staged barrier. -/
  | wait (st : Fin 2)
  /-- The TMA store of half `h` of stage `st`. -/
  | tma (st h : Fin 2)
  /-- The bulk-group commit of stage `st`. -/
  | commit (st : Fin 2)
  /-- `cp.async.bulk.wait_group.read 1` (`r = 0`) and `… 0` (`r = 1`). -/
  | drain (r : Fin 2)
  /-- The arrival freeing stage `st`. -/
  | free (st : Fin 2)
  /-- The common exit. -/
  | exit
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_3
  | .wait 0 => Flow.mbarWait_28 | .wait 1 => Flow.mbarWait_29
  | .tma 0 0 => Flow.tensorCopy_10 | .tma 0 1 => Flow.tensorCopy_11
  | .tma 1 0 => Flow.tensorCopy_12 | .tma 1 1 => Flow.tensorCopy_13
  | .commit 0 => Flow.bulkCommit_0 | .commit 1 => Flow.bulkCommit_1
  | .drain 0 => Flow.bulkWait_0 | .drain 1 => Flow.bulkWait_1
  | .free 0 => Flow.mbarArrive_8 | .free 1 => Flow.mbarArrive_9
  | .exit => Flow.exit_0

/-- A store state: the next event and the index of the current item. -/
structure D where
  site : Site
  i : Nat

open Work in
/-- The output row of item `i` of this CTA as the code computes it: the query block shifted
by 9 (`shl.b32`), `or` the CTA's 128-row half (`%r67 = %r3 << 7`). -/
def orowW (L : Launch) (g i : Nat) : BitVec 64 :=
  orW (shlW (mblkW L g i) (BitVec.ofInt 64 9))
    (shlW (BitVec.ofNat 64 (rank L g)) (BitVec.ofInt 64 7))

open Work in
/-- The registers of the store role at item `i`. -/
def table (L : Launch) (g i : Nat) : List (Nat × Value) :=
  [(390, .bits 32 (nbS1W L)), (391, .bits 32 (nbS2W L)), (394, .bits 32 (hS1W L)),
   (395, .bits 32 (hS2W L)),
   (396, sb L 19456), (397, sb L 35840), (398, sb L 52224), (399, sb L 3072),
   (400, .bits 32 (GW L)), (401, sb L 280),
   (402, .bits 32 (shlW (BitVec.ofNat 64 (rank L g)) (BitVec.ofInt 64 7))), (971, sb L 264),
   (973, .bits 32 (orowW L g i)), (974, .bits 32 (immW 0)), (975, .bits 32 (immW 64)),
   (976, .bits 32 (orW (orowW L g i) (BitVec.ofInt 64 256))), (977, .bits 32 (immW 1)),
   (3905, b32 (totOf L)), (3925, .bits 32 (workW L g i)), (3926, .bits 32 (batchW L g i)),
   (3927, .bits 32 (headW L g i)), (3928, .bits 32 (mblkW L g i)),
   (3929, .bits 32 (phaseW i)),
   (4099, .ptr 64 true (.param (param "7")) 0), (4100, .bits 64 (truncBits 64 (BitVec.ofInt 64 0)))]

/-- The value of register `r` at state `d`: the role's table, else the prologue's. -/
def valueOf (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((table L g d.i).lookup r).getD (Prologue.valueOf L g 13 (rankOf L g) r)

/-- The registers live at `pc`, with their values in state `d`. -/
def factsAt (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf L g d)

abbrev facts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) := factsAt L g d.site.pc d

/-- Outside the exit, the current item is one of the cluster's items. -/
def Inv (L : Launch) (g : Nat) (d : D) : Prop := d.site ≠ .exit → d.i < Work.T L g

/-- After item `i`: the next item, or the exit. -/
def itemEnd (L : Launch) (g : Nat) (d : D) : D :=
  if d.i + 1 < Work.T L g then ⟨.wait 0, d.i + 1⟩ else ⟨.exit, d.i⟩

/-- The abstract successor after event `e`. A site whose event is counted moves on only with
an event of its kind (an undefined behaviour stops the machine). -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg => some (some (if 0 < Work.T L g then ⟨.wait 0, 0⟩ else ⟨.exit, 0⟩))
  | .wait st =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some { d with site := if ok then .tma st 0 else .wait st })
    | _ => none
  | .tma st h =>
    match e.kind with
    | .tensorStore _ _ => some (some { d with site := if h = 0 then .tma st 1 else .commit st })
    | _ => none
  | .commit st =>
    match e.kind with
    | .bulkCommit => some (some { d with site := if st = 0 then .wait 1 else .drain 0 })
    | _ => none
  | .drain r =>
    match e.kind with
    | .bulkWait _ _ => some (some { d with site := .free r })
    | _ => none
  | .free st =>
    match e.kind with
    | .arrive _ _ _ _ _ =>
      some (some (if st = 0 then { d with site := .drain 1 } else itemEnd L g d))
    | _ => none
  | .exit => none

/-! The equation lemmas of the definitions the step files unfold, generated here once (two
step files generating them each could not be imported together). -/

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Store

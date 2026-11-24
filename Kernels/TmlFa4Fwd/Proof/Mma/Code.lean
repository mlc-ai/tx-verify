-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Lemmas.Flow.Glue

@[expose] public section

/-! # The MMA warp's code: the startup machine glued before the role machine

The definitions of `Mma/Startup.lean`, which proves their step obligations. This file imports no
step proof, so that the thread machine (`Common/Roles.lean`) does not either. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The startup states: the `setmaxnreg`, the allocation, its address write on lane 0, and the
hand-off at the first named barrier. -/
inductive Start where
  | set | alloc | wr | enter
  deriving DecidableEq

def Start.pc : Start → Nat
  | .set => 1907
  | .alloc | .wr => 1909
  | .enter => 1910

/-- The startup machine. -/
@[reducible] def S (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g where
  D := Start
  init := .set
  pc := Start.pc
  facts := fun s => Flow.factsFrom (Flow.live s.pc) (valueOf p L g ent ⟨.bar1, {}⟩)
  sub := fun | .wr => 1 | _ => 0
  inv := fun _ => True
  next := fun s _ => match s with
    | .set => some (some .alloc)
    | .alloc => some (some (if laneOf L g = 0 then .wr else .enter))
    | .wr => some (some .enter)
    | .enter => none

/-- The startup machine's exit: its hand-off state. -/
def Start.exit : Start → Option Unit
  | .enter => some ()
  | _ => none

/-- The MMA warp's machine from its `setmaxnreg`. -/
abbrev G (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g :=
  Code.glue (S p L g ent) (fun _ => code p L g ent) Start.exit

/-- The registers live at the `setmaxnreg` that the warp never reads, with their startup values:
three barrier addresses and two launch words. -/
def ent (p : Params) (L : Launch) (r : Nat) : Value :=
  if r = 1069 then b32 (L.sharedBase + 192) else if r = 2390 then b32 (L.sharedBase + 208)
  else if r = 6497 then b32 (L.sharedBase + 224) else if r = 7500 then b64 p.lseBase
  else if r = 7501 then b64 p.lseStride else .pred false

/-- **The MMA warp's fragment**: its machine from the role's entry, the `setmaxnreg` at pc 1907.
The registers live there are the startup's (`ent` for those the warp never reads). -/
abbrev M (p : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  G p L g (ent p L)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma

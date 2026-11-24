-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Lemmas.Flow.Counted
public import Lemmas.Kernel.Counted

@[expose] public section

/-! # The MMA warp's ledger classes

The definitions of `Mma/Ledger.lean`, apart from its step and shape facts. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the ledger. -/
inductive Cnt where
  /-- Successful polls of a barrier. -/
  | acquire (l : Loc)
  /-- Tensor Core commits to a barrier. -/
  | commit (l : Loc)
  /-- MMA issues. -/
  | mma
  /-- Named-barrier arrivals. -/
  | bar
  /-- Elections the lane wins, and elections it loses. -/
  | won
  | lost
  deriving DecidableEq

/-- The classes of an event of lane `g`. -/
def cls (L : Launch) (g : Nat) : Cnt → Event → Bool
  | .acquire l, e => match e.kind with | .wait m _ true _ _ => decide (m = l) | _ => false
  | .commit l, e => match e.kind with | .tc (.commit s) => decide (s.mbar = l) | _ => false
  | .mma, e => match e.kind with | .tc (.mma ..) => true | _ => false
  | .bar, e => match e.kind with | .bar .. => true | _ => false
  | .won, e => match e.kind with
    | .elect m _ ld => decide (m = 2 ^ 32 - 1 ∧ ld = laneOf L g) | _ => false
  | .lost, e => match e.kind with
    | .elect m _ ld => decide (m = 2 ^ 32 - 1 ∧ ld ≠ laneOf L g) | _ => false

/-- The MMA warp's machine with its ledger. -/
abbrev MC (p : Params) (L : Launch) (g : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g :=
  (code p L g ent).counted (cls L g)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof2.Mma.Steps
public import Lemmas.Kernel.Counted

@[expose] public section

/-! # The MMA warp's ledger

The MMA warp's machine with a ghost count per event class (`Code.counted`, lane L's ghost
ledger): the successful polls of each barrier, the Tensor Core commits to each barrier, the
MMAs, the named-barrier arrivals, and the full-mask elections the lane wins and loses (only the
lane that wins an election commits after it). The counted machine
has the machine's steps and shape table (`stepAt`, `shape`), and along a run from its first
state each count is the number of the run's events of its class (`ledger`), by construction. The
closed forms of the counts at each site are conjuncts of the role's reference invariant
(`Ref.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Mma
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

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem stepAt_counted (hp : Pre p L m) (hg : g < L.threads) (d : (MC p L g ent).D) :
    (MC p L g ent).StepAt d :=
  Code.counted_steps (stepAt hp hg d.1) d.2

theorem shape_counted (hp : Pre p L m) : (MC p L g ent).Shape (fun d e => Ev p L g d.1 e) :=
  Code.Shape.counted (shape hp)

/-- **The MMA warp's ledger**: along a run of the counted machine from a state with counts `n0`,
each count grows by the number of the run's events of its class. -/
theorem ledger {d0 : D} {n0 : Cnt → Nat} {es : List Event} {dn : (MC p L g ent).D}
    (h : (MC p L g ent).toMachine.after (some (d0, n0)) es = some (some dn)) (c : Cnt) :
    dn.2 c = n0 c + es.countP (cls L g c) :=
  Frame.counted_after h c

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Mma

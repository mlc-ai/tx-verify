-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Lemmas.Flow.Counted
public import Lemmas.Kernel.Counted

@[expose] public section

/-! # The softmax warps' ledger

The softmax machine with a ghost count per event class (`Code.counted`, lane L's ghost ledger):
the arrivals at each of the stage's barriers, the successful polls of each, the arrivals at
barrier 2, at the warp group's and at the stage's named barrier, the Tensor Memory loads and
stores, the shared-memory stores, the warp collectives (shuffles and ballots, for the collective
source) and the elections the lane wins per program counter (only the elected lane arrives at the
P-ready barrier, so that count is tied to the won elections, not to the state). Along a run from
its first state each count is the number of the run's events of its class (`Frame.counted_after`),
by construction. The closed forms of the counts at each site are the count conjuncts of the role's
reference invariant (`Ref.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The stage's offset of its barriers from the shared base: eight in the second stage. -/
def stS (L : Launch) (g : Nat) : Nat := if stg L g then 8 else 0

/-- The stage's barrier at offset `o` from its base. -/
def bl (L : Launch) (g o : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + (stS L g + o)⟩

/-- The event classes of the ledger. -/
inductive Cnt where
  /-- mbarrier arrivals at the stage's barrier at offset `o`. -/
  | arrive (o : Nat)
  /-- Successful polls of the stage's barrier at offset `o`. -/
  | acquire (o : Nat)
  /-- Arrivals at barrier 2, at the warp group's named barrier with the correction warps, and
  at the stage's named barrier. -/
  | bar2 | nb | sb
  /-- Tensor Memory loads and stores. -/
  | tcld | tcst
  /-- Stores (one per element; the role stores to shared memory only, and its shape table states
  the stores without their addresses). -/
  | sst
  /-- Shuffles and ballots. -/
  | shfl | vote
  /-- Elections at program counter `pc` that the lane wins. -/
  | won (pc : Nat)
  deriving DecidableEq

/-- The classes whose counts are closed forms in the places. -/
def Cnt.pointed : Cnt → Bool
  | .arrive o => o != 112
  | .shfl | .vote | .won _ => false
  | _ => true

/-- The classes of an event of lane `g`. -/
def cls (L : Launch) (g : Nat) : Cnt → Event → Bool
  | .arrive o, e => match e.kind with | .arrive m _ _ _ _ => decide (m = bl L g o) | _ => false
  | .acquire o, e => match e.kind with | .wait m _ true _ _ => decide (m = bl L g o) | _ => false
  | .bar2, e => match e.kind with | .bar i _ _ => decide (i = 2) | _ => false
  | .nb, e => match e.kind with | .bar i _ _ => decide (i = (nbW L g).toNat) | _ => false
  | .sb, e => match e.kind with
    | .bar i _ _ => decide (i = if stg L g then 12 else 11)
    | _ => false
  | .tcld, e => match e.kind with | .tc (.ld ..) => true | _ => false
  | .tcst, e => match e.kind with | .tc (.st ..) => true | _ => false
  | .sst, e => match e.kind with | .wr .. => true | _ => false
  | .shfl, e => match e.kind with | .shfl .. => true | _ => false
  | .vote, e => match e.kind with | .vote .. => true | _ => false
  | .won pc, e => match e.kind with
    | .elect _ _ ld => decide (e.pc = pc) && decide (ld = laneOf L g)
    | _ => false

/-- The softmax machine with its ledger. -/
abbrev MC (p : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  (codeD p L g).counted (cls L g)

variable {p : Params} {L : Launch} {g : Nat}

/-- **The softmax warps' ledger**: along a run of the counted machine from a state with counts
`n0`, each count grows by the number of the run's events of its class. -/
theorem ledger {d0 : D} {n0 : Cnt → Nat} {es : List Event} {dn : (MC p L g).D}
    (h : (MC p L g).toMachine.after (some (d0, n0)) es = some (some dn)) (c : Cnt) :
    dn.2 c = n0 c + es.countP (cls L g c) :=
  Frame.counted_after h c

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax

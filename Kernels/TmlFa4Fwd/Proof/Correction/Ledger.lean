-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Base
public import Lemmas.Flow.Counted
import Lemmas.Kernel.Counted

@[expose] public section

/-! # The correction warps' ledger

The correction machine with a ghost count per event class (`Code.counted`, lane L's ghost
ledger): the arrivals at the barrier at each shared offset, the successful polls of each such
barrier, the arrivals at CTA barrier 2 and at the lane's two named barriers with its softmax
warp, and the stores (one per element). Along a run from its first state each count is the
number of the run's events of its class (`ledger`), by construction. The closed forms of the
counts at each state are the count conjuncts of the role's reference invariant (`Ref.lean`).

A class names a barrier by its shared offset `o` (the barrier `bl L g o` of the lane's CTA): every
barrier the role signals or polls is one of these. The stores are not split by state space: the
shape table names a store's kind but not its address. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the ledger. -/
inductive Cnt where
  /-- mbarrier arrivals at the barrier at shared offset `o`. -/
  | arrive (o : Nat)
  /-- Successful polls of the barrier at shared offset `o`. -/
  | acquire (o : Nat)
  /-- Arrivals at CTA barrier 2 (`bar.sync`, `bar.arrive`). -/
  | bar2
  /-- Arrivals at the lane's named barrier `k` with its softmax warp (`%r565`, `%r566`). -/
  | nb (k : Fin 2)
  /-- Stores, one per element. -/
  | st
  deriving DecidableEq

/-- The lane's named barrier `k` (`%r565 = (warp & 3) + 3`, `%r566 = (warp & 3) + 7`). -/
abbrev nbOf (L : Launch) (g : Nat) (k : Fin 2) : BitVec 64 := if k = 0 then nb0W L g else nb1W L g

/-- The classes of an event of lane `g`. -/
def cls (L : Launch) (g : Nat) : Cnt → Event → Bool
  | .arrive o, e => match e.kind with | .arrive m _ _ _ _ => decide (m = bl L g o) | _ => false
  | .acquire o, e => match e.kind with | .wait m _ true _ _ => decide (m = bl L g o) | _ => false
  | .bar2, e => match e.kind with | .bar i _ _ => decide (i = 2) | _ => false
  | .nb k, e => match e.kind with | .bar i _ _ => decide (i = (nbOf L g k).toNat) | _ => false
  | .st, e => match e.kind with | .wr _ _ => true | _ => false

/-- The correction machine with its ledger. -/
abbrev MC (p : Params) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  (code p L g).counted (cls L g)

variable {p : Params} {L : Launch} {g : Nat}

/-- **The correction warps' ledger**: along a run of the counted machine from a state with
counts `n0`, each count grows by the number of the run's events of its class. -/
theorem ledger {d0 : D} {n0 : Cnt → Nat} {es : List Event} {dn : (MC p L g).D}
    (h : (MC p L g).toMachine.after (some (d0, n0)) es = some (some dn)) (c : Cnt) :
    dn.2 c = n0 c + es.countP (cls L g c) :=
  Frame.counted_after h c

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Loader.Machine
public import Lemmas.Kernel.Counted

@[expose] public section

/-! # The loader warps' ledger

The loader's machine with a ghost count per event class (`Code.counted`, lane L's ghost ledger):
the successful polls of each barrier, the mbarrier arrivals (the expect-tx arrivals of the Q and
Bias groups) and the asynchronous-copy arrivals (`cp.async.mbarrier.arrive.noinc`, one per
packet) of each barrier, the linear and tensor copies the lane issues, its `cp.async` commits,
and the elections it wins at each program counter (warp 14's arrivals and tensor copies are
those of the groups whose election it wins), and its local stores at each offset (the page
and pointer rounds' words, which the pointer rounds and the packets load back). Along a run
from a state each count is the number
of the run's events of its class (`ledger`), by construction. The closed forms of the counts at
each site are conjuncts of the role's reference invariant (`Ref.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The event classes of the ledger. -/
inductive Cnt where
  /-- Successful polls of a barrier. -/
  | acquire (l : Loc)
  /-- mbarrier arrivals on a barrier (with or without expected transaction bytes). -/
  | arrive (l : Loc)
  /-- Asynchronous-copy arrivals on a barrier (`cp.async.mbarrier.arrive`). -/
  | asyncArrive (l : Loc)
  /-- Issued copies (`cp.async` and the tensor copies, `tensorIssue`). -/
  | copy
  /-- `cp.async` commits. -/
  | commit
  /-- Elections at program counter `pc` that the lane wins. -/
  | won (pc : Nat)
  /-- The lane's stores to its local memory at offset `o` (`L.localBase + o`). -/
  | lst (o : Nat)

/-- The classes of an event of lane `g`. -/
def cls (L : Launch) (g : Nat) : Cnt → Event → Bool
  | .acquire l, e => match e.kind with | .wait m _ true _ _ => decide (m = l) | _ => false
  | .arrive l, e => match e.kind with | .arrive m _ _ _ _ => decide (m = l) | _ => false
  | .asyncArrive l, e => match e.kind with | .asyncArrive m _ => decide (m = l) | _ => false
  | .copy, e => match e.kind with | .copy _ | .tensorIssue _ _ => true | _ => false
  | .commit, e => match e.kind with | .asyncCommit => true | _ => false
  | .won pc, e => match e.kind with
    | .elect _ _ ld => decide (e.pc = pc) && decide (ld = laneOf L g)
    | _ => false
  | .lst o, e => match e.kind with
    | .wr a _ => decide (a.loc = ⟨.local, g, L.localBase + o⟩)
    | _ => false

/-- The loader's machine with its ledger. -/
abbrev MC (p : Params) (L : Launch) (g w : Nat) (ent : Nat → Value) :
    Flow.Code kernel Assumptions.all L g :=
  (code p L g w ent).counted (cls L g)

variable {p : Params} {L : Launch} {g w : Nat} {ent : Nat → Value}

/-- **The loader's ledger**: along a run of the counted machine from a state with counts `n0`,
each count grows by the number of the run's events of its class. -/
theorem ledger {d0 : D} {n0 : Cnt → Nat} {es : List Event} {dn : (MC p L g w ent).D}
    (h : (MC p L g w ent).toMachine.after (some (d0, n0)) es = some (some dn)) (c : Cnt) :
    dn.2 c = n0 c + es.countP (cls L g c) :=
  Frame.counted_after h c

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Loader

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Control
public import Kernels.TmlFa4Fwd.Proof.Correction.Ledger
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Kernels.TmlFa4Fwd.Proof.Loader.Code
public import Kernels.TmlFa4Fwd.Proof.Loader.Ledger
public import Kernels.TmlFa4Fwd.Proof.Mma.Cnt
public import Kernels.TmlFa4Fwd.Proof.Mma.Code
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
public import Kernels.TmlFa4Fwd.Proof.Softmax.Ledger
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Lemmas.Flow.Counted
public import Lemmas.Flow.Glue
public import Lemmas.Flow.Polls
import Tactics.KernelRfl

@[expose] public section

/-! # The roles of tml-fa4 and the thread machine glued from them

Every thread runs the startup (`Proof/Startup`) and then the role its warp index selects. This
file declares the roles against the code and glues their fragments into one machine per thread
(`thread`), so the layers above use one frame, `Frame.stateAt thread`, for every thread.

**Roles as data** (`Common/Sites/`). Each fragment has a region of the code (half-open intervals)
and the pcs where control may leave it (`Decl`). `closed` checks, by evaluation of the decoded
program, that every
instruction of a region other than its exits continues inside it, and `sites` lists the region's
event instructions, which are the machine's sites (`Startup.site_mem`). A role region contains the
dispatch tests that follow its code (the compiled dispatch is a sequence of `if`s, so a finished
role walks the remaining tests to the common return at pc 9205); the first instructions of the
roles those tests could reach are its declared exits, which the role's own facts on the warp index
exclude.

**Glue and ledger.** The role index is `Role`: a migrated role is its own constructor, a role
not yet migrated is `stub r`, whose fragment stops at its first event (`stop`). The startup's exit
`enter r` enters role `r` when the startup's recorded words are the reference ones the role's
first state relies on (`Gate`: the shared base and the warp index), else the stub of `r`. That
the gate holds on every thread is the startup's reference invariant, so no followed thread
reaches a stub of a migrated role; the startup itself follows every value (plan rule M1). The
thread machine counts the events of each class `Cls` (`Code.counted`); a role's reference
invariant states closed forms of the counts.

**Interface for other lanes.** A lane migrating role `r` adds a constructor to `Role`, its case
to `frag` and `exit` (with its gate), and a hand-off lemma `handoff_r` in `Common/Sound.lean`:
a concrete state of the startup's state `enter r` whose words pass the gate is a concrete state
of the role's first state. Nothing else in this file or in the startup changes. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The glue -/

/-- A fragment that stops at its first event, at `pc`: a role not yet migrated. -/
@[reducible] def stop (L : Launch) (g pc : Nat) : Flow.Code kernel Assumptions.all L g where
  D := Unit
  init := ()
  pc := fun _ => pc
  facts := fun _ => []
  inv := fun _ => True
  next := fun _ _ => some none

/-- The roles of the glue: the migrated ones, and the stub of every entry. -/
inductive Role where
  | epilogue
  | mma
  | correction
  /-- The loader warps: warp 15 for `true`, warp 14 for `false` (`Loader.wOf`). -/
  | loader (b : Bool)
  | stub (r : Startup.Entry)
  /-- The softmax warps (0 to 7), on the data machine (`SmWarp.codeT`). -/
  | softmax
  deriving DecidableEq

/-- The fragment of each role. -/
@[reducible] def fragD (p : Params) (L : Launch) (g : Nat) :
    Role → Flow.Code kernel Assumptions.all L g
  | .mma => Mma.M p L g
  | .epilogue => Epilogue.M p L g
  | .correction => Correction.code p L g
  | .loader b => Loader.F p L g b
  | .stub r => stop L g r.pc
  | .softmax => SmWarp.codeT p L g

/-- Protocol fragments retain scheduler and loop control across arbitrary data reads. -/
@[reducible] def frag (p : Params) (L : Launch) (g : Nat) :
    Role → Flow.Code kernel Assumptions.all L g
  | .correction => Correction.Control.code p L g
  | .softmax => SmWarp.control p L g
  | .mma => Mma.M p L g
  | .epilogue => Epilogue.M p L g
  | .loader b => Loader.F p L g b
  | .stub r => stop L g r.pc

/-- The startup's words the roles rely on: the shared base and, per role, the warp index (the
correction warps' first state holds the thread's own warp index, which feeds their named
barriers). -/
def Gate (L : Launch) (g : Nat) : Startup.Entry → Startup.D → Bool
  | .mma, d => d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 12
  | .epilogue, d => d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 13
  | .correction, d =>
      d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 (g % L.block / 32)
  | .loader, d => d.x1 == BitVec.ofNat 64 L.sharedBase &&
      (d.x3 == BitVec.ofNat 64 14 || d.x3 == BitVec.ofNat 64 15)
  | .softmax, d =>
      d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 (g % L.block / 32) &&
        decide (g % L.block / 32 < 8)
  | _, _ => false

/-- The role an entry enters when its gate holds; the loader's fragment is chosen by the warp
word the dispatch compared. -/
def roleOf (d : Startup.D) : Startup.Entry → Role
  | .mma => .mma
  | .epilogue => .epilogue
  | .correction => .correction
  | .loader => .loader (d.x3 == BitVec.ofNat 64 15)
  | .softmax => .softmax
  | r => .stub r

/-- The startup's exits: the state `enter r` enters role `r` when its gate holds. -/
def exit (L : Launch) (g : Nat) (d : Startup.D) : Option Role :=
  match d.site with
  | .enter r => some (if Gate L g r d then roleOf d r else .stub r)
  | _ => none

/-- The startup, then the role of the thread's warp. -/
@[reducible] def glued (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g :=
  Code.glue (Startup.code p L g) (frag p L g) (exit L g)

/-! ### The ghost ledger -/

deriving instance DecidableEq for Loader.Cnt

/-- The classes of events the thread machine counts: warp shuffles and full-mask ballots (the
instances of the warp collectives), all events (the position in the trace), and the output
warp's tensor stores, bulk-group commits and read waits, arrivals, and per stage the successful
polls of its ready barrier and the arrivals on its free barrier (the library's `okPoll` and
`arrivesOn`, the counts the unit hand-off is stated in), the MMA warp's ledger classes (`Mma.Cnt`),
the correction warps' ledger classes (`Correction.Cnt`), the loader warps' ledger classes
(`Loader.Cnt`), the softmax warps' classes whose counts are closed forms in the places
(`Softmax.Cnt.pointed`, counted on warps 0 to 7 only), and undefined-behaviour events (a
reference invariant may be guarded by none so far). -/
inductive Cls where
  | shfl
  | vote
  | all
  | store
  | commit
  | wait
  | arrive
  | poll (st : Fin 2)
  | freed (st : Fin 2)
  | mma (c : Mma.Cnt)
  | corr (c : Correction.Cnt)
  | load (c : Loader.Cnt)
  | soft (c : Softmax.Cnt)
  | ub
  deriving DecidableEq

/-- The events of each class. -/
def cls (L : Launch) (g : Nat) : Cls → Event → Bool
  | .shfl => Execution.isShfl
  | .vote => isFullVote
  | .all => fun _ => true
  | .store => Epilogue.isStore
  | .commit => Epilogue.isCommit
  | .wait => Epilogue.isWait
  | .arrive => Epilogue.isArrive
  | .poll st => Flow.okPoll (Epilogue.readyLoc L g st)
  | .freed st => Flow.arrivesOn (Epilogue.freeLoc L g st)
  | .mma c => Mma.cls L g c
  | .corr c => Correction.cls L g c
  | .load c => Loader.cls L g c
  | .soft c => fun e => Softmax.cls L g c e && c.pointed && decide (g % L.block / 32 < 8)
  | .ub => fun e => match e.kind with | .ub _ => true | _ => false

/-- **The thread machine**: the glued machine with its ghost ledger. Its state before a thread's
`k`-th event carries the counts of each class among the thread's first `k` events
(`Frame.count_eq`). -/
@[reducible] def thread (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g :=
  (glued p L g).counted (cls L g)

/-- The value layer tracks full data up to the first unsuccessful read. -/
@[reducible] def gluedD (p : Params) (L : Launch) (g : Nat) :=
  Code.glue (Startup.code p L g) (fragD p L g) (exit L g)

@[reducible] def threadD (p : Params) (L : Launch) (g : Nat) :=
  (gluedD p L g).counted (cls L g)

end
end PTX.Kernels.TmlFa4Fwd.Proof

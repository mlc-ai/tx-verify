-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

noncomputable section

namespace Output
open Epilogue

/-- The output warp's two writeback groups and the final drain. -/
inductive Phase where
  | selecting
  | waiting (stage : Fin 2)
  | issuing (stage : Fin 2) (subbox : Fin 4)
  | committing (stage : Fin 2)
  | waitingRead (stage : Fin 2)
  | releasing (stage : Fin 2)
  | draining
  | exited
  deriving DecidableEq

structure D where
  phase : Phase := .selecting
  issued : Nat := 0
  committed : Nat := 0
  released : Nat := 0

def initial : D := {}

def atWriteback (site : Nat) : Option WritebackSite :=
  writebackSites.find? (fun s => writebackPc (some s) == site)

def phaseOfSite : WritebackSite → Phase
  | .ready stage => .waiting stage
  | .store stage box => .issuing stage box
  | .commit stage => .committing stage
  | .readWait stage => .waitingRead stage
  | .release stage => .releasing stage

/-- A successful event advances the selected group, while a failed ready observation retries. -/
def advance (d : D) (e : Event) : D :=
  match atWriteback e.pc with
  | some s =>
    let phase := (writebackSuccessor s (writebackSucceeded e.kind)).map phaseOfSite
    { phase := phase.getD .draining
      issued := d.issued + (match s with | .store .. => 1 | _ => 0)
      committed := d.committed + (match s with | .commit .. => 1 | _ => 0)
      released := d.released + (match s with | .release .. => 1 | _ => 0) }
  | none =>
    match e.kind with
    | .exit => { d with phase := .exited }
    | _ => d

abbrev machine (l : Launch) (g : Nat) := observationMachine l g initial advance

theorem sound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    (machine l g).Sound :=
  observationSound hp g initial advance

end Output
end
end PTX.Kernels.TmlFa4Fwd.Thread

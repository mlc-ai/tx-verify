-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
public import Kernels.TmlFa4Fwd.Proof.PrologueGenerationZero

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

noncomputable section

namespace Startup

/-- Abstract stages of the launch setup, common to every lane. -/
inductive Phase where
  | broadcasts
  | initialization
  | publishing
  | rendezvous
  | dispatched
  deriving DecidableEq

structure D where
  phase : Phase := .broadcasts
  broadcasts : Nat := 0
  initializedObjects : Nat := 0

def initial : D := {}

def advance (d : D) (e : Event) : D :=
  match e.kind with
  | .bar 0 none .sync => { d with phase := .rendezvous }
  | .setMaxReg .. => { d with phase := .dispatched }
  | _ => if d.phase = .dispatched then d else
    match e.kind with
    | .shfl .. =>
      if d.phase = .broadcasts then
        { d with
          broadcasts := d.broadcasts + 1
          phase := if d.broadcasts = 2 then .initialization else .broadcasts }
      else d
    | .mbInit .. => { d with initializedObjects := d.initializedObjects + 1 }
    | .fenceMbarInit => { d with phase := .publishing }
    | _ => d

abbrev machine (l : Launch) (g : Nat) := observationMachine l g initial advance

theorem sound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    (machine l g).Sound :=
  observationSound hp g initial advance

/-- The explicit full-CTA publishing rendezvous. -/
def Rendezvous (X : Execution) (i : EvId) : Prop :=
  ∃ e, X.get i = some e ∧ e.kind = .bar 0 none .sync

/-- At the last rendezvous event the object records may extend without adding trace events. -/
theorem releaseRendezvous {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads)
    (hLast : Rendezvous X (g, (X.tr g).length - 1)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
  obtain ⟨⟨site, _⟩, he, rfl⟩ := hLast
  have hs := ((actualNamedBarrier hp hMax.1 he).2.2.2.2.1).mp rfl
  subst site
  exact Prologue.commonBarrierCanReleaseGenerationZero hp hMax hg he

end Startup
end
end PTX.Kernels.TmlFa4Fwd.Thread

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Epilogue
public import Kernels.TmlFa4Fwd.Proof.Thread.Prologue
public import Kernels.TmlFa4Fwd.Proof.Thread.Loader
public import Kernels.TmlFa4Fwd.Proof.Thread.Mma
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
public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

noncomputable section

/-- Roles after the common rendezvous. Both loader warps use the same machine. -/
inductive Role where
  | softmax
  | correction
  | mma
  | output
  | loader
  deriving DecidableEq

def roleOf (l : Launch) (g : Nat) : Role :=
  let w := Prologue.warpIndex l g
  if w < 8 then .softmax else if w < 12 then .correction
  else if w = 12 then .mma else if w = 13 then .output else .loader

def roleMachine (l : Launch) (g : Nat) : Role → Machine kernel Assumptions.all l g
  | .softmax => Scores.machine l g
  | .correction => correctionMachine l g
  | .mma => Mma.machine l g
  | .output => Output.machine l g
  | .loader => Loader.machine l g

/-- Each lane is interpreted by the machine for its statically assigned warp role. -/
def machine (l : Launch) (g : Nat) : Machine kernel Assumptions.all l g :=
  roleMachine l g (roleOf l g)

theorem sound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    (machine l g).Sound := by
  unfold machine
  cases roleOf l g
  · exact Scores.sound hp g
  · exact correctionSound hp g
  · exact Mma.sound hp g
  · exact Output.sound hp g
  · exact Loader.sound hp g

/-- The common startup trace and the assigned role's trace both have sound machines. -/
theorem traces {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) :
    (Startup.machine l g).Trace (Startup.machine l g).init (X.tr g) ∧
      (machine l g).Trace (machine l g).init (X.tr g) :=
  ⟨(Startup.sound hp g).produces (hX.thr g hg), (sound hp g).produces (hX.thr g hg)⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread

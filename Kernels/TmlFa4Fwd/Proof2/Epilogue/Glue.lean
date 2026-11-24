-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Common.Frame
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Shape
public import Lemmas.Flow.Glue
public import Lemmas.Flow.Counted
public import Lemmas.Kernel.Counted
public import Kernels.TmlFa4Fwd.Proof2.Startup.Shape

@[expose] public section

/-! # The output warp inside the thread machine

A lane of warp 13 runs the startup fragment and then the output warp's fragment of the glued
thread machine (`Proof2.thread`). A role state of the public frame `Frame.stateAt (thread p L)`
is `inj d n`, the role's state with the ghost counts; an event at it has its site's shape
(`fired`). The startup's facts and the counts are the thread frame's (`Common/Frame.lean`). That a
lane of warp 13 passes the startup into the role is part of its reference invariant
(`Warp.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The output warp's state `d` with the counts `n` as a state of the thread machine. -/
abbrev inj (p : Params) (L : Launch) (g : Nat) (d : D) (n : Cls → Nat) : (thread p L g).D :=
  (.inr ⟨.epilogue, d⟩, n)

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **An event at a state of the output warp has its site's shape**, and the role's machine
fires it from that state. -/
theorem fired (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {d : D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (inj p L g d n))) :
    Ev p L g d e ∧ ∃ o, (M p L g).toMachine.Fired (some d) e o := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf⟩ := (Frame.trace (fun g hg => thread_sound hp hg) hX hg).fired_at he hσ
  have hf' : (M p L g).toMachine.Fired (some d) e o := hf
  exact ⟨(Code.Shape.fired (shape hp) (stepAt hp hg) hf').1, o, hf'⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Core.Source.Instr
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.FmaRun
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemWait
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Correction.Export.Tmem

@[expose] public section

/-! # A correction lane's load is followed at once by its `wait::ld`

A `tcgen05.ld` event of a correction lane is fired at a rescale load (`rld`, then the implicit
wait `rldw` at sub-step 1: `rldw_wait`) or a final load (`fld`, then `fwl`, whose shape is the
`wait::ld`); an implicit-wait state fires no load (its template at sub-step 1 is the wait, and
at sub-step 0 the machine stops, which a followed lane never does). So the lane's next event
after a load is a `wait::ld` (`corr_ld_wait`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **The event after a correction lane's load is a `wait::ld`.** -/
theorem corr_ld_wait (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {f pc a : Nat}
    {vals : List Value} {sh : TcShape} {d : Correction.Control.D} {n : Cls → Nat} {e1 : Event}
    (he : X.get (g, f) = some ⟨pc, .tc (.ld a vals sh)⟩)
    (hσ : Frame.stateAt (thread p L) X g f = some (some (CorrWarp.cinj p L g d n)))
    (he1 : X.get (g, f + 1) = some e1) (hu : ∀ f, e1.kind ≠ .ub f) : e1.kind = .tc .waitLd := by
  have hJ := (goodR hp hX hFw (Frame.lt_of_get hX he) f).2 _ hσ
  obtain ⟨hw,hw1,-⟩ := JR.correction hJ (Prologue.warpIndex_lt hp g)
  obtain ⟨pc1,h⟩ := Correction.corr_ld_wait' hp hX hFw (by omega) (by omega) ⟨pc,he⟩
    (Nat.lt_succ_self f) he1 hu
  rw [he1] at h
  exact congrArg Event.kind (Option.some.inj h)

end
end PTX.Kernels.TmlFa4Fwd.Proof

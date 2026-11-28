-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.Export.DataNext
import Kernels.InklingRelDecode.Proof.Lib.NextPoll
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Sched

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g pc q : Nat}
  {l : Loc} {sc : MbarScope}

private theorem wait_steps (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hu : ¬ HasUb X) (hF : Follow Q L X) (hg : Frame.Pending L X g) (hr : Step.Released L X g)
    (hpc : 20 ≤ pc) (he : NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hb : WaitBlk (schedule Q L) X g l q) : Steps (schedule Q L) m X (.thread g) := by
  obtain ⟨hne, htime⟩ := poll_floor hp hF hpc he
  exact mbar_at_stepsQ Lib.assumptions_step.wfQuiet hu hm hg hr hne
    (mbarAt_of (Lib.next_poll_blocked he hb)) (by omega) htime

public theorem loader_wait_step (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hu : ¬ HasUb X) (hF : Follow Q L X) (hg : Frame.Pending L X g) (hr : Step.Released L X g)
    (he : NextEv L kernel Assumptions.all m X g ⟨2374, .wait l q false true sc⟩)
    (hb : WaitBlk (schedule Q L) X g l q) : Steps (schedule Q L) m X (.thread g) :=
  wait_steps hp hm hu hF hg hr (by decide) he hb

public theorem mma_wait_step (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hu : ¬ HasUb X) (hF : Follow Q L X) (hg : Frame.Pending L X g) (hr : Step.Released L X g)
    (hpc : pc = 2462 ∨ pc = 2510)
    (he : NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q false true sc⟩)
    (hb : WaitBlk (schedule Q L) X g l q) : Steps (schedule Q L) m X (.thread g) :=
  wait_steps hp hm hu hF hg hr (by omega) he hb

public theorem softmax_wait_step (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hu : ¬ HasUb X) (hf : Follow Q L X) (hg : Frame.Pending L X g) (hr : Step.Released L X g)
    (hpc : pc=1257 ∨ pc=2239) (he : NextEv L kernel Assumptions.all m X g
      ⟨pc,.wait l q false true sc⟩) (hb : WaitBlk (schedule Q L) X g l q) :
    Steps (schedule Q L) m X (.thread g) :=
  wait_steps hp hm hu hf hg hr (by omega) he hb

public theorem epilogue_wait_step (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hu : ¬ HasUb X) (hf : Follow Q L X) (hg : Frame.Pending L X g) (hr : Step.Released L X g)
    (he : NextEv L kernel Assumptions.all m X g ⟨2565,.wait l q false true sc⟩)
    (hb : WaitBlk (schedule Q L) X g l q) : Steps (schedule Q L) m X (.thread g) :=
  wait_steps hp hm hu hf hg hr (by decide) he hb

public theorem prologue_wait_step (reg : 27≤pc ∧ pc<574)
    (he : NextEv L kernel Assumptions.all m X g ⟨pc,.wait l q false true sc⟩) :
    Steps (schedule Q L) m X (.thread g) :=
  (prologue_next he reg.1 reg.2 l q false true sc rfl).elim

end PTX.Kernels.InklingRelDecode.Proof.Export

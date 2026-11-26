-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
public import Lemmas.Quiet.Progress.ReleasedU
public import Lemmas.Quiet.Progress.Other
public import Lemmas.Quiet.Progress.IssueU
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RestAt

@[expose] public section

/-! # A released lane at an ordinary instruction steps

`Descent.released_stepsUQ` for the kernel's thread machines, stated by the next event only: a
pending released lane whose next event is at an instruction outside `Descent.NextKind.Rest`
(not an mbarrier poll, a warp collective, a register request, an allocation or another
instruction without a library step) performs it (`ordinary_steps`), given the execution facts
(`Descent.NextEnvQ`, `Top/Prog/NextEnv.lean`) and that an exit's selected stores have finished
reading (`hexit`). The state behind the event is taken privately (`next_state`); a lane without
events is at the startup's first event, a warp collective, so it is never outside `Rest`; after
lane 0's allocation request the next event is at the allocation (`alloc_next_pc`), not a store. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- **A next event is at an instruction that is no local one**: the machine's state behind it is
at a site. -/
theorem next_site (hp : Pre P L m) (hFw : Follow P L X)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ ins, kernel.code[e.pc]? = some ins ∧ ins.op.isLocal = false := by
  obtain ⟨σ, -, -, hi, -, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨ins, hc, hl, -⟩ := ((thread_sound hp).steps σ).site hi
  exact ⟨ins, hpc ▸ hc, hl⟩

/-- **A released pending lane whose next event is at an instruction outside `Rest` steps.** -/
theorem ordinary_steps (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins → (Descent.opKind ins.op).Rest = false)
    (hexit : ∀ ins, kernel.code[e.pc]? = some ins → Descent.opKind ins.op = .exit →
      TensorStore.Drained drainSel X g) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, -, -, -, hpc⟩ := next_state hp hFw hn hub
  rw [hpc] at hk hexit
  exact ordinary_at hp hc hFw hpd hrel hσ hk hexit

/-- **A released pending lane whose next event is a non-coherent load, a `tcgen05` fence, copy
or shift, a Tensor Memory store or a store wait steps.** -/
theorem other_steps (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins →
      (Descent.otherOp ins.op || Sched.tcStoreOp ins.op) = true) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, -, -, -, hpc⟩ := next_state hp hFw hn hub
  rw [hpc] at hk
  exact other_at hp hc hpd hrel hσ hk

/-- **A released pending lane whose next event is a register request steps**: it is the lane's
first. -/
theorem reg_quiet_steps (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins → Sched.regOp ins.op = true) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, hJ, hi, -, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨ins, hins⟩ : ∃ ins, kernel.code[e.pc]? = some ins := by
    obtain ⟨ins, h, -⟩ := next_site hp hFw hn hub
    exact ⟨ins, h⟩
  rw [hpc] at hk hins
  exact reg_at hp hc hFw hpd hrel hσ (J := hJ) (hi := hi) hk ⟨ins, hins⟩

/-- **A released pending lane whose next event is the allocation steps**, when every recorded
allocation is at column 0. -/
theorem alloc_quiet_steps (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins → Sched.allocOp ins.op = true)
    (hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, -, -, -, hpc⟩ := next_state hp hFw hn hub
  rw [hpc] at hk
  exact alloc_at hp hc hpd hrel hσ hk hzero

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Kind

@[expose] public section

/-! # E5a: a released loader lane at its other states

The progress class this file owns, proved (`Prog.loaderOther`): a loader site that is no wait and no
warp collective, with its instruction in `Rest`, is the register request or an operation of a
packet's `cp.async` copies (`Loader/Export/Kind.lean`), which the lane makes (`Prog/Issue.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- A loader state other than a wait, at an instruction in `Rest`. -/
def Prog.LoaderOther.At (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  (∃ b d n, σ = (.inr ⟨.loader b, d⟩, n) ∧ ¬ Loader.isWait d.site) ∧ RestAt p L g σ ∧
    ¬ CollAt p L g σ

/-- **A released loader lane at any state other than a wait steps.** -/
theorem Prog.loaderOther (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m (Prog.LoaderOther.At p L) := by
  rintro X hmax g _ hpd hrel hσ ⟨⟨b, d, n, rfl, hw⟩, hr, hc⟩
  exact site_rel hp hs hmax hpd hrel hσ hr hc (ld_kind hw) fun he => by
    simpa [IsEntry] using he

end PTX.Kernels.TmlFa4Fwd.Proof.Top

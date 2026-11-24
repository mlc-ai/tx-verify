-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Kind

@[expose] public section

/-! # A released lane of warp 13 away from its ready polls

The progress class this file owns, proved (`Prog.epilogue`): a site of the output warp that is no
ready poll and no warp collective, with its instruction in `Rest`, is the register request
(`Epilogue/Export/Kind.lean`), which the lane makes (`Prog/Issue.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- An output state other than a ready poll, at an instruction in `Rest`. -/
def Prog.Epilogue.At (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  (∃ d n, σ = (.inr ⟨.epilogue, d⟩, n) ∧ ∀ st, d.site ≠ .ready st) ∧ RestAt p L g σ ∧
    ¬ CollAt p L g σ

/-- **A released lane of warp 13 at a state other than a ready poll steps.** -/
theorem Prog.epilogue (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m (Prog.Epilogue.At p L) := by
  rintro X hmax g _ hpd hrel hσ ⟨⟨d, n, rfl, hw⟩, hr, hc⟩
  exact site_rel hp hs hmax hpd hrel hσ hr hc (out_kind hw) fun he => by
    simpa [IsEntry] using he

end PTX.Kernels.TmlFa4Fwd.Proof.Top

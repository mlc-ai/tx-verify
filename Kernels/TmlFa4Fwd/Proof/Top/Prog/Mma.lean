-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Kind

import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section

/-! # A released lane of warp 12 away from its pipeline polls

The progress class this file owns, proved (`Prog.mma`): a site of the MMA warp that is no poll and
no warp collective, with its instruction in `Rest`, is the register request or the allocation with
its address store (`Mma/Export/Kind.lean`), which the lane makes (`Prog/Issue.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- An MMA state other than a pipeline poll, at an instruction in `Rest`. -/
def Prog.Mma.At (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  (∃ d n, σ = (.inr ⟨.mma, d⟩, n) ∧
    ∀ d', d = .inr ⟨(), d'⟩ → Progress.isPoll d'.site = false) ∧ RestAt p L g σ ∧
    ¬ CollAt p L g σ

/-- **A released lane of warp 12 at a state other than a pipeline poll steps.** -/
theorem Prog.mma (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    RelSteps p L m (Prog.Mma.At p L) := by
  rintro X hmax g _ hpd hrel hσ ⟨⟨d, n, rfl, hw⟩, hr, hc⟩
  rcases d with s | ⟨⟨⟩, d⟩
  · obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 (Sched.safe_noUb (hs.2 X hmax.1)) hpd
    obtain ⟨t1, ins, -, -, hinv, -, -⟩ :=
      strict_end_at hp hpd.1 hrun hσ rfl
    have hne : s ≠ .enter := by
      rintro rfl
      have hx : Mma.Start.exit .enter = none := hinv.2
      cases hx
    exact site_rel hp hs hmax hpd hrel hσ hr hc (mma_start_kind hne) fun he => by
      simpa [IsEntry] using he
  · exact site_rel hp hs hmax hpd hrel hσ hr hc (mma_kind (hw d rfl)) fun he => by cases he

end PTX.Kernels.TmlFa4Fwd.Proof.Top

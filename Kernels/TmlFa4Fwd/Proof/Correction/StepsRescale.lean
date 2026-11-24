-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW0NumLo
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW0NumHi
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW0OneLo
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW0OneHi
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW1NumLo
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW1NumHi
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW1OneLo
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescaleW1OneHi
import Kernels.TmlFa4Fwd.Proof.Correction.Loads
import Lemmas.Flow.Step.TcSteps
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_rld (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : (∃ st c, d.site = .rld st c) ∨ ∃ st c, d.site = .rst st c) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s except [.rld _ _ => (by corr_rld), .rst _ _ => (by corr_tst)]

theorem stepAt_rldw (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 1)
    (hs : ∃ st c, d.site = .rldw st c) :
    (code p L g).StepAt d := by
  obtain ⟨st, c, hs⟩ := hs
  obtain ⟨s, v, k⟩ := d
  cases hk
  fin_cases st
  · cases hv : v.s0 with
    | num x =>
      rcases Nat.lt_or_ge c.val 4 with hc | hc
      · exact stepAt_rldwANumLo hp hv s ⟨c, hc, hs⟩
      · exact stepAt_rldwANumHi hp hv s ⟨c, hc, hs⟩
    | one =>
      rcases Nat.lt_or_ge c.val 4 with hc | hc
      · exact stepAt_rldwAOneLo hp hv s ⟨c, hc, hs⟩
      · exact stepAt_rldwAOneHi hp hv s ⟨c, hc, hs⟩
  · cases hv : v.s1 with
    | num x =>
      rcases Nat.lt_or_ge c.val 4 with hc | hc
      · exact stepAt_rldwBNumLo hp hv s ⟨c, hc, hs⟩
      · exact stepAt_rldwBNumHi hp hv s ⟨c, hc, hs⟩
    | one =>
      rcases Nat.lt_or_ge c.val 4 with hc | hc
      · exact stepAt_rldwBOneLo hp hv s ⟨c, hc, hs⟩
      · exact stepAt_rldwBOneHi hp hv s ⟨c, hc, hs⟩

/-- The implicit wait's site at sub-step 0 is not a state the machine reaches; it stops. -/
theorem stepAt_rldw0 (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : ∃ st c, d.site = .rldw st c) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction

-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepAll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataState
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictGlue
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import Lemmas.Kernel.StrictSite

@[expose] public section

/-! # The strict chain of a lane of warpgroup 0

`w0_prev`: the step of the data thread machine before a state of a lane of warps 0 to 3 is strict
for its event (`Code.StepFor`): the startup's (`startup_steps`), or warpgroup 0's data machine's
(`dataStepFor_wg0`), whose conditions (`WinCond`, the length loads' bytes, the chain's flag) are
the hypothesis `hW` of the state. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

namespace Wg0
open Wg0.Data

/-- The side conditions of the strict step of warpgroup 0's data machine at a state and event. -/
def StepConds (L : Launch) (g : Nat) (dd : D) (ej : Event) : Prop :=
  (onChain dd.c.site = true → isStart dd.c.site = false → dd.ok = true) ∧ EvNcOk ej ∧
    WinCond L g dd ej

/-- **The step before a state of a lane of warps 0 to 3 is strict.** -/
theorem w0_prev (hp : Pre P L m) (hg : g < L.threads ∧ g / L.block < L.grid)
    {dj : (threadD P L g).D} {ej : Event}
    (hslot : (∃ b, dj.1 = .inl b) ∨ ∃ d, dj.1 = .inr ⟨.inl .wg0, d⟩)
    (hW : ∀ dd, dj.1 = .inr ⟨.inl .wg0, dd⟩ → StepConds L g dd ej) :
    (threadD P L g).StepFor dj ej := by
  rcases hslot with ⟨b, hb⟩ | ⟨dd, hdd⟩
  · obtain ⟨q, n⟩ := dj
    obtain rfl : q = .inl b := hb
    exact fun {t u} ins hat hi hc hf => (Code.counted_stepFor (Code.glue_inl_stepFor
      (fun hx => (startup_steps hp b hx).stepFor ej) threadD_handoff) n) ins hat hi hc hf
  · obtain ⟨q, n⟩ := dj
    obtain rfl : q = .inr ⟨.inl .wg0, dd⟩ := hdd
    obtain ⟨hok, hn, hw⟩ := hW dd rfl
    have hstep : (wg0DCode P L g (warpW L g)).StepFor dd ej :=
      dataStepFor_wg0 hp hg dd ej hok hn hw
    exact fun {t u} ins hat hi hc hf => (Code.counted_stepFor
      (Code.glue_inr_stepFor (i := Sum.inl Entry.wg0) hstep) n) ins hat hi hc hf

end Wg0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

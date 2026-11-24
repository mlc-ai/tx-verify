-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVMetadata
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPacket
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Flow.Code.Part010

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue

noncomputable section

theorem primingKCommitAdvanceInPrefix {l : Launch} {X : Execution}
    {g i : Nat} {s : TState} {F : List (Nat × Value)}
    (hs : At s 673 F) {ending : Option TState}
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    X.get (g, i) = some ⟨673, .asyncCommit⟩ ∧
      Run kernel Assumptions.all l g (next s) ((X.tr g).drop (i + 1)) ending := by
  have hNext : Next kernel Assumptions.all l g s s (.asyncCommit (next s)) := by
    refine ⟨.refl, ?_⟩
    rw [out_event hs.2.2.2.1 (by rw [hs.1]; exact Flow.code_673) rfl rfl]
    rfl
  obtain ⟨_, _, hEvent, ⟨rfl, hRet⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, h⟩
    cases h) hr hMore
  obtain rfl := Option.some.inj hRet
  rw [hs.1] at hEvent
  exact ⟨hEvent, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

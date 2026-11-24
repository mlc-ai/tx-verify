-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Common.View

@[expose] public section

/-! # An event of the softmax warps and the followed state it is fired from

For the role's exports only: the layers above read the exports. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The followed state of the softmax warps an event is fired from**:
the startup's, or the role's with its reference invariant. -/
theorem SmWarp.open_ev (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8)
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    (∃ s n, Frame.stateAt (thread p L) X g k = some (some (.inl s, n)) ∧ n .ub = 0 ∧
        JR p L g (.inl s, n) ∧ (thread p L g).inv (.inl s, n) ∧ Startup.Ev L g s e) ∨
      ∃ d n, Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)) ∧
        n .ub = 0 ∧ SmWarp.Ref p L (Prologue.warpIndex L g) g (SmWarp.sinj p L g d n) ∧
        (thread p L g).inv (SmWarp.sinj p L g d n) ∧ Softmax.EvS p L g d e := by
  obtain ⟨σ, n, hσ, h0, hJ, hi, hev⟩ := ev_open hp hX hFw he hub
  rcases σ with s | ⟨i, d⟩
  · exact .inl ⟨s, n, hσ, h0, hJ, hi, hev⟩
  · cases i with
    | softmax => exact .inr ⟨d, n, hσ, h0, (JR.softmax hJ).2, hi, hev⟩
    | epilogue => have := (JR.epilogue hJ).1; omega
    | mma => have := (JR.mma hJ).1; omega
    | correction => have := (JR.correction hJ (by omega)).1; omega
    | loader b => have := (JR.loader hJ).1; omega
    | stub r => exact (JR.not_stub hJ).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof

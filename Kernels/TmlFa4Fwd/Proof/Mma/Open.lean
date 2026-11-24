-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Mma.Warp
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Common.View

@[expose] public section

/-! # An event of the MMA warp and the followed state it is fired from

For the role's exports only: the layers above read the exports. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The followed state of the MMA warp an event is fired from**:
the startup's, or the role's with its reference invariant. -/
theorem Mma.open_ev (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 12)
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    (∃ s n, Frame.stateAt (thread p L) X g k = some (some (.inl s, n)) ∧ n .ub = 0 ∧
        JR p L g (.inl s, n) ∧ (thread p L g).inv (.inl s, n) ∧ Startup.Ev L g s e) ∨
      (∃ s n, Frame.stateAt (thread p L) X g k = some (some (.inr ⟨.mma, .inl s⟩, n)) ∧
        n .ub = 0 ∧ (thread p L g).inv (.inr ⟨.mma, .inl s⟩, n) ∧ Mma.PreEv e) ∨
      ∃ d n, Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)) ∧
        n .ub = 0 ∧ Mma.Ref p L g (Mma.minj p L g d n) ∧
        (thread p L g).inv (Mma.minj p L g d n) ∧ Mma.Ev p L g d e := by
  obtain ⟨σ, n, hσ, h0, hJ, hi, hev⟩ := ev_open hp hX hFw he hub
  rcases σ with s | ⟨i, d⟩
  · exact .inl ⟨s, n, hσ, h0, hJ, hi, hev⟩
  · cases i with
    | softmax => have := (JR.softmax hJ).1; omega
    | epilogue => have := (JR.epilogue hJ).1; omega
    | mma =>
      rcases d with s | ⟨⟨⟩, d⟩
      · exact .inr (.inl ⟨s, n, hσ, h0, hi, hev⟩)
      · exact .inr (.inr ⟨d, n, hσ, h0, (JR.mma hJ).2, hi, hev⟩)
    | correction => have := (JR.correction hJ (by omega)).2.1; omega
    | loader b => have := (JR.loader hJ).1; omega
    | stub r => exact (JR.not_stub hJ).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof

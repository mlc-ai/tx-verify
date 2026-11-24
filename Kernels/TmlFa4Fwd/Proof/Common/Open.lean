-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Common.Frame

@[expose] public section

/-! # The followed state an event is fired from

Every event of a thread that is not undefined behaviour is fired from a followed state, with the
lane invariant, the machine's invariant and the shape table (`ev_open`). A role's own form of it, at
the role's warps, is the role's `Open.lean`, which the role's exports use. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The followed state an event is fired from.** -/
theorem ev_open (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ σ n, Frame.stateAt (thread p L) X g k = some (some (σ, n)) ∧ n .ub = 0 ∧
      JR p L g (σ, n) ∧ (thread p L g).inv (σ, n) ∧ TEv p L g (σ, n) e := by
  obtain ⟨⟨σ, n⟩, hσ, hJ, hi, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun _ hg => thread_sound hp hg) hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) (Frame.lt_of_get hX he) he hub
  exact ⟨σ, n, hσ, ub_zero hX he hσ, hJ, hi, hev⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof

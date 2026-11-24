-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

/-- A rendezvous with an exact ID, count, and participation mode. -/
def BarrierArrival (X : Execution) (i : EvId) (id : Nat) (count : Option Nat)
    (mode : BarMode) : Prop :=
  ∃ e, X.get i = some e ∧ e.kind = .bar id count mode

theorem barrierCountAgrees {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {id : Nat} {count count' : Option Nat} {mode mode' : BarMode}
    (he : BarrierArrival X i id count mode) (hf : BarrierArrival X j id count' mode') :
    count = count' := by
  obtain ⟨⟨site, _⟩, he, rfl⟩ := he
  obtain ⟨⟨site', _⟩, hf, rfl⟩ := hf
  exact actualNamedBarrierCountAgrees hp hX he hf

end PTX.Kernels.TmlFa4Fwd.Thread

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Representative
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Bound

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Flow.Arith32
variable {p : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event} {ns nv : Nat}

private theorem measure_erase (a : Softmax.D) (ns : Nat) :
    measure (erase a).scheduler ns = measure a ns := by
  cases a with
  | mk s v k acc =>
    cases s <;> rfl

theorem measure_step {ns' : Nat} (rep : Represents p L g d d' e)
    (room : d.site = .pwend .bias → (r32 d.v.nb).toNat + 1 < 2 ^ 32)
    (hn : ns' = ns + if Execution.isShfl e then 1 else 0) :
    measure d.scheduler ns ≤ measure d'.scheduler ns' ∧
      (e.counts = true → measure d.scheduler ns < measure d'.scheduler ns') := by
  obtain ⟨a, ev, _, _, hs, hsite, hv, hk, _, hm⟩ := rep
  have effects : ev.counts = e.counts ∧ Execution.isShfl ev = Execution.isShfl e := by
    rcases hm with rfl | ⟨_, hc, hsh, _⟩
    · exact ⟨rfl,rfl⟩
    · exact ⟨hc,hsh⟩
  have h := Softmax.measure_step hs room (effects.2.symm ▸ hn)
  rw [← measure_erase a ns', effects.1] at h
  cases d' with
  | mk s v k acc =>
    cases hsite
    cases hv
    cases hk
    exact h

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control

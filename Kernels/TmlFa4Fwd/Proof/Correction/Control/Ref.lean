-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.RefDef

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

/-- The protocol reference invariant uses the ledger, round count and scheduler inputs. -/
def Ref (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  RefCounts p L g (dn.1.scheduler, dn.2)

/-- Reads and shuffles of scheduler control words have reference sources. -/
def Expect (d : D) (e : Event) : Prop :=
  match d.site with
  | .word _ | .q0 | .q1 | .uk | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ =>
    ExpectD d.scheduler e
  | _ => True

/-- Project the strict value invariant onto the protocol ledger. -/
theorem Ref.of_data {p L g d n} (h : Correction.Ref p L g (d, n)) : Ref p L g (erase d, n) := by
  obtain ⟨r, l, hr⟩ := h.counts
  exact ⟨r, l, hr.cnt, hr.st, hr.lse, hr.sub, hr.pre, hr.loop, hr.tail⟩

/-- The rescale ballot carries the condition and result, even when the value machine's scale
word is unavailable. The other shapes already depend only on scheduler control words. -/
def Ev (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .rvote _ => ∃ pred b, e.kind = .vote (2 ^ 32 - 1) pred b
  | _ => Correction.Ev p L g d.scheduler e

theorem Ev.of_data {p L g d e} (h : Correction.Ev p L g d e) : Ev p L g (erase d) e := by
  obtain ⟨s,v,k⟩ := d
  cases s with
  | rvote st => obtain ⟨b, he⟩ := h; exact ⟨_, b, he⟩
  | _ => exact h

theorem Ev.data_or_vote {p L g d e} (h : Ev p L g d e) :
    Correction.Ev p L g d.scheduler e ∨ ∃ pred b, e.kind = .vote (2 ^ 32 - 1) pred b := by
  obtain ⟨s,v,k⟩ := d
  cases s with
  | rvote st => exact .inr h
  | _ => exact .inl h

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

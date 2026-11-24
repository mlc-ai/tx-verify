-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Core.Assembly.Correctness
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

/-- A role lane ran a normal exit event. -/
def Exited (X : Execution) (g : Nat) : Prop :=
  ∃ j e, X.get (g, j) = some e ∧ e.kind = .exit

/-- An actual role exit is the last event of the lane. -/
theorem Exited.last {l : Launch} {m : Mem0} {X : Execution} {A : List Assumption}
    {g : Nat} (h : Exited X g) (hX : Consistent l Decoded.kernel A m X) (hg : g < l.threads) :
    ∃ e, (X.tr g).getLast? = some e ∧ e.kind = .exit := by
  obtain ⟨j, ⟨site, kind⟩, he, hKind⟩ := h
  change kind = .exit at hKind
  subst kind
  have hLast := Execution.exit_last hX hg he
  refine ⟨⟨site, .exit⟩, ?_, rfl⟩
  rw [List.getLast?_eq_getElem?, ← hLast, Nat.add_sub_cancel]
  exact he

/-- Complete executions of this kernel have actual exits for all launched lanes. -/
theorem exitedOfComplete {l : Launch} {m : Mem0} {X : Execution} {A : List Assumption}
    (hX : Consistent l Decoded.kernel A m X) (hDone : Complete l X) {g : Nat}
    (hg : g < l.threads) : Exited X g := by
  obtain ⟨site, h⟩ := (hDone.1 g hg).resolve_left (noCanceled hX)
  rw [List.getLast?_eq_getElem?] at h
  exact ⟨(X.tr g).length - 1, ⟨site, .exit⟩, h, rfl⟩

/-- The normal exit flag of a consistent lane matches Core's last-event witness. -/
theorem Exited.lastEvent {l : Launch} {m : Mem0} {X : Execution} {A : List Assumption}
    {g : Nat} (h : Exited X g) (hX : Consistent l Decoded.kernel A m X) (hg : g < l.threads) :
    ∃ site, (X.tr g).getLast? = some ⟨site, .exit⟩ := by
  obtain ⟨⟨site, kind⟩, he, hKind⟩ := h.last hX hg
  exact ⟨site, by cases hKind; exact he⟩

end PTX.Kernels.TmlFa4Fwd.Thread

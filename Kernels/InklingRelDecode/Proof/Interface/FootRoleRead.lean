-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FootBar
public import Kernels.InklingRelDecode.Proof.Interface.FootSrc
public import Kernels.InklingRelDecode.Proof.Interface.ShapeInput

@[expose] public section

/-!
# Small facts about events, for the reads of shared words

`write_present` (a write names its issuing event), `state_of_prev` (the state before an event whose
thread was tracked up to the event before it), the barrier-1 classification of reads, writes and
barrier events, and `bar_not_ub`. The reads of the role byte themselves are the second tree's
(`Proof2.role_byte`, used by `FootRoleAll.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A write names its issuing event. -/
theorem write_present (hX : Consistent L kernel asms mem0 X) {r : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} (h : X.MemWrites r a bs) : Present X (refEvent r) := by
  rcases r with ⟨g, k⟩ | ⟨i, p⟩
  · rcases h with ⟨pc, hh⟩ | ⟨old, pc, hh⟩
    · exact ⟨_, hh⟩
    · exact ⟨_, hh⟩
  · cases p
    case writeLoad x y z =>
      obtain ⟨o, addr, b, -, ⟨pc, hget⟩, -⟩ := h
      exact ⟨_, hget⟩
    case writeStore x y k =>
      obtain ⟨o, addr, b, -, ⟨pc, hget⟩, -⟩ := h
      exact absurd hget (no_tensorStore hX)
    case writeCta c =>
      obtain ⟨s, targets, ⟨pc, hget⟩, -⟩ := h
      exact absurd hget (no_clc hX)
    case writeCopy =>
      obtain ⟨s, ⟨pc, hget⟩, -⟩ := h
      exact absurd hget (no_copy hX)
    case writeElem j =>
      obtain ⟨s, ⟨pc, hget⟩, -⟩ := h
      exact absurd hget (no_copy hX)
    all_goals exact (h : False).elim

/-- **The state before a non-undefined-behaviour event whose thread was tracked up to the event
before it.** -/
theorem state_of_prev (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hX : Consistent L kernel asms mem0 X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hprev : k = 0 ∨ ∃ k', k = k' + 1 ∧ TT Q L X (g, k')) :
    ∃ s, St Q L X g k = some (some s) := by
  rcases hprev with rfl | ⟨k', rfl, hT⟩
  · exact ⟨_, Frame.stateAt_zero⟩
  · rcases Frame.fired hS hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
    · cases σ with
      | none => exact absurd hσ hT
      | some s => exact ⟨s, hσ⟩
    · exact absurd rfl (hub pc f)

theorem isBarId_rd {pc : Nat} {a : Acc} {bs : List (Option Byte)} {i : Nat} :
    ¬ Execution.isBarId i (⟨pc, .rd a bs⟩ : Event) = true := by
  simp [Execution.isBarId]

theorem isBarId_wr {pc : Nat} {a : Acc} {bs : List Byte} {i : Nat} :
    ¬ Execution.isBarId i (⟨pc, .wr a bs⟩ : Event) = true := by
  simp [Execution.isBarId]

theorem isBarId_bar {pc : Nat} {m : BarMode} {i : Nat} :
    Execution.isBarId i (⟨pc, .bar i none m⟩ : Event) = true := by
  simp [Execution.isBarId]

/-- The bar event of a barrier-1 arrival is no undefined-behaviour event. -/
theorem bar_not_ub {pc : Nat} {m : BarMode} :
    ∀ pc' f, (⟨pc, .bar 1 none m⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
  intro pc' f h
  cases h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface

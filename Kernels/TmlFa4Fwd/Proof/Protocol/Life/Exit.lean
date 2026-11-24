-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.SharedLifetime
import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # The exits of a CTA that exited -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX

variable {L : Launch} {X : Execution}

/-- A lane of an exited CTA exits. -/
theorem exit_of_exited {c g : Nat} (hx : CtaExited L X c) (hg : g < L.threads)
    (hc : g / L.block = c) : ∃ pc, X.get (g, (X.tr g).length - 1) = some ⟨pc, .exit⟩ := by
  obtain ⟨pc, hl⟩ := hx g hg hc
  rw [List.getLast?_eq_getElem?] at hl
  exact ⟨pc, hl⟩

/-- An event of a lane that exits last and is no exit is before its exit. -/
theorem before_exit {g k pc pcx : Nat} {kd : Kind} (he : X.get (g, k) = some ⟨pc, kd⟩)
    (hne : kd ≠ .exit) (hx : X.get (g, (X.tr g).length - 1) = some ⟨pcx, .exit⟩) :
    k < (X.tr g).length - 1 ∧ (X.tr g).length - 1 < (X.tr g).length := by
  have h1 : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have h2 : (X.tr g).length - 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
  refine ⟨?_, h2⟩
  rcases Nat.lt_or_eq_of_le (show k ≤ (X.tr g).length - 1 by omega) with h | h
  · exact h
  · rw [← h, he] at hx
    cases hx
    exact absurd rfl hne

end PTX.Kernels.TmlFa4Fwd.Proof.Life

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Mma.Warp
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.JR
import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # The thread view: a role's invariant from the thread invariant

`JR` (`Top/Register.lean`) selects a lane's reference invariant by its warp index (the softmax
warps' below warp 8, `RefAll` above), not by the role tag of its state. The projections below
read the role's warp and its reference invariant off a role state, once: `JR.softmax`,
`JR.correction`, `JR.mma`, `JR.epilogue`, `JR.loader`, and `JR.not_stub` (no stub state holds
`JR`). `table_ev` is the common opening of a cross-role proof: an event of a thread that is not
undefined behaviour has a followed state before it, which holds `JR`, the machine's invariant
and the shape table (`TEv`). New code uses these instead of unfolding `JR` or splitting on the
role. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {n : Cls → Nat}

/-- A softmax state is on a softmax warp, with the softmax warps' invariant. -/
theorem JR.softmax {d : (frag p L g .softmax).D} (h : JR p L g (.inr ⟨.softmax, d⟩, n)) :
    Prologue.warpIndex L g < 8 ∧
      SmWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.softmax, d⟩, n) := by
  rw [JR_eq] at h
  by_cases h8 : Prologue.warpIndex L g < 8
  · simp only [h8, ↓reduceIte] at h
    exact ⟨h8, h⟩
  · simp only [h8, ↓reduceIte] at h
    unfold RefAll at h
    split_ifs at h <;> exact False.elim h

/-- A correction state is on a correction warp, with the correction warps' invariant. -/
theorem JR.correction {d : (frag p L g .correction).D}
    (h : JR p L g (.inr ⟨.correction, d⟩, n)) (hw16 : Prologue.warpIndex L g < 16) :
    8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11 ∧
      CorrWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.correction, d⟩, n) := by
  rw [JR_eq] at h
  by_cases h8 : Prologue.warpIndex L g < 8
  · simp only [h8, ↓reduceIte] at h
    exact False.elim h
  · simp only [h8, ↓reduceIte] at h
    unfold RefAll at h
    split_ifs at h with h12 h13 h14
    · exact False.elim h
    · exact False.elim h
    · exact False.elim h
    · exact ⟨by omega, by omega, h⟩

/-- An MMA state is on warp 12, with the MMA warp's invariant. -/
theorem JR.mma {d : (frag p L g .mma).D} (h : JR p L g (.inr ⟨.mma, d⟩, n)) :
    Prologue.warpIndex L g = 12 ∧ Mma.Ref p L g (.inr ⟨.mma, d⟩, n) := by
  rw [JR_eq] at h
  by_cases h8 : Prologue.warpIndex L g < 8
  · simp only [h8, ↓reduceIte] at h
    exact False.elim h
  · simp only [h8, ↓reduceIte] at h
    unfold RefAll at h
    split_ifs at h with h12
    · exact ⟨h12, h⟩
    all_goals exact False.elim h

/-- An output state is on warp 13, with the output warp's invariant. -/
theorem JR.epilogue {d : (frag p L g .epilogue).D} (h : JR p L g (.inr ⟨.epilogue, d⟩, n)) :
    Prologue.warpIndex L g = 13 ∧ Epilogue.Ref p L g (.inr ⟨.epilogue, d⟩, n) := by
  rw [JR_eq] at h
  by_cases h8 : Prologue.warpIndex L g < 8
  · simp only [h8, ↓reduceIte] at h
    exact False.elim h
  · simp only [h8, ↓reduceIte] at h
    unfold RefAll at h
    split_ifs at h with h12 h13
    · exact False.elim h
    · exact ⟨h13, h⟩
    all_goals exact False.elim h

/-- A loader state is on warp 14 or 15, with the loader warps' invariant. -/
theorem JR.loader {b : Bool} {d : (frag p L g (.loader b)).D}
    (h : JR p L g (.inr ⟨.loader b, d⟩, n)) :
    (Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) ∧
      LdWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.loader b, d⟩, n) := by
  rw [JR_eq] at h
  by_cases h8 : Prologue.warpIndex L g < 8
  · simp only [h8, ↓reduceIte] at h
    exact False.elim h
  · simp only [h8, ↓reduceIte] at h
    unfold RefAll at h
    split_ifs at h with h12 h13 h14
    · exact False.elim h
    · exact False.elim h
    · exact ⟨h14, h⟩
    · exact False.elim h

/-- No stub state holds `JR`. -/
theorem JR.not_stub {r : Startup.Entry} {d : (frag p L g (.stub r)).D}
    (h : JR p L g (.inr ⟨.stub r, d⟩, n)) : False := by
  rw [JR_eq] at h
  by_cases h8 : Prologue.warpIndex L g < 8
  · simp only [h8, ↓reduceIte] at h
    exact h
  · simp only [h8, ↓reduceIte] at h
    unfold RefAll at h
    split_ifs at h <;> exact h

/-- **An event of a thread that is not undefined behaviour** has a followed state before it,
which holds `JR`, the thread machine's invariant and the shape table. -/
theorem table_ev (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {h k : Nat} {e : Event} (he : X.get (h, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ σ, Frame.stateAt (thread p L) X h k = some (some σ) ∧ JR p L h σ ∧
      (thread p L h).inv σ ∧ TEv p L h σ e :=
  have ⟨σ, n, hσ, _, hJ, hi, hev⟩ := ev_open hp hX (launchFollow hp hX) he hub
  ⟨(σ, n), hσ, hJ, hi, hev⟩

end PTX.Kernels.TmlFa4Fwd.Proof

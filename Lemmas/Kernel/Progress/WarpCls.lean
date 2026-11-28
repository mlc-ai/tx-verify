-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpCollPair

@[expose] public section

/-! # The collectives of two lanes of a warp, from a classification of its states

`warpPair_of_cls`: the facts of two lanes of a warp (`WarpPair`) from a classification of
the states of the lanes `P` by their collectives (`WarpCls`). A warp's collectives are a list of
program counters in order (`cn`: the pc of the `n`-th collective, none past the last), and the
time table puts the state at the `n`-th collective at `slot n` and every earlier state below it.
The role supplies these facts, the release of a mate at its collective and that no stopped lane
is blocked; the one position and static part, the exit, the lag are here. -/

namespace PTX.Sched

open PTX PTX.Flow

noncomputable section

/-- The collectives a lane has made by its position `k`. -/
abbrev collCount (X : Execution) (x k : Nat) : Nat := ((X.tr x).take k).countP isWarpColl

/-- **The classification of the states of the lanes `P` of one warp** by their collectives:
`cn n` is the pc of the warp's `n`-th collective, `slot n` its time. -/
structure WarpCls {K : Kernel} {A : List Assumption} {L : Launch} (M : Timed K A L) (m : Mem0)
    (X : Execution) (P : Nat → Prop) (AtColl : ∀ g, (M.code g).D → Prop)
    (cn : Nat → Option Nat) (slot : Nat → Nat) : Prop where
  /-- A state is at a collective exactly when its pc is the one of its count. -/
  at_ : ∀ {x k σ}, P x → Frame.stateAt M.code X x k = some (some σ) →
    (AtColl x σ ↔ cn (collCount X x k) = some ((M.code x).pc σ))
  /-- A collective event is fired from a state at a collective. -/
  isP : ∀ {x k σ e}, P x → Frame.stateAt M.code X x k = some (some σ) →
    X.get (x, k) = some e → isWarpColl e = true → AtColl x σ
  slot_mono : ∀ {a b}, a < b → (cn b).isSome = true → slot a < slot b
  time_at : ∀ {x k σ}, P x → Frame.stateAt M.code X x k = some (some σ) → AtColl x σ →
    M.time x σ = slot (collCount X x k)
  time_lt : ∀ {x k σ}, P x → Frame.stateAt M.code X x k = some (some σ) → ¬ AtColl x σ →
    ∀ n, (cn n).isSome = true → collCount X x k ≤ n → M.time x σ < slot n
  /-- A lane exits after every collective of the warp. -/
  exit : ∀ {y k pc σ}, P y → Frame.stateAt M.code X y k = some (some σ) →
    X.get (y, k) = some ⟨pc, .exit⟩ → ∀ n, (cn n).isSome = true → n < collCount X y k
  /-- Of two lanes of the warp at one collective, when one is released, the other is. -/
  released : ∀ {x y} {σ : (M.code x).D} {σ' : (M.code y).D}, P x → P y → SameWarp L x y →
    Frame.stateAt M.code X x (X.tr x).length = some (some σ) → AtColl x σ →
    Frame.stateAt M.code X y (X.tr y).length = some (some σ') → AtColl y σ' →
    (X.tr y).countP isWarpColl = (X.tr x).countP isWarpColl → Step.Released L X x →
    Step.Released L X y ∨ ∃ Y, Consistent L K A m Y ∧ X.le Y ∧
      X.size L < Y.size L
  /-- A pending lane whose machine stopped is released. -/
  dead : ∀ {y}, P y → Frame.Pending L X y →
    Frame.stateAt M.code X y (X.tr y).length = none → Step.Released L X y

variable {K : Kernel} {A : List Assumption} {L : Launch} {M : Timed K A L} {m : Mem0}
  {X : Execution} {g h : Nat}
  {AtColl : ∀ g, (M.code g).D → Prop}

/-- **The collectives of two lanes of a warp**, from a classification; the static part is a
function of the pc. -/
theorem warpPair_of_cls {P : Nat → Prop} {S : ∀ g, (M.code g).D → CollShape}
    {cn : Nat → Option Nat} {slot : Nat → Nat} (C : WarpCls M m X P AtColl cn slot)
    (hS : ∀ {x y σ σ'}, (M.code x).pc σ = (M.code y).pc σ' → S x σ = S y σ')
    (ht : Frame.Tracked M.code X) (hs : SameWarp L g h) (hAg : P g) (hAh : P h) :
    WarpPair m M X AtColl S g h := by
  have hh := hs.1.2.1
  have hPos : ∀ {x k σ}, P x → CollPos M X AtColl x k σ →
      cn (collCount X x k) = some ((M.code x).pc σ) := by
    rintro x k σ hA ⟨hσ, ⟨e, he, hc⟩ | ⟨-, hat⟩⟩
    · exact (C.at_ hA hσ).mp (C.isP hA hσ he hc)
    · exact (C.at_ hA hσ).mp hat
  refine ⟨fun {k k' σ σ'} hP hP' hn => ?_, fun {σ σ'} hσ hcg hσ' hch hn hrel =>
    C.released hAg hAh hs hσ hcg hσ' hch hn hrel,
    fun {k pc σ σ'} hσ hcg hσ' he => ?_, fun {σ} hσ hcg hle hno hnn => ?_,
    fun hph hσ' => C.dead hAh hph hσ'⟩
  · have e1 := hPos hAg hP
    have e2 := hPos hAh hP'
    have hpc : (M.code g).pc σ = (M.code h).pc σ' := by
      rw [show collCount X g k = collCount X h k' from hn] at e1
      exact Option.some.inj (e1.symm.trans e2)
    exact ⟨hpc, hS hpc⟩
  · have hc := (C.at_ hAg hσ).mp hcg
    have := C.exit hAh hσ' he (collCount X g (X.tr g).length) (by rw [hc]; rfl)
    simpa [collCount] using this
  · have hc := (C.at_ hAg hσ).mp hcg
    cases hσ' : Frame.stateAt M.code X h (X.tr h).length with
    | none => exact absurd hσ' hnn
    | some o =>
      cases o with
      | none => exact absurd hσ' (ht h _ hh)
      | some σ' =>
        refine lt_of_eq_of_lt (threadTime_of (M := M) hσ') ?_
        rw [C.time_at hAg hσ hcg]
        have hle' : collCount X h (X.tr h).length ≤ collCount X g (X.tr g).length := by
          simpa [collCount] using hle
        by_cases hch : AtColl h σ'
        · have hne : collCount X h (X.tr h).length ≠ collCount X g (X.tr g).length := fun heq =>
            hno ⟨by simpa [collCount] using heq, σ', hσ', hch⟩
          rw [C.time_at hAh hσ' hch]
          exact C.slot_mono (lt_of_le_of_ne hle' hne) (by rw [hc]; rfl)
        · exact C.time_lt hAh hσ' hch _ (by rw [hc]; rfl) hle'

end
end PTX.Sched

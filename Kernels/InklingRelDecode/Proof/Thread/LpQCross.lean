-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ScFence
public import Kernels.InklingRelDecode.Proof.Thread.FootQ

@[expose] public section

/-!
# The query stores are one straight line before the fence `fnc1`

The prologue's 32 query-store sites (`stqSite i`, the four elements of each of the eight
`st.shared.v4.b32`) follow each other, and the fence `fnc1` follows the last; none of these steps
changes the machine's data. `next_into_stq` says which state a step into one of these sites (or
into `fnc1`) comes from, so a thread at `fnc1` was, `32 - i` events before, at store site `i`,
with the same data (`Interface.LpQStore`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The sites after the first store, up to the fence: store sites `1 … 31` and `fnc1`. -/
def stqTail : List Site :=
  [.stq0_1, .stq0_2, .stq0_3, .stq1_0, .stq1_1, .stq1_2, .stq1_3, .stq2_0, .stq2_1, .stq2_2,
    .stq2_3, .stq3_0, .stq3_1, .stq3_2, .stq3_3, .stq4_0, .stq4_1, .stq4_2, .stq4_3, .stq5_0,
    .stq5_1, .stq5_2, .stq5_3, .stq6_0, .stq6_1, .stq6_2, .stq6_3, .stq7_0, .stq7_1, .stq7_2,
    .stq7_3, .fnc1]

/-- The site of index `i ≤ 32` of the chain: store site `i`, and `fnc1` for `32`. -/
def chainSite (i : Nat) : Site := if i < 32 then stqSite i else .fnc1

/-- **A step into a site of the chain after its first** comes from the chain's previous site, with
the same data. -/
theorem next_into_tail {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hs : d'.site ∈ stqTail) :
    (∃ i < 32, s = chainSite i ∧ d'.site = chainSite (i + 1)) ∧ d'.dt = dt := by
  cases s <;>
    (simp only [next] at h
     repeat' split at h
     all_goals first
       | (cases h; done)
       | (simp only [Option.some.injEq] at h
          subst h
          simp only at hs ⊢
          first
            | (exfalso; revert hs; decide)
            | (unfold qSite at hs; (repeat' split at hs) <;> (exfalso; revert hs; decide))
            | exact ⟨by decide, trivial⟩))

theorem chainSite_tail {i : Nat} (hi : i < 32) : chainSite (i + 1) ∈ stqTail := by
  have key : ∀ i < 32, chainSite (i + 1) ∈ stqTail := by decide
  exact key i hi

theorem chainSite_inj {i j : Nat} (hi : i < 33) (hj : j < 33) (h : chainSite i = chainSite j) :
    i = j := by
  have key : ∀ i < 33, ∀ j < 33, chainSite i = chainSite j → i = j := by decide
  exact key i hi j hj h

theorem chainSite_stq {i : Nat} (hi : i < 32) : chainSite i = stqSite i := by
  simp [chainSite, hi]

theorem chainSite_fnc1 : chainSite 32 = .fnc1 := rfl

end
end PTX.Kernels.InklingRelDecode.Proof.ProA

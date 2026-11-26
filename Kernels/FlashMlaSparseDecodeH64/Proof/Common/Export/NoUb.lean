-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbId
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Lemmas.Kernel.NoUbFollowedSites

@[expose] public section

/-! # No undefined behaviour from the role leaves

`noUb_of_leaves`: if every role's leaf holds (`NoUbLeaf`), no event of a followed execution is
undefined behaviour. The thread machine follows every launched thread (`Follow`), so
`Frame.noUb_of_followed_sites` applies: at a followed state the leaf of the state's role gives the
`safe` and `live` obligations, the state's role being a case split on its constructor. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

/-- The role of a followed state (`J` excludes the stubs). -/
private theorem role_of_state {g : Nat} {σ : (thread P L g).D} (hJ : (table P L).J g σ) :
    ∃ r, InRole P L g r σ := by
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d'⟩
  · exact ⟨_, .startup d n⟩
  · cases i with
    | wg0 => exact ⟨_, .wg0 d' n⟩
    | dequant => exact ⟨_, .dequant d' n⟩
    | wg1 =>
      rcases d' with s | ⟨j | r, d⟩
      · exact ⟨_, .head s n⟩
      · cases j with
        | mma => exact ⟨_, .mma d n⟩
        | tma => exact ⟨_, .tma d n⟩
        | index => exact ⟨_, .index d n⟩
        | idle => exact ⟨_, .idle d n⟩
      · obtain ⟨-, hW, -⟩ := hJ
        exact hW.elim
  · exact hJ.elim

/-- **No event is undefined behaviour, given every role's leaf.** -/
theorem noUb_of_leaves (hp : Pre P L m) (hl : ∀ r, NoUbLeaf P L m r) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  have hg := Frame.lt_of_get hX he
  have hF := (follow_iff.mp hFw) g hg
  have key : ∀ k d e, X.get (g, k) = some e →
      Frame.stateAt (thread P L) X g k = some (some d) → (table P L).J g d →
      (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
    intro k d e he hσ hJ
    obtain ⟨r, hr⟩ := role_of_state hJ
    exact hl r hp X hX hFw g k e he (aliveIn_iff.mpr ⟨d, hσ, hr⟩)
  exact Frame.noUb_of_followed_sites (C := thread P L) (J := (table P L).J) hX hF
    (fun k d e he hσ hJ => (key k d e he hσ hJ).1)
    (fun k d e he hσ hJ _ hn => (key k d e he hσ hJ).2 (by
      refine stopsAt_iff.mpr ?_
      rw [Frame.stateAt_succ he, hσ]
      exact hn)) he f rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg

@[expose] public section

/-!
# The `P` stores of one thread are in the order of the iterations

After a softmax state at `tmemSt` of iteration `i`, the thread's later states are at `tmemWait`,
`bar21` or `arrive` of iteration `i`, or in a later iteration (the loop counter rises only after
`bar21` and `arrive`, `Interface.next_iter`). So two states of one thread at `tmemSt` are in the
order of their iterations, and one iteration has one such state (`tmemSt_order`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Kk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The sites that follow the `P` store within an iteration. -/
def AfterTm : Sm.Site → Prop
  | .tmemWait | .bar21 | .arrive => True
  | _ => False

/-- **The `P` store is followed by `tmemWait`, `bar21` and `arrive`** within its iteration. -/
theorem next_afterTm {d0 d : Sm.D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d0.site = .tmemSt ∨ AfterTm d0.site) (hi : d.i = d0.i) : AfterTm d.site := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (rcases hs with hs | hs <;> simp_all [AfterTm]; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [AfterTm]; done)
    | (unfold Sm.afterArrive at hn
       have h1 := afterSetup_i hn
       simp only at h1
       omega)

/-- **The states after a `P` store.** At an event after the state `d` at `tmemSt`, a softmax state
is in a later iteration or in the same iteration at a site that follows the store. -/
theorem after_tmemSt {k : Nat} {d : Sm.D}
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .tmemSt) :
    ∀ m, k ≤ m → m ≤ (X.tr g).length → ∀ s : DComp.St,
      St Q L X g m = some (some (.d s)) →
      ¬ PreSt s ∧ ∀ d', s = .sm d' → (m = k ∧ d' = d) ∨
        (k < m ∧ (d.i < d'.i ∨ (d'.i = d.i ∧ AfterTm d'.site))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hkm hm s hσm
    rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
    · rw [hσ] at hσm
      simp only [Option.some.injEq, TSt.d.injEq] at hσm
      subst hσm
      exact ⟨by simp [PreSt], fun d' h => by
        simp only [DComp.St.sm.injEq] at h
        exact Or.inl ⟨rfl, h.symm⟩⟩
    · rcases pred_d hm hσm with ⟨rfl, -⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
      · omega
      · obtain ⟨hp0, hr0⟩ := ih k0 (by omega) (by omega) (by omega) s0 hσ0
        refine ⟨fun hp => hp0 (dnext_pre hn hp), fun d' hd' => ?_⟩
        subst hd'
        rcases dnext_sm hn with ⟨dp, rfl, -⟩ | ⟨d0, rfl, hn0⟩
        · exact absurd trivial hp0
        · have hr := hr0 d0 rfl
          right
          refine ⟨by omega, ?_⟩
          rcases next_iter hn0 with hi | ⟨hi, -⟩
          · rcases hr with ⟨-, rfl⟩ | ⟨-, hr | ⟨hi0, hA⟩⟩
            · right
              exact ⟨hi, next_afterTm hn0 (Or.inl hs) hi⟩
            · left; omega
            · right
              exact ⟨by omega, next_afterTm hn0 (Or.inr hA) hi⟩
          · left
            rcases hr with ⟨-, rfl⟩ | ⟨-, hr | ⟨hi0, hA⟩⟩ <;> omega

/-- **Two `P` store states of a thread are in the order of their iterations.** -/
theorem tmemSt_order {k k' : Nat} {d d' : Sm.D} (hk' : k' ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .tmemSt)
    (hσ' : St Q L X g k' = some (some (.d (.sm d')))) (hs' : d'.site = .tmemSt)
    (hlt : k < k') : d.i < d'.i := by
  obtain ⟨-, hr⟩ := after_tmemSt hσ hs k' hlt.le hk' _ hσ'
  rcases hr d' rfl with ⟨h1, -⟩ | ⟨-, hr | ⟨-, hA⟩⟩
  · omega
  · exact hr
  · rw [hs'] at hA
    exact absurd hA (by simp [AfterTm])

/-- **One iteration of a thread has one `P` store state.** -/
theorem tmemSt_unique {k k' : Nat} {d d' : Sm.D} (hk : k ≤ (X.tr g).length)
    (hk' : k' ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .tmemSt)
    (hσ' : St Q L X g k' = some (some (.d (.sm d')))) (hs' : d'.site = .tmemSt)
    (hi : d.i = d'.i) : k = k' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have := tmemSt_order hk' hσ hs hσ' hs' h
    omega
  · exact h
  · have := tmemSt_order hk hσ' hs' hσ hs h
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Kk

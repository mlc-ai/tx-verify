-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.LegacyExtension
public import Lemmas.Execution.NoAsync

@[expose] public section

section
namespace PTX
noncomputable section
open AsyncCopy

/-- Replace one CTA's history by an extension of the actual recorded prefix. -/
def Execution.withCtaHistory (X : Execution) (c : Nat) (records : List (CtaBarrier.Record EvId)) :
    Execution := {X with barriers := fun d => if d = c then records else X.barriers d}

theorem Execution.le_withCtaHistory (X : Execution) (c : Nat)
    {records : List (CtaBarrier.Record EvId)} (hp : X.barriers c <+: records) :
    X.le (X.withCtaHistory c records) := by
  have hx := X.le_refl
  refine ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,?_,hx.2.2.2.2.2⟩
  intro d
  by_cases hd : d = c
  · subst d; simpa [Execution.withCtaHistory] using hp
  · simp only [Execution.withCtaHistory,ite_eq_right hd]
    exact List.prefix_refl _

variable {L : Launch} {X : Execution} {c : Nat} {records : List (CtaBarrier.Record EvId)}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0}

theorem modelCausality_withCtaHistory
    (hbo : ∀ e f, baseCausality L (X.withCtaHistory c records) e f ↔ baseCausality L X e f)
    {l : Loc} {e f : Ref} :
    modelCausality L (X.withCtaHistory c records) l e f ↔ modelCausality L X l e f := by
  have hcb (i p w f) : ObservedCompletionBefore L (X.withCtaHistory c records) l i p w f ↔
      ObservedCompletionBefore L X l i p w f :=
    observedCompletionBefore_congr rfl rfl (hbo w f) (by simp only [ProxyBefore, hbo]; rfl)
  cases e <;> cases f <;> simp only [modelCausality,ProxyBefore,hbo,hcb]
  all_goals first
    | rfl
    | exact and_congr_right fun _ =>
        AsyncChain.congr (fun _ _ => by simp only [AsyncBefore,hbo]; rfl)
        (fun _ p => by cases p <;> rfl)

end
end PTX
end

section
namespace PTX
noncomputable section
variable {L : Launch} {X : Execution} {c : Nat} {records : List (CtaBarrier.Record EvId)}

theorem ctaBarK_withCtaHistory_other {e : EvId} {key : Nat} (hne : e.1/L.block ≠ c) :
    CtaBarK L (X.withCtaHistory c records) e key ↔ CtaBarK L X e key := by
  have heq : (X.withCtaHistory c records).barriers (e.1/L.block) = X.barriers (e.1/L.block) := by
    simp [Execution.withCtaHistory,hne]
  constructor
  · rintro ⟨hg,hbar,hgen⟩
    exact ⟨hg,hbar,by rwa [heq] at hgen⟩
  · rintro ⟨hg,hbar,hgen⟩
    exact ⟨hg,hbar,by rw [heq]; exact hgen⟩

theorem ctaBarArrivalK_withCtaHistory_other {e : EvId} {key : Nat} (hne : e.1/L.block ≠ c) :
    CtaBarArrivalK L (X.withCtaHistory c records) e key ↔ CtaBarArrivalK L X e key := by
  have heq : (X.withCtaHistory c records).barriers (e.1/L.block) = X.barriers (e.1/L.block) := by
    simp [Execution.withCtaHistory,hne]
  constructor
  · rintro ⟨hg,hbar,hgen⟩
    exact ⟨hg,hbar,by rwa [heq] at hgen⟩
  · rintro ⟨hg,hbar,hgen⟩
    exact ⟨hg,hbar,by rw [heq]; exact hgen⟩

end
end PTX
end

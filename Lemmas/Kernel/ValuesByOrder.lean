-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Order.OrderBaseCausality
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-! # Facts about the events of an execution by induction on base causality

A proof tool for the layers above the thread layer. A thread machine records the values its
events returned without a claim about them; a claim such as "the word this load returned is the
one the producer stored" is proved for every event of a consistent execution at once, assuming it
for the events that precede the event in base causality (`values_by_order`). Base causality is a
strict order on the finitely many events of the execution (`causal_wellFounded`), so the
induction is well founded. `causal_minimal` gives a causally minimal event of a nonempty set. -/

namespace PTX.Frame

open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The events present in an execution. -/
def PresentEv (X : Execution) := { i : EvId // ∃ e, X.get i = some e }

/-- Base causality is well founded on the events of a consistent execution. -/
theorem causal_wellFounded (hX : Consistent L K A mem0 X) :
    WellFounded (fun a b : PresentEv X => baseCausality L X a.val b.val) := by
  let packed (i : PresentEv X) : Σ g : Fin L.threads, Fin (X.tr g.val).length :=
    ⟨⟨i.val.1, by
        obtain ⟨e, he⟩ := i.property
        have hk := (List.getElem?_eq_some_iff.mp he).1
        by_contra hn
        rw [hX.outside _ (by omega)] at hk
        simp at hk⟩,
      ⟨i.val.2, (List.getElem?_eq_some_iff.mp i.property.choose_spec).1⟩⟩
  have packed_inj : Function.Injective packed := by
    intro i j hij
    have hhead := congrArg (fun p : Σ g : Fin L.threads, Fin (X.tr g.val).length => p.1.val) hij
    have htail := congrArg (fun p : Σ g : Fin L.threads, Fin (X.tr g.val).length => p.2.val) hij
    exact Subtype.ext (Prod.ext hhead htail)
  let : Finite (PresentEv X) := Finite.of_injective packed packed_inj
  let rel (i j : PresentEv X) := baseCausality L X i.val j.val
  let : IsTrans (PresentEv X) rel := ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
  let : Std.Irrefl rel := ⟨fun _ => baseCausality_irrefl hX.object.cause⟩
  exact Finite.wellFounded_of_trans_of_irrefl rel

/-- **Facts by causal induction**: a property of the events of a consistent execution that holds
at each event whenever it holds at the events before it in base causality holds at every
event. -/
theorem values_by_order (hX : Consistent L K A mem0 X) (Q : EvId → Prop)
    (step : ∀ i e, X.get i = some e →
      (∀ j e', X.get j = some e' → baseCausality L X j i → Q j) → Q i) :
    ∀ i e, X.get i = some e → Q i := by
  have claim (i : PresentEv X) : Q i.val := by
    induction i using (causal_wellFounded hX).induction with
    | h i ih =>
      obtain ⟨e, he⟩ := i.property
      exact step i.val e he fun j e' hj hc => ih ⟨j, e', hj⟩ hc
  exact fun i e he => claim ⟨i, e, he⟩

/-- A nonempty set of present events has a causally minimal element. -/
theorem causal_minimal (hX : Consistent L K A mem0 X) (p : EvId → Prop)
    (hget : ∀ i, p i → ∃ e, X.get i = some e) (hex : ∃ i, p i) :
    ∃ i, p i ∧ ∀ j, baseCausality L X j i → ¬ p j := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨i, hi⟩ := hex
  obtain ⟨e, he⟩ := hget i hi
  exact values_by_order hX (fun i => ¬ p i)
    (fun i _ _ ih hp => by
      obtain ⟨j, hj, hpj⟩ := hno i hp
      obtain ⟨e', he'⟩ := hget j hpj
      exact ih j e' he' hj hpj) i e he hi

end PTX.Frame

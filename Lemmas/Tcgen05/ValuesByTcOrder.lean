-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.ValuesByOrder
public import Lemmas.Tcgen05.TcFence
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-! # Facts about the events of an execution by induction on the tcgen05 order

A proof tool beside `Frame.values_by_order`. The tcgen05 orders (`TcMma.TcStep`: causality, a
morally strong mbarrier observation, an MMA's observed commit) have no cycle under guarded
synchronization (`TcMma.tcStep_acyclic`), and the events of an execution are finitely many, so
the transitive closure of `TcStep` is well founded. A claim about the events of a consistent
execution that holds at an event when it holds at every event with a `TcStep` path to it holds
at every event (`values_by_tcStep`). The claim of a Tensor Memory word may thus use the claims of
the writes its source chain consists of: MMA results, stores, and the loads between them. -/

namespace PTX.Frame

open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The paths of tcgen05 orders are well founded on the events of a consistent execution with
guarded synchronization. -/
theorem tcStep_wellFounded (hX : Consistent L K A mem0 X) (hG : SyncGuarded L K X) :
    WellFounded (fun a b : PresentEv X => Relation.TransGen (TcMma.TcStep L X) a.val b.val) := by
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
  let rel (i j : PresentEv X) := Relation.TransGen (TcMma.TcStep L X) i.val j.val
  let : IsTrans (PresentEv X) rel := ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
  let : Std.Irrefl rel := ⟨fun i => TcMma.tcStep_acyclic hX hG i.val⟩
  exact Finite.wellFounded_of_trans_of_irrefl rel

/-- **Facts by tcgen05 induction**: a property of the events of a consistent execution that holds
at each event whenever it holds at the events with a `TcStep` path to it holds at every event. -/
theorem values_by_tcStep (hX : Consistent L K A mem0 X) (hG : SyncGuarded L K X)
    (Q : EvId → Prop)
    (step : ∀ i e, X.get i = some e →
      (∀ j e', X.get j = some e' → Relation.TransGen (TcMma.TcStep L X) j i → Q j) → Q i) :
    ∀ i e, X.get i = some e → Q i := by
  have claim (i : PresentEv X) : Q i.val := by
    induction i using (tcStep_wellFounded hX hG).induction with
    | h i ih =>
      obtain ⟨e, he⟩ := i.property
      exact step i.val e he fun j e' hj hc => ih ⟨j, e', hj⟩ hc
  exact fun i e he => claim ⟨i, e, he⟩

end PTX.Frame

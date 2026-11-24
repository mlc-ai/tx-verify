-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocMemory
public import Lemmas.Snoc.SnocPlainWaiting

@[expose] public section

section
/-!
# Extension by a barrier arrival

Appending thread `g`'s next barrier arrival to a possible execution gives a possible
execution (`consistent_bar_snoc`), whatever other events the execution has (bulk copies,
mbarriers, `tcgen05`). The arrival is `g`'s `kb`-th, where `kb` counts `g`'s arrivals so
far. Since `g` has not arrived at instance `kb`, no thread of its CTA has an event after
its own `kb`-th arrival, so the arrival adds no synchronization between old events: base
causality among old events is unchanged (`baseCausality_snoc_old_bar`).
-/

namespace PTX

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}

theorem countP_take_lt {p : Event → Bool} {l : List Event} {i : Nat} (hi : i < l.length)
    (hp : p l[i] = true) : (l.take i).countP p < l.countP p := by
  have h1 : (l.take (i + 1)).countP p = (l.take i).countP p + 1 := by
    rw [List.take_add_one, List.countP_append, List.getElem?_eq_getElem hi]; simp [hp]
  have h2 : (l.take (i + 1)).countP p ≤ l.countP p := (List.take_sublist (i + 1) l).countP_le
  omega

theorem baseCausality_snoc_old_bar {mem0 : Mem0} (hcl : ClusterHistoryOk L X)
    (hrf : RfWf mem0 X) (hbk : CtaBarHistoryOk L X)
    (_hg : g < L.threads) (hk : e.kind.isTma = false)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length) :
    baseCausality L (X.snoc g e r) a b ↔ baseCausality L X a b :=
  ⟨fun h => baseCausality_old_of_step (fun hb => snoc_step_old_with_bar
    (fun _ _ he => by rw [he] at hk; cases hk) hcl (.of_rfWf hrf)
    (fun _ _ => snoc_ctaBarK_history hbk)
    (fun _ _ => snoc_ctaBarArrivalK_history hbk)
    (fun _ _ _ _ he => by rw [he] at hk; cases hk)
    (fun _ he => by rw [he] at hk; cases hk) hb) h hbo, baseCausality_snoc⟩

end
end PTX
end

section
/-! A source barrier arrival does not itself record a resource update. Checked
histories retain their old references, so appending the source arrival is covered
by the ordinary append frame. Collective resource updates have
separate extension proofs. -/
namespace PTX
noncomputable section

/-- Appending an unrecorded source arrival keeps the execution-order axioms. -/
theorem snoc_bar_orderOk {L : Launch} {X : Execution} {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {id : Nat} {count : Option Nat}
    (he : e.kind = .bar id count) : OrderOk L K A (X.snoc g e r) :=
  snoc_plain_orderOk hX (.of_plain (by rw [he]; rfl)) (by simp [he]) (by simp [he])
    (by simp [Kind.laneValue, he]) (by obtain ⟨pc, k⟩ := e; subst he; rfl) (by simp [he])
    (by simp [he])

end
end PTX
end

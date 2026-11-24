-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX

/-- A recorded event at or after a cursor makes that actual suffix nonempty. -/
theorem traceAfterObservedEvent {X : Execution} {g i j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hle : i ≤ j) : (X.tr g).drop i ≠ [] := by
  intro h
  exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
    ((List.drop_eq_nil_iff.mp h).trans hle)

/-- A cursor can continue if its lane terminated or a downstream event is already present. -/
def PrefixDemand (X : Execution) (g pos bound : Nat) (ending : Option TState) : Prop :=
  ending = none ∨ ∃ (j : Nat) (later : Event), pos ≤ j ∧ bound < later.pc ∧
    X.get (g, j) = some later

theorem PrefixDemand.nonempty {l : Launch} {X : Execution} {g pos bound : Nat}
    {s : TState} {ending : Option TState} (h : PrefixDemand X g pos bound ending)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) :
    (X.tr g).drop pos ≠ [] := by
  intro hEmpty
  rcases h with hDone | ⟨_, _, hBefore, _, hEvent⟩
  · rw [hEmpty, hDone] at hr
    cases hr
  · exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp hEvent).1
      ((List.drop_eq_nil_iff.mp hEmpty).trans hBefore)

theorem PrefixDemand.advance {X : Execution} {g pos bound : Nat} {ending : Option TState}
    (h : PrefixDemand X g pos bound ending) {seen : Event}
    (he : X.get (g, pos) = some seen) (hSite : seen.pc ≤ bound) :
    PrefixDemand X g (pos + 1) bound ending := by
  apply h.imp_right
  rintro ⟨j, later, hBefore, hPc, hGet⟩
  have hNe : pos ≠ j := by
    intro h
    subst j
    obtain rfl := Option.some.inj (he.symm.trans hGet)
    omega
  exact ⟨j, later, by omega, hPc, hGet⟩

theorem PrefixDemand.advanceList {X : Execution} {g pos bound : Nat} {ending : Option TState}
    (h : PrefixDemand X g pos bound ending) {front : List Event}
    (hTrace : (X.tr g).drop pos = front ++ (X.tr g).drop (pos + front.length))
    (hSites : ∀ e ∈ front, e.pc ≤ bound) : PrefixDemand X g (pos + front.length) bound ending := by
  apply h.imp_right
  rintro ⟨j, later, hBefore, hPc, hGet⟩
  refine ⟨j, later, ?_, hPc, hGet⟩
  by_contra hPast
  let k := j - pos
  have hk : k < front.length := by dsimp [k]; omega
  have hEq : pos + k = j := Nat.add_sub_of_le hBefore
  have hr : ((X.tr g).drop pos)[k]? = some later := by rw [List.getElem?_drop, hEq]; exact hGet
  rw [hTrace, List.getElem?_append_left hk] at hr
  exact (Nat.not_le_of_lt hPc) (hSites later (List.mem_of_getElem? hr))

theorem PrefixDemand.weaken {X : Execution} {g pos lower upper : Nat} {ending : Option TState}
    (h : PrefixDemand X g pos upper ending) (hBound : lower ≤ upper) :
    PrefixDemand X g pos lower ending := by
  apply h.imp_right
  rintro ⟨j, later, hj, hPc, he⟩
  exact ⟨j, later, hj, hBound.trans_lt hPc, he⟩

theorem PrefixDemand.eventInSuffix {X : Execution} {g pos bound : Nat} {ending : Option TState}
    (h : PrefixDemand X g pos bound ending) :
    ending = none ∨ ∃ e ∈ (X.tr g).drop pos, bound < e.pc := by
  apply h.imp_right
  rintro ⟨j, later, hj, hPc, he⟩
  refine ⟨later, List.mem_of_getElem? (i := j - pos) ?_, hPc⟩
  rw [List.getElem?_drop, Nat.add_sub_of_le hj]
  exact he

end PTX.Kernels.TmlFa4Fwd.Loader

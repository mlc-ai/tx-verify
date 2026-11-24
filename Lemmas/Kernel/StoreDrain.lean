-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.ExitChain
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! # Lifetime and progress facts for selected tensor-store source drains. -/

namespace PTX

section
variable {select : Nat → Bool} {X Y : Execution}

/-- A monotone extension does not lose a performed tensor-store read completion. -/
theorem Execution.readsDone_mono (hle : X.le Y) {i : EvId}
    (h : X.AsyncPresent i .readsDone) : Y.AsyncPresent i .readsDone := by
  obtain ⟨old, hold, hd⟩ := h
  have hstores : TensorStore.SnapshotExtends X.tensorStores Y.tensorStores :=
    hle.2.2.2.2.2.2.2.2.2.1
  obtain ⟨new, hnew, he⟩ := hstores i old hold
  refine ⟨new, hnew, ?_⟩
  obtain ⟨s, effects⟩ := old
  obtain ⟨s', effects'⟩ := new
  obtain ⟨heq, he⟩ := he
  change s = s' at heq
  subst s'
  exact he.2.2.1 hd

/-- Recording async effects with fixed thread traces preserves the drain condition as soon as
the source read completion flags already present remain present. -/
theorem TensorStore.ReadsDrainedBeforeExit.of_trace
    (h : TensorStore.ReadsDrainedBeforeExit select X) (htrace : Y.tr = X.tr)
    (hp : ∀ i, X.AsyncPresent i .readsDone → Y.AsyncPresent i .readsDone) :
    TensorStore.ReadsDrainedBeforeExit select Y := by
  have hget : Y.get = X.get := by funext i; simp only [Execution.get, htrace]
  intro i finish hb hs he
  apply hp i
  exact h (by simpa only [TraceBefore, htrace] using hb)
    (by simpa only [TensorStore.Selected, hget] using hs) (by simpa only [hget] using he)

/-- Appending a thread event preserves the drain condition when an appended exit has drained
the previously issued selected stores in its trace. A non-exit adds no drain requirement. -/
theorem TensorStore.ReadsDrainedBeforeExit.snoc {g : Nat} {e : Event}
    {rf : Nat → Option AsyncCopy.Ref}
    (h : TensorStore.ReadsDrainedBeforeExit select X)
    (hnew : e.kind = .exit → ∀ i, i.1 = g → TensorStore.Selected select X i →
      X.AsyncPresent i .readsDone) :
    TensorStore.ReadsDrainedBeforeExit select (X.snoc g e rf) := by
  intro i finish hb ⟨site, address, spec, hi, hsite⟩ ⟨pc, he⟩
  have hiOld : i ≠ (g, (X.tr g).length) := by
    intro hEq
    subst i
    have hthread : g = finish.1 := hb.1
    have hlt := hb.2.1
    have hlen := hb.2.2
    rw [snoc_len, ite_eq_left hthread.symm] at hlen
    omega
  rw [snoc_get, ite_eq_right hiOld] at hi
  rw [snoc_get] at he
  change X.AsyncPresent i .readsDone
  split_ifs at he with hfinish
  · subst finish
    exact hnew (congrArg Event.kind (Option.some.inj he)) i hb.1
      ⟨site, address, spec, hi, hsite⟩
  · exact h ⟨hb.1, hb.2.1, len_of_get he⟩ ⟨site, address, spec, hi, hsite⟩ ⟨pc, he⟩

end

/-- A selected tensor store's shared reads are finished before its issuing thread's owner exit. -/
theorem SharedFinished.of_storeReadsDrained {L : Launch} {K : Kernel} {A : List Assumption}
    {X : Execution} {a : Assumption} {i finish : EvId} {c : Nat}
    (ha : a ∈ A) (hb : TraceBefore X i finish)
    (hs : TensorStore.Selected a.storeReadsBeforeExit X i)
    (hx : OwnerExit L X c finish)
    (hd : TensorStore.ReadsDrainedBeforeExit a.storeReadsBeforeExit X) :
    SharedFinished L K A X (.async i .readsDone) c := by
  have hp := hd hb hs hx.2.2
  obtain ⟨site, address, spec, hi, hsite⟩ := hs
  have hselect : A.any (·.storeReadsBeforeExit site) = true :=
    List.any_eq_true.mpr ⟨a, ha, hsite⟩
  exact SharedFinished.of_completedBefore hp hx
    (CompletedBefore.of_storeReadsBeforeExit
      ⟨hb, ⟨site, address, spec, hi, hselect⟩, hx.2.2, hp⟩)

end PTX

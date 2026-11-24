-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.Snoc
public import Lemmas.Snoc.SnocAsyncSilent
public import Lemmas.Snoc.QuietReturnSink
public import Lemmas.Async.AsyncExecution
public import Lemmas.Step.WfInOrder

@[expose] public section

/-! # Appending one event to each of several threads

A proof tool for warp-synchronous collectives (`shfl.sync`, `elect.sync`, `bar.warp.sync`,
`vote.sync`): such an event of one lane is ready only together with the events of the other lanes
of its instance (DEP-ORDER, DEP-WARP-INSTANCE), so a progress step appends one event to each lane
at once. `Execution.appendLanes X ds ev` appends `ev h` to every thread `h` of the list `ds`; for a
list without duplicates it is the appends of the single events one after another
(`appendLanes_cons`), so the one-event lemmas apply
lane by lane. -/

namespace PTX
open AsyncCopy
noncomputable section

/-- The kinds of the warp-synchronous collectives other than the ballot. -/
def Kind.WarpColl : Kind → Prop
  | .elect .. | .warpBar .. | .shfl .. => True
  | _ => False

theorem Kind.WarpColl.ne {k k' : Kind} (hw : k.WarpColl) (hk : ¬ k'.WarpColl) : k ≠ k' :=
  fun h => hk (h ▸ hw)

/-- The kinds of the lane collectives: the warp collectives and synchronized votes
(THREAD-VOTE). A lane's vote is ready together with the votes of the other lanes of its
instance (DEP-ORDER, DEP-WARP-INSTANCE). -/
def Kind.LaneColl : Kind → Prop
  | .elect .. | .warpBar .. | .shfl .. | .vote .. | .voteMode .. => True
  | _ => False

namespace Kind.LaneColl
variable {k : Kind}

theorem of_warpColl (hw : k.WarpColl) : k.LaneColl := by
  cases k <;> simp_all [Kind.WarpColl, Kind.LaneColl]

theorem ne {k' : Kind} (hw : k.LaneColl) (hk : ¬ k'.LaneColl) : k ≠ k' :=
  fun h => hk (h ▸ hw)

theorem asyncSilent (hw : k.LaneColl) : k.AsyncSilent := by
  cases k <;> simp_all [Kind.LaneColl, Kind.AsyncSilent]

theorem quiet (hw : k.LaneColl) : k.quiet = true := by
  cases k <;> simp_all [Kind.LaneColl, Kind.quiet]

theorem counts {e : Event} (hw : e.kind.LaneColl) : e.counts = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> first | exact (hw : False).elim | rfl

end Kind.LaneColl

/-- Append `ev h` to every thread `h` of `ds`; a read of none of the new events. -/
def Execution.appendLanes (X : Execution) (ds : List Nat) (ev : Nat → Event) : Execution :=
  { X with
    tr := fun h => if h ∈ ds then X.tr h ++ [ev h] else X.tr h
    rf := fun v k => match v with
      | .thread i => if i.1 ∈ ds ∧ i.2 = (X.tr i.1).length then none else X.rf v k
      | v => X.rf v k }

section
variable {L : Launch} {X : Execution} {ds : List Nat} {ev : Nat → Event}

theorem appendLanes_nil : X.appendLanes [] ev = X := by
  unfold Execution.appendLanes
  cases X
  simp only [List.not_mem_nil, ↓reduceIte, false_and]
  congr
  funext v k
  cases v <;> rfl

/-- Appending to a further thread is one more single append. -/
theorem appendLanes_cons {h : Nat} (hh : h ∉ ds) :
    X.appendLanes (h :: ds) ev = (X.appendLanes ds ev).snoc h (ev h) (fun _ => none) := by
  unfold Execution.appendLanes Execution.snoc
  simp only [List.mem_cons]
  congr 1
  · funext h'
    by_cases e : h' = h
    · subst e; simp [hh]
    · simp [e]
  · funext v k
    cases v with
    | thread i =>
      obtain ⟨a, b⟩ := i
      by_cases e : a = h
      · subst e; simp [hh]
      · simp [e]
    | «async» i p => simp

theorem appendLanes_tr (h : Nat) :
    (X.appendLanes ds ev).tr h = if h ∈ ds then X.tr h ++ [ev h] else X.tr h := rfl

theorem appendLanes_len (h : Nat) :
    ((X.appendLanes ds ev).tr h).length =
      if h ∈ ds then (X.tr h).length + 1 else (X.tr h).length := by
  rw [appendLanes_tr]; split_ifs <;> simp

theorem appendLanes_get (i : EvId) :
    (X.appendLanes ds ev).get i =
      if i.1 ∈ ds ∧ i.2 = (X.tr i.1).length then some (ev i.1) else X.get i := by
  obtain ⟨h, j⟩ := i
  unfold Execution.get
  simp only [appendLanes_tr]
  by_cases hh : h ∈ ds
  · simp only [hh, ↓reduceIte, true_and]
    rcases Nat.lt_trichotomy j (X.tr h).length with hj | hj | hj
    · rw [List.getElem?_append_left hj, ite_eq_right (by omega)]
    · subst hj; simp
    · rw [ite_eq_right (by omega), List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]
  · simp [hh]

theorem appendLanes_get_old {i : EvId} (hi : i.2 < (X.tr i.1).length) :
    (X.appendLanes ds ev).get i = X.get i := by
  rw [appendLanes_get, ite_eq_right (by omega)]

theorem appendLanes_get_new {h : Nat} (hh : h ∈ ds) :
    (X.appendLanes ds ev).get (h, (X.tr h).length) = some (ev h) := by
  rw [appendLanes_get, ite_eq_left ⟨hh, rfl⟩]

/-- An event of the extension is old or one of the new ones. -/
theorem appendLanes_get_cases {i : EvId} {q : Event} (hq : (X.appendLanes ds ev).get i = some q) :
    (i.2 < (X.tr i.1).length ∧ X.get i = some q) ∨
      (i.1 ∈ ds ∧ i.2 = (X.tr i.1).length ∧ q = ev i.1) := by
  rw [appendLanes_get] at hq
  split_ifs at hq with hn
  · exact .inr ⟨hn.1, hn.2, (Option.some.inj hq).symm⟩
  · exact .inl ⟨len_of_get hq, hq⟩

/-- Appending events that read no memory adds no read. -/
theorem noNewRead_appendLanes (h : ∀ x, (ev x).kind.readsMem = false) :
    X.NoNewRead (X.appendLanes ds ev) := by
  intro i q hq hr
  rcases appendLanes_get_cases hq with ⟨-, hx⟩ | ⟨-, -, rfl⟩
  · exact hx
  · rw [h] at hr
    cases hr

/-- An event of a kind no new event has is old. -/
theorem appendLanes_get_kind {i : EvId} {pc : Nat} {k : Kind}
    (hk : ∀ h ∈ ds, (ev h).kind ≠ k) :
    (X.appendLanes ds ev).get i = some ⟨pc, k⟩ ↔ X.get i = some ⟨pc, k⟩ := by
  constructor
  · intro hq
    rcases appendLanes_get_cases hq with ⟨-, hq⟩ | ⟨hh, -, hq⟩
    · exact hq
    · exact (hk _ hh (by rw [← hq])).elim
  · intro hq
    rw [appendLanes_get_old (len_of_get hq), hq]

theorem appendLanes_take {i : EvId} (hi : i.2 ≤ (X.tr i.1).length) :
    ((X.appendLanes ds ev).tr i.1).take i.2 = (X.tr i.1).take i.2 := by
  rw [appendLanes_tr]
  split_ifs
  · exact List.take_append_of_le_length hi
  · rfl

theorem le_appendLanes : X.le (X.appendLanes ds ev) := by
  have h0 := Execution.le_refl X
  refine ⟨fun h => ?_, ?_, h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2.1,
    h0.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.2.2.1,
    h0.2.2.2.2.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [appendLanes_tr]; split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  · rintro v k ⟨a, bs, hv⟩
    cases v with
    | thread i =>
      obtain ⟨pc, hp⟩ | ⟨new, pc, hp⟩ := hv <;>
      · have hl := len_of_get hp
        change (if i.1 ∈ ds ∧ i.2 = (X.tr i.1).length then none else X.rf _ k) = _
        rw [ite_eq_right (by omega)]
    | «async» i p => rfl

/-- A property that a single append of a lane's event keeps or loses with the old execution
holds of the extension exactly when it holds of the old execution. -/
theorem appendLanes_transport (P : Execution → Prop) (hd : ds.Nodup)
    (hstep : ∀ Z, ∀ h ∈ ds, (P (Z.snoc h (ev h) (fun _ => none)) ↔ P Z)) :
    P (X.appendLanes ds ev) ↔ P X := by
  induction ds with
  | nil => rw [appendLanes_nil]
  | cons h ds ih =>
    rw [appendLanes_cons (List.nodup_cons.mp hd).1, hstep _ h List.mem_cons_self]
    exact ih (List.nodup_cons.mp hd).2 (fun Z h' hm => hstep Z h' (List.mem_cons_of_mem _ hm))

/-- A thread outside `ds` keeps its events. -/
theorem appendLanes_get_of_not_mem {h : Nat} (hh : h ∉ ds) (j : Nat) :
    (X.appendLanes ds ev).get (h, j) = X.get (h, j) := by
  rw [appendLanes_get, ite_eq_right (fun hn => hh hn.1)]

theorem appendLanes_tr_of_not_mem {h : Nat} (hh : h ∉ ds) :
    (X.appendLanes ds ev).tr h = X.tr h := by
  rw [appendLanes_tr, ite_eq_right hh]

/-- An index of the extension is old or a new event. -/
theorem appendLanes_index_cases {i : EvId} (hi : i.2 < ((X.appendLanes ds ev).tr i.1).length) :
    i.2 < (X.tr i.1).length ∨ (i.1 ∈ ds ∧ i.2 = (X.tr i.1).length) := by
  rw [appendLanes_len] at hi
  split_ifs at hi with hh
  · by_cases ho : i.2 < (X.tr i.1).length
    · exact .inl ho
    · exact .inr ⟨hh, by omega⟩
  · exact .inl hi

/-- The extension appends `ds.length` counted events, and no stage of them. -/
theorem size_appendLanes {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hd : ds.Nodup) (hlt : ∀ h ∈ ds, h < L.threads)
    (hc : ∀ h ∈ ds, (ev h).counts = true) :
    (X.appendLanes ds ev).size L = X.size L + ds.length := by
  induction ds with
  | nil => simp [appendLanes_nil]
  | cons h ds ih =>
    have hh := (List.nodup_cons.mp hd).1
    rw [appendLanes_cons hh, size_snoc_of_no_effects (hlt h List.mem_cons_self)
      (hc h List.mem_cons_self),
      ih (List.nodup_cons.mp hd).2 (fun h' hm => hlt h' (List.mem_cons_of_mem _ hm))
        (fun h' hm => hc h' (List.mem_cons_of_mem _ hm))]
    · simp only [List.length_cons]; omega
    · have hl : ((X.appendLanes ds ev).tr h).length = (X.tr h).length := by
        rw [appendLanes_len, ite_eq_right hh]
      rw [hl]
      have he := hX.elem_empty_of_get_none (i := (h, (X.tr h).length))
        (List.getElem?_eq_none (le_refl _))
      have h0 := hX.absent_no_effects (i := (h, (X.tr h).length))
        (List.getElem?_eq_none (le_refl _))
      unfold Execution.asyncSize at h0 ⊢
      rw [Execution.elemSize_eq_zero he] at h0
      rw [Execution.elemSize_eq_zero (X := X.appendLanes ds ev) he]
      exact h0
    · have hl : ((X.appendLanes ds ev).tr h).length = (X.tr h).length := by
        rw [appendLanes_len, ite_eq_right hh]
      rw [hl]
      exact hX.elem_empty_of_get_none (i := (h, (X.tr h).length))
        (List.getElem?_eq_none (le_refl _))

end
end
end PTX

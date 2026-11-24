-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ClusterPhase

@[expose] public section

/-! # One lane of a cluster barrier history

The object lets a lane arrive again once its previous arrival's phase has completed, with or
without a wait (PTX ISA §9.7.15.3), so it does not force a lane's records to alternate. When a
program's order does (`Alt`: an arrival record of the lane is preceded by an even number of the
lane's records and a wait record by an odd number), the lane status follows (`run_laneSt`): after
`a` arrival records and `w` wait records of the lane, `w ≤ a ≤ w + 1`, it has a last arrival exactly
when `a > 0`, and with `a = w > 0` that arrival's phase has completed; so it has not arrived in the
open phase (`LaneSt.not_arrived`). Conversely a warp record is accepted when each of its lanes is
ready: no lane of an arrival arrived in the open phase (`record_arrival_done`), and every lane of a
wait arrived in a completed phase (`record_wait_done`); a warp arrival of ready lanes does not fault
(`record_arrival_fault`), and a warp wait does not fault (`record_wait_fault`). -/

namespace PTX.ClusterLanes
open PTX ClusterBarrier ClusterPhase

/-- Wait records that contain lane `g`. -/
def ownWait {α : Type} (g : Nat) : Record α → Bool
  | .wait _ _ lanes => decide (g ∈ lanes.map Prod.fst)
  | _ => false

/-- The status of lane `x` after `a` arrival and `w` wait records of it. -/
def LaneSt (x : Nat) (s : State) (a w : Nat) : Prop :=
  w ≤ a ∧ a ≤ w + 1 ∧ ((s.lastArrival x).isSome ↔ 0 < a) ∧
    (0 < a → a = w → ∃ p, s.lastArrival x = some p ∧ p < s.phase)

/-- The fields of lane `x`: its last arrival, and the phase never goes back. -/
def Same (x : Nat) (s t : State) : Prop :=
  t.lastArrival x = s.lastArrival x ∧ s.phase ≤ t.phase

theorem Same.trans {x : Nat} {s t u : State} (h1 : Same x s t) (h2 : Same x t u) : Same x s u :=
  ⟨h2.1.trans h1.1, h1.2.trans h2.2⟩

theorem LaneSt.of_same {x a w : Nat} {s t : State} (h : LaneSt x s a w) (hs : Same x s t) :
    LaneSt x t a w := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, by rw [hs.1]; exact h3, fun ha haw => ?_⟩
  obtain ⟨p, hp, hlt⟩ := h4 ha haw
  exact ⟨p, by rw [hs.1]; exact hp, lt_of_lt_of_le hlt hs.2⟩

/-- An arrival of another lane leaves lane `x` alone. -/
theorem perform_arrive_other {threads x j : Nat} {rel : Bool} {s t : State} (hne : x ≠ j)
    (hp : perform threads s (.arrive j rel) = .done t) : Same x s t := by
  refine ⟨?_, perform_phase_le hp⟩
  rw [perform_arrive_eq hp, finish_lastArrival]
  simp [hne]

/-- A wait of another lane leaves lane `x` alone. -/
theorem perform_wait_other {threads x j : Nat} {s t : State}
    (hp : perform threads s (.wait j) = .done t) : Same x s t := by
  have := perform_wait_eq hp
  subst this
  exact ⟨rfl, le_rfl⟩

/-- An exit leaves every lane's fields alone. -/
theorem perform_exit_same {threads x j : Nat} {s t : State}
    (hp : perform threads s (.exit j) = .done t) : Same x s t :=
  ⟨by rw [perform_exit_eq hp, finish_lastArrival], perform_phase_le hp⟩

/-- An arrival of another lane does not make lane `x` arrived. -/
theorem perform_arrive_arrived {threads x j : Nat} {rel : Bool} {s t : State} (hne : x ≠ j)
    (hp : perform threads s (.arrive j rel) = .done t) (hx : x ∈ t.arrived) : x ∈ s.arrived := by
  rw [perform_arrive_eq hp] at hx
  unfold finish at hx
  split at hx
  · simp at hx
  · simpa [hne] using hx

/-- Lane `x`'s own arrival: it now has a last arrival. -/
theorem perform_arrive_own {threads x : Nat} {rel : Bool} {s t : State}
    (hp : perform threads s (.arrive x rel) = .done t) : (t.lastArrival x).isSome := by
  rw [perform_arrive_own_last hp]
  rfl

/-- The arrivals of a warp record: a lane outside it is left alone, and a lane in it now has a
last arrival. -/
theorem performAll_arrive_lane {threads x : Nat} {rel : Bool} {gs : List Nat} {s t : State}
    (hnd : gs.Nodup) (hp : performAll threads s (gs.map fun j => Action.arrive j rel) = .done t) :
    (x ∉ gs → Same x s t) ∧ (x ∈ gs → (t.lastArrival x).isSome) := by
  induction gs generalizing s with
  | nil =>
    cases hp
    exact ⟨fun _ => ⟨rfl, le_rfl⟩, fun h => by cases h⟩
  | cons j gs ih =>
    simp only [List.map_cons, performAll] at hp
    cases hstep : perform threads s (.arrive j rel) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      have hnd' := (List.nodup_cons.mp hnd)
      obtain ⟨ihn, ihm⟩ := ih hnd'.2 hp
      by_cases hxj : x = j
      · subst hxj
        have h3 := perform_arrive_own hstep
        have hs := ihn hnd'.1
        refine ⟨fun h => (h (List.mem_cons_self ..)).elim, fun _ => ?_⟩
        rw [hs.1]; exact h3
      · have hsu := perform_arrive_other hxj hstep
        refine ⟨fun h => hsu.trans (ihn fun h' => h (List.mem_cons_of_mem _ h')), fun h => ?_⟩
        have hm : x ∈ gs := by
          rcases List.mem_cons.mp h with h | h
          · exact (hxj h).elim
          · exact h
        exact ihm hm

/-- The waits of a warp record: a lane outside it is left alone, and a lane in it ends with a
last arrival of a completed phase. -/
theorem performAll_wait_lane {threads x : Nat} {gs : List Nat} {s t : State}
    (hnd : gs.Nodup) (hp : performAll threads s (gs.map fun j => Action.wait j) = .done t) :
    (x ∉ gs → Same x s t) ∧ (x ∈ gs → ∃ q, t.lastArrival x = some q ∧ q < t.phase) := by
  induction gs generalizing s with
  | nil =>
    cases hp
    exact ⟨fun _ => ⟨rfl, le_rfl⟩, fun h => by cases h⟩
  | cons j gs ih =>
    simp only [List.map_cons, performAll] at hp
    cases hstep : perform threads s (.wait j) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      have hnd' := (List.nodup_cons.mp hnd)
      obtain ⟨ihn, ihm⟩ := ih hnd'.2 hp
      have hu := perform_wait_eq hstep
      subst hu
      by_cases hxj : x = j
      · subst hxj
        obtain ⟨p, hp1, hp2⟩ := perform_wait_info hstep
        have hs := ihn hnd'.1
        refine ⟨fun h => (h (List.mem_cons_self ..)).elim, fun _ => ⟨p, ?_, ?_⟩⟩
        · rw [hs.1]; exact hp1
        · exact lt_of_lt_of_le hp2 hs.2
      · refine ⟨fun h => (perform_wait_other (x := x) hstep).trans
          (ihn fun h' => h (List.mem_cons_of_mem _ h')), fun h => ?_⟩
        have hm : x ∈ gs := by
          rcases List.mem_cons.mp h with h | h
          · exact (hxj h).elim
          · exact h
        exact ihm hm

/-- The lane status after one more record, when an arrival of the lane comes after as many of its
waits as arrivals and a wait after one more arrival than waits. -/
theorem record_laneSt {α : Type} {block ctas x a w : Nat} {s t : State} {r : Record α}
    (hst : LaneSt x s a w) (hp : r.perform block ctas s = .done t)
    (hA : ownArrival x r = true → a = w) (hW : ownWait x r = true → a = w + 1) :
    LaneSt x t (a + if ownArrival x r then 1 else 0) (w + if ownWait x r then 1 else 0) := by
  cases r with
  | exit j _ =>
    have hs := perform_exit_same (x := x)
      (show perform (block * ctas) s (.exit j) = .done t from hp)
    simp only [ownArrival, ownWait, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact hst.of_same hs
  | arrival cta warp rel lanes =>
    simp only [Record.perform] at hp
    split at hp
    · rename_i hv
      split at hp
      · cases hp
      have hnd := (of_decide_eq_true hv).2.2.2.2.1
      have hmap : (lanes.map fun p => Action.arrive p.1 rel) =
          (lanes.map Prod.fst).map fun j => Action.arrive j rel := by simp
      rw [hmap] at hp
      obtain ⟨hn, hm⟩ := performAll_arrive_lane (x := x) hnd hp
      simp only [ownWait, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases hx : x ∈ lanes.map Prod.fst
      · have hs := hm hx
        have hown : ownArrival x (Record.arrival cta warp rel lanes : Record α) = true := by
          simp [ownArrival, hx]
        have haw' : a = w := hA hown
        rw [hown]
        simp only [↓reduceIte]
        obtain ⟨hwa, haw, -, -⟩ := hst
        exact ⟨by omega, by omega, ⟨fun _ => by omega, fun _ => hs⟩, fun _ h => by omega⟩
      · have hown : ownArrival x (Record.arrival cta warp rel lanes : Record α) = false := by
          simp [ownArrival, hx]
        rw [hown]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact hst.of_same (hn hx)
    · cases hp
  | wait cta warp lanes =>
    simp only [Record.perform] at hp
    split at hp
    · rename_i hv
      have hnd := (of_decide_eq_true hv).2.2.2.2.1
      have hmap : (lanes.map fun p => Action.wait p.1) =
          (lanes.map Prod.fst).map fun j => Action.wait j := by simp
      rw [hmap] at hp
      obtain ⟨hn, hm⟩ := performAll_wait_lane (x := x) hnd hp
      simp only [ownArrival, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases hx : x ∈ lanes.map Prod.fst
      · obtain ⟨q, hq, hqlt⟩ := hm hx
        have hown : ownWait x (Record.wait cta warp lanes : Record α) = true := by
          simp [ownWait, hx]
        have haw' : a = w + 1 := hW hown
        rw [hown]
        simp only [↓reduceIte]
        exact ⟨by omega, by omega, ⟨fun _ => by omega, fun _ => by rw [hq]; rfl⟩,
          fun _ _ => ⟨q, hq, hqlt⟩⟩
      · have hown : ownWait x (Record.wait cta warp lanes : Record α) = false := by
          simp [ownWait, hx]
        rw [hown]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact hst.of_same (hn hx)
    · cases hp

/-- Records that contain lane `g`, as an arrival or as a wait. -/
def ownAny {α : Type} (g : Nat) (r : Record α) : Bool := ownArrival g r || ownWait g r

theorem countP_ownAny {α : Type} (g : Nat) (h : List (Record α)) :
    h.countP (ownAny g) = h.countP (ownArrival g) + h.countP (ownWait g) := by
  induction h with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.countP_cons, ih]
    cases r with
    | exit j e => simp [ownAny, ownArrival, ownWait]
    | arrival cta warp rel lanes =>
      by_cases hg : g ∈ lanes.map Prod.fst <;> simp [ownAny, ownArrival, ownWait, hg]; omega
    | wait cta warp lanes =>
      by_cases hg : g ∈ lanes.map Prod.fst <;> simp [ownAny, ownArrival, ownWait, hg]; omega

/-- **The program alternates the lane's records**: an arrival record of lane `x` comes after an
even number of the lane's records, and a wait record after an odd number. -/
def Alt {α : Type} (x : Nat) (h : List (Record α)) : Prop :=
  ∀ i r, h[i]? = some r →
    (ownArrival x r = true → (h.take i).countP (ownAny x) % 2 = 0) ∧
    (ownWait x r = true → (h.take i).countP (ownAny x) % 2 = 1)

/-- **The lane status of alternating records**: after a checked run, the lane status holds with
the lane's arrival and wait records. -/
theorem run_laneSt {α : Type} {block ctas x : Nat} {s : State} {h : List (Record α)}
    (hp : run block ctas {} h = .done s) (halt : Alt x h) :
    LaneSt x s (h.countP (ownArrival x)) (h.countP (ownWait x)) := by
  suffices ∀ k (u : State), k ≤ h.length → run block ctas {} (h.take k) = .done u →
      LaneSt x u ((h.take k).countP (ownArrival x)) ((h.take k).countP (ownWait x)) by
    have := this h.length s le_rfl (by rw [List.take_length]; exact hp)
    rwa [List.take_length] at this
  intro k
  induction k with
  | zero =>
    intro u _ hu
    simp only [List.take_zero, run] at hu
    cases hu
    simp [LaneSt]
  | succ k ih =>
    intro u hk hu
    have hget : h[k]? = some h[k] := List.getElem?_eq_getElem (by omega)
    have htk : h.take (k + 1) = h.take k ++ [h[k]] := by
      rw [List.take_add_one, hget, Option.toList_some]
    rw [htk, run_append] at hu
    rw [htk, List.countP_append, List.countP_append, List.countP_singleton,
      List.countP_singleton]
    cases hpre : run block ctas {} (h.take k) with
    | blocked => rw [hpre] at hu; cases hu
    | fault e => rw [hpre] at hu; cases hu
    | done v =>
      rw [hpre] at hu
      have hv := ih v (by omega) hpre
      have hstep : h[k].perform block ctas v = .done u := by
        simp only [run] at hu
        cases hq : h[k].perform block ctas v with
        | done w => rw [hq] at hu; cases hu; rfl
        | blocked => rw [hq] at hu; cases hu
        | fault e => rw [hq] at hu; cases hu
      have h2 := halt k h[k] hget
      rw [countP_ownAny] at h2
      have := hv.1
      have := hv.2.1
      exact record_laneSt hv hstep (fun hown => by have := h2.1 hown; omega)
        (fun hown => by have := h2.2 hown; omega)

/-- A lane with as many waits as arrivals has not arrived in the open phase. -/
theorem LaneSt.not_arrived {x a : Nat} {s : State} (hs : Sound s) (h : LaneSt x s a a) :
    x ∉ s.arrived := by
  intro hx
  have hlast := hs.1 x hx
  obtain ⟨-, -, hl, h4⟩ := h
  have ha : 0 < a := hl.mp (by rw [hlast]; rfl)
  obtain ⟨p, hp, hlt⟩ := h4 ha rfl
  rw [hlast] at hp
  have := Option.some.inj hp
  omega

/-! ## Accepting a warp record -/

/-- The arrivals of ready lanes are performed. -/
theorem performAll_arrive_done {threads : Nat} {rel : Bool} {gs : List Nat} {s : State}
    (hnd : gs.Nodup) (hok : ∀ j ∈ gs, j < threads ∧ j ∉ s.exited ∧ ¬ Locked j s) :
    ∃ t, performAll threads s (gs.map fun j => Action.arrive j rel) = .done t := by
  induction gs generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons j gs ih =>
    obtain ⟨hj, hje, hjl⟩ := hok j (List.mem_cons_self ..)
    have hstep : perform threads s (.arrive j rel) = .done (finish threads { s with
        arrived := insert j s.arrived
        lastArrival := fun h => if h = j then some s.phase else s.lastArrival h }) := by
      have hjl' : j ∉ s.arrived := hjl
      simp only [perform, hj, hje, hjl', not_true_eq_false, and_true, not_false_eq_true,
        ↓reduceIte]
    simp only [List.map_cons, performAll, hstep]
    apply ih (List.nodup_cons.mp hnd).2
    intro k hk
    have hkj : k ≠ j := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hk)
    obtain ⟨h1, h2, h3⟩ := hok k (List.mem_cons_of_mem _ hk)
    refine ⟨h1, ?_, fun hl => h3 (perform_arrive_arrived hkj hstep hl)⟩
    rw [finish_exited]
    exact h2

/-- Arrivals of lanes that have not arrived in the open phase fail only on a bad lane. -/
theorem performAll_arrive_fault {threads : Nat} {rel : Bool} {gs : List Nat} {s : State}
    {err : Error} (hnd : gs.Nodup) (hok : ∀ j ∈ gs, ¬ Locked j s)
    (hp : performAll threads s (gs.map fun j => Action.arrive j rel) = .fault err) :
    err.isFault = false := by
  induction gs generalizing s with
  | nil => cases hp
  | cons j gs ih =>
    simp only [List.map_cons, performAll] at hp
    cases hstep : perform threads s (.arrive j rel) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e =>
      rw [hstep] at hp
      cases hp
      simp only [perform] at hstep
      split at hstep
      · cases hstep; rfl
      · split at hstep
        · rename_i hin
          exact (hok j (List.mem_cons_self ..) hin).elim
        · cases hstep
    | done u =>
      rw [hstep] at hp
      have hnd' := List.nodup_cons.mp hnd
      refine ih hnd'.2 (fun k hk hl => ?_) hp
      have hkj : k ≠ j := fun h => hnd'.1 (h ▸ hk)
      exact hok k (List.mem_cons_of_mem _ hk) (perform_arrive_arrived hkj hstep hl)

/-- A wait fails only on a bad lane. -/
theorem performAll_wait_fault {threads : Nat} {gs : List Nat} {s : State} {err : Error}
    (hp : performAll threads s (gs.map fun j => Action.wait j) = .fault err) :
    err.isFault = false := by
  induction gs generalizing s with
  | nil => cases hp
  | cons j gs ih =>
    simp only [List.map_cons, performAll] at hp
    cases hstep : perform threads s (.wait j) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e =>
      rw [hstep] at hp
      cases hp
      simp only [perform] at hstep
      repeat' split at hstep
      all_goals first
        | (cases hstep; rfl)
        | (cases hstep)
    | done u =>
      rw [hstep] at hp
      exact ih hp

/-- A warp arrival record none of whose lanes arrived in the open phase does not fault. -/
theorem record_arrival_fault {α : Type} {block ctas cta warp : Nat} {rel : Bool}
    {lanes : List (Nat × α)} {s : State} {err : Error}
    (hok : ∀ j ∈ lanes.map Prod.fst, ¬ Locked j s)
    (hp : Record.perform block ctas s (.arrival cta warp rel lanes) = .fault err) :
    err.isFault = false := by
  simp only [Record.perform] at hp
  split at hp
  · rename_i hv
    have hany : (lanes.any fun p => decide (p.1 ∈ s.arrived)) = false :=
      List.any_eq_false.mpr fun p hp hd =>
      hok p.1 (List.mem_map_of_mem hp) (show p.1 ∈ s.arrived from of_decide_eq_true hd)
    rw [hany] at hp
    have hmap : (lanes.map fun p => Action.arrive p.1 rel) =
        (lanes.map Prod.fst).map fun j => Action.arrive j rel := by simp
    simp only [Bool.false_eq_true, ↓reduceIte] at hp
    rw [hmap] at hp
    exact performAll_arrive_fault (of_decide_eq_true hv).2.2.2.2.1 hok hp
  · cases hp; rfl

/-- A warp wait record does not fault. -/
theorem record_wait_fault {α : Type} {block ctas cta warp : Nat} {lanes : List (Nat × α)}
    {s : State} {err : Error}
    (hp : Record.perform block ctas s (.wait cta warp lanes) = .fault err) :
    err.isFault = false := by
  simp only [Record.perform] at hp
  split at hp
  · rw [show (lanes.map fun p => Action.wait p.1) =
        (lanes.map Prod.fst).map fun j => Action.wait j by simp] at hp
    exact performAll_wait_fault hp
  · cases hp; rfl

/-- The waits of lanes that arrived in a completed phase are performed. -/
theorem performAll_wait_done {threads : Nat} {gs : List Nat} {s : State} (hnd : gs.Nodup)
    (hok : ∀ j ∈ gs, j < threads ∧ j ∉ s.exited ∧ ∃ p, s.lastArrival j = some p ∧ p < s.phase) :
    ∃ t, performAll threads s (gs.map fun j => Action.wait j) = .done t := by
  induction gs generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons j gs ih =>
    obtain ⟨hj, hje, p, hp, hlt⟩ := hok j (List.mem_cons_self ..)
    have hstep : perform threads s (.wait j) = .done s := wait_completed hj hje hp hlt
    simp only [List.map_cons, performAll, hstep]
    exact ih (List.nodup_cons.mp hnd).2 fun k hk => hok k (List.mem_cons_of_mem _ hk)

/-- An arrival record of a live warp none of whose lanes arrived in the open phase is
performed. -/
theorem record_arrival_done {α : Type} {block ctas cta warp : Nat} {rel : Bool}
    {lanes : List (Nat × α)} {s : State}
    (hv : liveWarp block ctas s cta warp (lanes.map Prod.fst) = true)
    (hok : ∀ j ∈ lanes.map Prod.fst, ¬ Locked j s) :
    ∃ t, Record.perform block ctas s (.arrival cta warp rel lanes) = .done t := by
  have hv' := of_decide_eq_true hv
  have hany : (lanes.any fun p => decide (p.1 ∈ s.arrived)) = false :=
    List.any_eq_false.mpr fun p hp hd =>
      hok p.1 (List.mem_map_of_mem hp) (show p.1 ∈ s.arrived from of_decide_eq_true hd)
  simp only [Record.perform, hv, hany, Bool.false_eq_true, ↓reduceIte]
  have hmap : (lanes.map fun p => Action.arrive p.1 rel) =
      (lanes.map Prod.fst).map fun j => Action.arrive j rel := by simp
  rw [hmap]
  exact performAll_arrive_done hv'.2.2.2.2.1 fun j hj =>
    ⟨(hv'.2.2.2.2.2.1 j hj).1, (hv'.2.2.2.2.2.1 j hj).2.2.2, hok j hj⟩

/-- A wait record of a live warp whose lanes arrived in a completed phase is performed. -/
theorem record_wait_done {α : Type} {block ctas cta warp : Nat} {lanes : List (Nat × α)}
    {s : State} (hv : liveWarp block ctas s cta warp (lanes.map Prod.fst) = true)
    (hok : ∀ j ∈ lanes.map Prod.fst, ∃ p, s.lastArrival j = some p ∧ p < s.phase) :
    ∃ t, Record.perform block ctas s (.wait cta warp lanes) = .done t := by
  have hv' := of_decide_eq_true hv
  simp only [Record.perform, hv, ↓reduceIte]
  have hmap : (lanes.map fun p => Action.wait p.1) =
      (lanes.map Prod.fst).map fun j => Action.wait j := by simp
  rw [hmap]
  exact performAll_wait_done hv'.2.2.2.2.1 fun j hj =>
    ⟨(hv'.2.2.2.2.2.1 j hj).1, (hv'.2.2.2.2.2.1 j hj).2.2.2, hok j hj⟩

/-! ## Lanes of one warp -/

/-- **A live lane is in every record of its warp**: every record that contains lane `x` also
contains lane `y` of the same warp, when `y` has not exited by the end of the run. -/
theorem countP_ownAny_le {α : Type} {block ctas x y : Nat} {s : State} {h : List (Record α)}
    (hp : run block ctas {} h = .done s) (hcta : x / block = y / block)
    (hw : x % block / 32 = y % block / 32) (hy : y ∉ s.exited) :
    h.countP (ownAny x) ≤ h.countP (ownAny y) := by
  apply List.countP_mono_left
  intro r hr hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨u, v, hu, hv⟩ := run_perform_at hp hi
  have hrest : run block ctas u (h.drop i) = .done s := by
    have := hp
    rw [← List.take_append_drop i h, run_append, hu] at this
    exact this
  have hyu : y ∉ u.exited := run_live hrest hy
  -- the warp's liveness check puts `y` in the record
  have key : ∀ (cta warp : Nat) (gs : List Nat), liveWarp block ctas u cta warp gs = true →
      x ∈ gs → y ∈ gs := by
    intro cta warp gs hlw hxg
    have hl := of_decide_eq_true hlw
    obtain ⟨hb, -, -, -, -, hall, hcomp⟩ := hl
    obtain ⟨-, hxc, hxw, -⟩ := hall x hxg
    have hlane := hcomp (y % block % 32) (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
    have hloc : warp * 32 + y % block % 32 = y % block := by
      have := Nat.div_add_mod (y % block) 32
      rw [← hxw, hw]
      omega
    simp only [hloc] at hlane
    have hy' : cta * block + y % block = y := by
      have := Nat.div_add_mod y block
      rw [← hxc, hcta]
      rw [Nat.mul_comm]
      omega
    rw [hy'] at hlane
    exact hlane (Nat.mod_lt _ hb) hyu
  cases r with
  | exit j e => simp [ownAny, ownArrival, ownWait] at hx
  | arrival cta warp rel lanes =>
    simp only [Record.perform] at hv
    split at hv
    · rename_i hlw
      have hxg : x ∈ lanes.map Prod.fst := by simpa [ownAny, ownArrival, ownWait] using hx
      simpa [ownAny, ownArrival, ownWait] using key cta warp _ hlw hxg
    · cases hv
  | wait cta warp lanes =>
    simp only [Record.perform] at hv
    split at hv
    · rename_i hlw
      have hxg : x ∈ lanes.map Prod.fst := by simpa [ownAny, ownArrival, ownWait] using hx
      simpa [ownAny, ownArrival, ownWait] using key cta warp _ hlw hxg
    · cases hv

end PTX.ClusterLanes

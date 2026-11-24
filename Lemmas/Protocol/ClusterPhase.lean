-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Cluster.ClusterFirstPhase
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Order.DependencyWitness
public import Lemmas.Protocol.CountNth

@[expose] public section

/-! # Phase counts of a cluster barrier

For one cluster barrier, the object phase at a successful arrival of a lane equals the number of
arrival records that lane has already made. A completed wait that observes phase `n` therefore
forces every live participant to have at least `n + 1` earlier arrival records, while a participant
that has exited has all of its arrival records before its exit. The `n`-th generation arrival of a
live participant precedes the wait, and a release arrival of that generation orders the
participant's earlier events before the waiter's later events. Only the record sequence of a
cluster, its checked run and the cluster-local lane of each thread are used. -/

namespace PTX.ClusterPhase
open PTX ClusterBarrier

/-! ## Object counting -/

/-- Generation count of lane `g`: completed generations plus its arrival in the open one. -/
def weight (g : Nat) (s : State) : Nat := s.phase + (if g ∈ s.arrived then 1 else 0)

/-- Units of lane `g`'s own arrival performed by one action. -/
def actionUnits (g : Nat) : Action → Nat
  | .arrive j _ => if g = j then 1 else 0
  | _ => 0

/-- Arrival records that contain lane `g`. -/
def ownArrival {α : Type} (g : Nat) : Record α → Bool
  | .arrival _ _ _ lanes => decide (g ∈ lanes.map Prod.fst)
  | _ => false

theorem finish_weight {threads g : Nat} {s : State}
    (hg : g < threads) (hlive : g ∉ s.exited) : weight g (finish threads s) = weight g s := by
  unfold finish
  split
  · rename_i hall
    have ha : g ∈ s.arrived := (hall g (Finset.mem_range.mpr hg)).resolve_right hlive
    simp [weight, ha]
  · rfl

theorem perform_live {threads g : Nat} {s t : State} {a : Action}
    (hp : perform threads s a = .done t) (hlive : g ∉ t.exited) : g ∉ s.exited := by
  cases a with
  | arrive j _ =>
    rw [perform_arrive_eq hp, finish_exited] at hlive
    exact hlive
  | wait j =>
    rw [perform_wait_eq hp] at hlive
    exact hlive
  | exit j =>
    rw [perform_exit_eq hp, finish_exited] at hlive
    exact fun h => hlive (Finset.mem_insert_of_mem h)

theorem perform_weight {threads g : Nat} {s t : State} {a : Action}
    (_hs : Sound s) (hp : perform threads s a = .done t)
    (hg : g < threads) (hlive : g ∉ t.exited) :
    weight g t = weight g s + actionUnits g a := by
  cases a with
  | arrive j _ =>
    have hslive := perform_live hp hlive
    have hnot := perform_arrive_not_locked hp
    rw [perform_arrive_eq hp,
      finish_weight (s := { s with
        arrived := insert j s.arrived
        lastArrival := fun h => if h = j then some s.phase else s.lastArrival h }) hg hslive]
    by_cases heq : g = j
    · subst j
      have hna : g ∉ s.arrived := fun ha => hnot ha
      simp [weight, actionUnits, hna]
    · simp [weight, actionUnits, heq]
  | wait j =>
    rw [perform_wait_eq hp]
    simp only [weight, actionUnits, Nat.add_zero]
  | exit j =>
    have ht := hlive
    rw [perform_exit_eq hp, finish_exited] at ht
    rw [perform_exit_eq hp, finish_weight (s := { s with exited := insert j s.exited }) hg ht]
    simp only [weight, actionUnits, Nat.add_zero]

theorem performAll_live {threads g : Nat} {s t : State} {actions : List Action}
    (hp : performAll threads s actions = .done t) (hlive : g ∉ t.exited) : g ∉ s.exited :=
  performAll_lift (R := fun s t => g ∉ t.exited → g ∉ s.exited) (fun _ h => h)
    (fun h1 h2 h => h1 (h2 h)) (fun _ _ _ _ hp => perform_live hp) hp hlive

theorem performAll_weight {threads g : Nat} {s t : State} {actions : List Action}
    (hs : Sound s) (hp : performAll threads s actions = .done t)
    (hg : g < threads) (hlive : g ∉ t.exited) :
    weight g t = weight g s + (actions.map (actionUnits g)).sum := by
  induction actions generalizing s with
  | nil => cases hp; simp
  | cons a actions ih =>
    simp only [performAll] at hp
    cases hstep : perform threads s a with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      rw [ih (sound_perform hs hstep) hp, perform_weight hs hstep hg (performAll_live hp hlive)]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem sum_indicator {g : Nat} {gs : List Nat} (hnd : gs.Nodup) :
    (gs.map (fun j => if g = j then 1 else 0)).sum = if g ∈ gs then 1 else 0 := by
  induction gs with
  | nil => simp
  | cons j gs ih =>
    have hd := List.nodup_cons.mp hnd
    rw [List.map_cons, List.sum_cons, ih hd.2]
    by_cases he : g = j
    · subst j
      simp [hd.1]
    · simp [he]

theorem record_weight {α : Type} {block ctas g : Nat} {s t : State} {r : Record α}
    (hs : Sound s) (hp : r.perform block ctas s = .done t)
    (hg : g < block * ctas) (hlive : g ∉ t.exited) :
    weight g t = weight g s + (if ownArrival g r then 1 else 0) := by
  cases r with
  | exit j _ =>
    change perform (block * ctas) s (.exit j) = .done t at hp
    simpa [ownArrival, actionUnits] using perform_weight hs hp hg hlive
  | wait cta warp lanes =>
    simp only [Record.perform] at hp
    split at hp
    · have hm := performAll_weight hs hp hg hlive
      simpa [List.map_map, Function.comp_def, actionUnits, ownArrival] using hm
    · cases hp
  | arrival cta warp release lanes =>
    simp only [Record.perform] at hp
    split at hp
    · rename_i hv
      split at hp
      · cases hp
      have hd := (of_decide_eq_true hv).2.2.2.2.1
      have hm := performAll_weight hs hp hg hlive
      have hsum := sum_indicator (g := g) hd
      simp only [List.map_map, Function.comp_def, actionUnits] at hm hsum
      rw [hsum] at hm
      simpa only [ownArrival, decide_eq_true_eq] using hm
    · cases hp

theorem run_live {α : Type} {block ctas g : Nat} {s t : State} {h : List (Record α)}
    (hp : run block ctas s h = .done t) (hlive : g ∉ t.exited) : g ∉ s.exited :=
  run_lift (R := fun s t => g ∉ t.exited → g ∉ s.exited) (fun _ h => h)
    (fun h1 h2 h => h1 (h2 h)) (fun _ _ _ _ _ _ hp => perform_live hp) hp hlive

theorem run_exited_mono {α : Type} {block ctas g : Nat} {s t : State} {h : List (Record α)}
    (hp : run block ctas s h = .done t) (hg : g ∈ s.exited) : g ∈ t.exited := by
  by_contra hn
  exact run_live hp hn hg

theorem run_weight {α : Type} {block ctas g : Nat} {s t : State} {h : List (Record α)}
    (hs : Sound s) (hp : run block ctas s h = .done t)
    (hg : g < block * ctas) (hlive : g ∉ t.exited) :
    weight g t = weight g s + h.countP (ownArrival g) := by
  induction h generalizing s with
  | nil => cases hp; simp
  | cons r rs ih =>
    simp only [run] at hp
    cases hstep : r.perform block ctas s with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      rw [ih (sound_record hs hstep) hp, record_weight hs hstep hg (run_live hp hlive)]
      cases hsel : ownArrival g r <;> simp [hsel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Any successful arrival of lane `g` has object phase equal to the number of arrival
records of `g` before it. Other lanes may already have exited; they do not change this count. -/
theorem arrival_phase_count {α : Type} {block ctas g i cta warp : Nat}
    {h : List (Record α)} {lanes : List (Nat × α)} {e : α} {release : Bool}
    {s t : State} (hs : At block ctas h i s) (he : (g, e) ∈ lanes)
    (hp : Record.perform block ctas s (.arrival cta warp release lanes) = .done t) :
    s.phase = (h.take i).countP (ownArrival g) := by
  have hsound := sound_run sound_empty hs
  have hnotall := record_arrive_not_locked hp
  simp only [Record.perform] at hp
  split at hp
  · rename_i hv
    have hvalid := of_decide_eq_true hv
    have hgmem : g ∈ lanes.map Prod.fst := List.mem_map.mpr ⟨(g, e), he, rfl⟩
    have hglive := hvalid.2.2.2.2.2.1 g hgmem
    have hna : g ∉ s.arrived := hnotall g hgmem
    have hcount := run_weight sound_empty hs hglive.1 hglive.2.2.2
    simpa [weight, hna] using hcount
  · cases hp

/-- A completed wait observing phase `phase` has passed it: the object phase is strictly larger. -/
theorem wait_phase_lt {α : Type} {block ctas g phase cta warp : Nat} {s t : State}
    {lanes : List (Nat × α)} {e : α}
    (he : (g, e) ∈ lanes) (hphase : s.lastArrival g = some phase)
    (hp : Record.perform block ctas s (.wait cta warp lanes) = .done t) : phase < s.phase := by
  simp only [Record.perform] at hp
  split at hp
  · have hh : performAll (block * ctas) s ((lanes.map Prod.fst).map Action.wait) = .done t := by
      simpa only [List.map_map, Function.comp_def] using hp
    have hm : g ∈ lanes.map Prod.fst := List.mem_map.mpr ⟨(g, e), he, rfl⟩
    obtain ⟨p, hp', hlt⟩ := performAll_wait_info hh g hm
    have heq : p = phase := Option.some.inj (hp'.symm.trans hphase)
    omega
  · cases hp

/-- The last arrival generation of lane `g` is one less than its generation count. -/
def LastCount (g : Nat) (s : State) : Prop :=
  s.lastArrival g = if weight g s = 0 then none else some (weight g s - 1)

theorem perform_last_count {threads g : Nat} {s t : State} {a : Action}
    (hs : Sound s) (hc : LastCount g s) (hp : perform threads s a = .done t)
    (hg : g < threads) (hlive : g ∉ t.exited) : LastCount g t := by
  cases a with
  | arrive j _ =>
    have hw := perform_weight hs hp hg hlive
    by_cases heq : g = j
    · subst j
      have hn : g ∉ s.arrived := fun ha => perform_arrive_not_locked hp ha
      have hlast := perform_arrive_own_last hp
      simp [actionUnits] at hw
      unfold LastCount
      rw [hlast, hw]
      simp [weight, hn]
    · have hlast := perform_arrive_other_last heq hp
      simp [actionUnits, heq] at hw
      unfold LastCount at hc ⊢
      rwa [hlast, hw]
  | wait j =>
    rw [perform_wait_eq hp]
    exact hc
  | exit j =>
    have hw := perform_weight hs hp hg hlive
    simp only [actionUnits, Nat.add_zero] at hw
    unfold LastCount at hc ⊢
    have hla : t.lastArrival = s.lastArrival := by
      rw [perform_exit_eq hp, finish_lastArrival]
    rw [hw, hla]
    exact hc

theorem performAll_last_count {threads g : Nat} {s t : State} {actions : List Action}
    (hs : Sound s) (hc : LastCount g s) (hp : performAll threads s actions = .done t)
    (hg : g < threads) (hlive : g ∉ t.exited) : LastCount g t := by
  induction actions generalizing s with
  | nil => cases hp; exact hc
  | cons a actions ih =>
    simp only [performAll] at hp
    cases hstep : perform threads s a with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      exact ih (sound_perform hs hstep)
        (perform_last_count hs hc hstep hg (performAll_live hp hlive)) hp

theorem record_last_count {α : Type} {block ctas g : Nat} {s t : State} {r : Record α}
    (hs : Sound s) (hc : LastCount g s) (hp : r.perform block ctas s = .done t)
    (hg : g < block * ctas) (hlive : g ∉ t.exited) : LastCount g t := by
  cases r with
  | exit j _ =>
    change perform (block * ctas) s (.exit j) = .done t at hp
    exact perform_last_count hs hc hp hg hlive
  | arrival cta warp release lanes =>
    simp only [Record.perform] at hp
    split at hp
    · split at hp
      · cases hp
      exact performAll_last_count hs hc hp hg hlive
    · cases hp
  | wait cta warp lanes =>
    simp only [Record.perform] at hp
    split at hp
    · exact performAll_last_count hs hc hp hg hlive
    · cases hp

theorem run_last_count {α : Type} {block ctas g : Nat} {s t : State} {h : List (Record α)}
    (hs : Sound s) (hc : LastCount g s) (hp : run block ctas s h = .done t)
    (hg : g < block * ctas) (hlive : g ∉ t.exited) : LastCount g t := by
  induction h generalizing s with
  | nil => cases hp; exact hc
  | cons r rs ih =>
    simp only [run] at hp
    cases hstep : r.perform block ctas s with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      exact ih (sound_record hs hstep) (record_last_count hs hc hstep hg (run_live hp hlive)) hp

/-- A completed wait observing phase `n` in lane `g` has exactly `n + 1` arrival records of
lane `g` before it. -/
theorem wait_phase_count {α : Type} {block ctas g i cta warp phase : Nat}
    {h : List (Record α)} {lanes : List (Nat × α)} {e : α} {s t : State}
    (hs : At block ctas h i s) (he : (g, e) ∈ lanes)
    (hphase : s.lastArrival g = some phase)
    (hp : Record.perform block ctas s (.wait cta warp lanes) = .done t) :
    (h.take i).countP (ownArrival g) = phase + 1 := by
  have hsound := sound_run sound_empty hs
  have hlt := wait_phase_lt he hphase hp
  simp only [Record.perform] at hp
  split at hp
  · rename_i hv
    have hgmem : g ∈ lanes.map Prod.fst := List.mem_map.mpr ⟨(g, e), he, rfl⟩
    have hglive := (of_decide_eq_true hv).2.2.2.2.2.1 g hgmem
    have hna : g ∉ s.arrived := by
      intro ha
      have hv' := hsound.1 g ha
      rw [hphase] at hv'
      have heq := Option.some.inj hv'
      omega
    have hlc := run_last_count sound_empty (by simp [LastCount, weight]) hs hglive.1 hglive.2.2.2
    have hcount := run_weight sound_empty hs hglive.1 hglive.2.2.2
    simp only [LastCount, hphase, weight, hna, Nat.add_zero, ↓reduceIte] at hlc
    rw [ite_eq_right (show ¬ s.phase = 0 by omega)] at hlc
    have heq := Option.some.inj hlc
    simp [weight, hna] at hcount
    omega
  · cases hp

/-- A completed wait observing phase `n` in lane `w` forces every live lane `g` to have at
least `n + 1` arrival records before the wait. The lanes that have exited are excluded. -/
theorem wait_forces_count {α : Type} {block ctas g i cta warp phase w : Nat}
    {h : List (Record α)} {lanes : List (Nat × α)} {e : α} {s t : State}
    (hs : At block ctas h i s) (he : (w, e) ∈ lanes)
    (hphase : s.lastArrival w = some phase)
    (hp : Record.perform block ctas s (.wait cta warp lanes) = .done t)
    (hg : g < block * ctas) (hlive : g ∉ s.exited) :
    phase + 1 ≤ (h.take i).countP (ownArrival g) := by
  have hlt := wait_phase_lt he hphase hp
  have hw := run_weight sound_empty hs hg hlive
  have h0 : weight g ({} : State) = 0 := by simp [weight]
  have h2 : s.phase ≤ weight g s := by unfold weight; omega
  omega

/-- A recorded step of a successful run is performed from the state of its prefix. -/
theorem run_perform_at {α : Type} {block ctas : Nat} {s t : State} {h : List (Record α)}
    {k : Nat} {r : Record α} (hrun : run block ctas s h = .done t) (hk : h[k]? = some r) :
    ∃ u v, run block ctas s (h.take k) = .done u ∧ r.perform block ctas u = .done v := by
  induction h generalizing s k with
  | nil => simp at hk
  | cons q qs ih =>
    simp only [run] at hrun
    cases hstep : q.perform block ctas s with
    | blocked => rw [hstep] at hrun; cases hrun
    | fault e => rw [hstep] at hrun; cases hrun
    | done u =>
      rw [hstep] at hrun
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact ⟨s, u, rfl, hstep⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨u', v', hu', hv'⟩ := ih hrun hk
        refine ⟨u', v', ?_, hv'⟩
        simp only [List.take_succ_cons, run, hstep]
        exact hu'

theorem perform_arrive_exited {threads j : Nat} {s t : State} {release : Bool}
    (hp : perform threads s (.arrive j release) = .done t) : t.exited = s.exited := by
  rw [perform_arrive_eq hp, finish_exited]

theorem performAll_arrive_exited {threads : Nat} {s t : State} {release : Bool} {gs : List Nat}
    (hp : performAll threads s (gs.map (fun j => Action.arrive j release)) = .done t) :
    t.exited = s.exited := by
  induction gs generalizing s with
  | nil => cases hp; rfl
  | cons j gs ih =>
    simp only [List.map_cons, performAll] at hp
    cases hstep : perform threads s (.arrive j release) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u => rw [hstep] at hp; exact (ih hp).trans (perform_arrive_exited hstep)

theorem performAll_wait_exited {threads : Nat} {s t : State} {gs : List Nat}
    (hp : performAll threads s (gs.map Action.wait) = .done t) : t.exited = s.exited := by
  induction gs generalizing s with
  | nil => cases hp; rfl
  | cons j gs ih =>
    simp only [List.map_cons, performAll] at hp
    cases hstep : perform threads s (.wait j) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u => rw [hstep] at hp; exact (ih hp).trans (by rw [perform_wait_eq hstep])

theorem record_exited_source {α : Type} {block ctas g : Nat} {s t : State} {r : Record α}
    (hp : r.perform block ctas s = .done t) (hexit : g ∈ t.exited) :
    g ∈ s.exited ∨ ∃ e, r = .exit g e := by
  cases r with
  | exit j e =>
    change perform (block * ctas) s (.exit j) = .done t at hp
    rw [perform_exit_eq hp, finish_exited] at hexit
    rcases Finset.mem_insert.mp hexit with heq | he
    · subst j
      exact .inr ⟨e, rfl⟩
    · exact .inl he
  | arrival cta warp release lanes =>
    left
    simp only [Record.perform] at hp
    split at hp
    · split at hp
      · cases hp
      have hh : performAll (block * ctas) s
          ((lanes.map Prod.fst).map (fun j => Action.arrive j release)) = .done t := by
        simpa only [List.map_map, Function.comp_def] using hp
      rwa [performAll_arrive_exited hh] at hexit
    · cases hp
  | wait cta warp lanes =>
    left
    simp only [Record.perform] at hp
    split at hp
    · have hh : performAll (block * ctas) s ((lanes.map Prod.fst).map Action.wait) = .done t := by
        simpa only [List.map_map, Function.comp_def] using hp
      rwa [performAll_wait_exited hh] at hexit
    · cases hp

/-- A lane exited at the end of a successful run either had already exited at its start, or
has an exit record in the run. -/
theorem run_exited_source {α : Type} {block ctas g : Nat} {s t : State} {h : List (Record α)}
    (hp : run block ctas s h = .done t) (hexit : g ∈ t.exited) :
    g ∈ s.exited ∨ ∃ e, Record.exit g e ∈ h := by
  induction h generalizing s with
  | nil => cases hp; exact .inl hexit
  | cons r rs ih =>
    simp only [run] at hp
    cases hstep : r.perform block ctas s with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      rcases ih hp with hu | ⟨e, he⟩
      · rcases record_exited_source hstep hu with hs | ⟨e, he⟩
        · exact .inl hs
        · subst r
          exact .inr ⟨e, by simp⟩
      · exact .inr ⟨e, by simp [he]⟩

/-! ## Cluster-level consequences -/

/-- Every global thread is its cluster's offset plus its cluster-local lane; the cluster of a CTA
is `cta / clusterSize` only in a one-dimensional launch. -/
theorem global_local_split (L : Launch) (hone : L.OneDim) (x : Nat) :
    x = L.clusterOfCta (x / L.block) * (L.block * L.clusterSize.val)
      + x % (L.block * L.clusterSize.val) := by
  rw [Launch.oneDim_clusterOfCta hone, Nat.div_div_eq_div_mul,
    Nat.mul_comm (x / (L.block * L.clusterSize.val))]
  exact (Nat.div_add_mod x (L.block * L.clusterSize.val)).symm

/-- A completed cluster wait observing phase `n` in cluster `c`, and a live cluster-local lane
`p` of that cluster, has an arrival of thread `c * (block * clusterSize) + p` with phase `n`
among the records before the wait. -/
theorem nth_arrival_before_wait {L : Launch} {X : Execution} (hX : ClusterHistoryOk L X)
    (hone : L.OneDim) {c i cta warp : Nat} {lanes : List (Nat × EvId)} {s t : ClusterBarrier.State}
    {g p : Nat} {w : EvId} {n : Nat}
    (hi : (X.clusters c)[i]? = some (.wait cta warp lanes))
    (hs : ClusterBarrier.At L.block L.clusterSize.val (X.clusters c) i s)
    (hwl : (g, w) ∈ lanes) (hphase : s.lastArrival g = some n)
    (hp : ClusterBarrier.Record.perform L.block L.clusterSize.val s (.wait cta warp lanes) =
      .done t)
    (hpl : p < L.block * L.clusterSize.val) (hlive : p ∉ s.exited) :
    ∃ (e : EvId) (release : Bool), e.1 = c * (L.block * L.clusterSize.val) + p ∧
      ClusterBarrier.ArrivalOf L.block L.clusterSize.val ((X.clusters c).take i) e n release := by
  have hc : c < L.nclusters := by
    by_contra hn
    rw [hX.2.1 c (not_lt.mp hn)] at hi
    simp at hi
  obtain ⟨-, hsrc, -⟩ := hX.2.2 c hc
  have hs' : run L.block L.clusterSize.val {} ((X.clusters c).take i) = .done s := hs
  have hcount := wait_forces_count hs hwl hphase hp hpl hlive
  obtain ⟨k, r, hk, hr, hkc⟩ :=
    MbarRing.Slot.exists_nth_countP (ownArrival p) (xs := (X.clusters c).take i) (c := n) (by omega)
  cases r with
  | exit x e => simp [ownArrival] at hr
  | wait cta' warp' lanes' => simp [ownArrival] at hr
  | arrival cta' warp' rel lanes' =>
    have hm : p ∈ lanes'.map Prod.fst := by simpa [ownArrival] using hr
    obtain ⟨⟨q, e⟩, he, hq⟩ := List.mem_map.mp hm
    have hqp : q = p := hq
    rw [hqp] at he
    have hmem : Record.arrival cta' warp' rel lanes' ∈ X.clusters c :=
      List.mem_of_mem_take (List.mem_of_getElem? hk)
    have hglob : e.1 = c * (L.block * L.clusterSize.val) + p := by
      rw [(hsrc _ hmem (p, e) he).2.1, Launch.oneDim_clusterStart hone, Nat.mul_assoc,
        Nat.mul_comm L.clusterSize.val L.block]
    obtain ⟨u, v, hu, hv⟩ := run_perform_at hs' hk
    have hph := arrival_phase_count hu he hv
    exact ⟨e, rel, hglob, k, u, v, cta', warp', lanes', p, hk, hu, he, hph.trans hkc, hv⟩

/-- A release arrival of phase `n` of thread `e.1`, following the event `e`, and a completed
wait of phase `n` in the same cluster orders `e` before every later event `f` of the waiter. -/
theorem baseCausality_of_arrival_wait {L : Launch} {X : Execution} (hX : ClusterHistoryOk L X)
    (hone : L.OneDim) {e f a w : EvId} {n : Nat} (hcl : SameCluster L e.1 f.1)
    (ha : ClusterBarrier.ArrivalOf L.block L.clusterSize.val
      (X.clusters (L.clusterOfCta (f.1 / L.block))) a n true)
    (hae : a.1 = e.1) (hea : e.2 < a.2)
    (hw : ClusterBarrier.WaitOf L.block L.clusterSize.val
      (X.clusters (L.clusterOfCta (f.1 / L.block))) w n)
    (hwf : w.1 = f.1) (hwlt : w.2 < f.2) (hfx : f.2 < (X.tr f.1).length) :
    baseCausality L X e f := by
  obtain ⟨pc, aligned, hget⟩ := ClusterHistoryOk.arrival_present hX ha
  have hlen_a : a.2 < (X.tr e.1).length := by
    have h := len_of_get hget
    rwa [hae] at h
  have hA : ClusterBarrier.ArrivalOf L.block L.clusterSize.val
      (X.clusters (L.clusterOfCta (e.1 / L.block))) (e.1, a.2) n true := by
    have hpair : ((e.1, a.2) : EvId) = a := Prod.ext hae.symm rfl
    rw [hpair, hcl.2.2]
    exact ha
  have hW : ClusterBarrier.WaitOf L.block L.clusterSize.val
      (X.clusters (L.clusterOfCta (e.1 / L.block))) (f.1, w.2) n := by
    have hpair : ((f.1, w.2) : EvId) = w := Prod.ext hwf.symm rfl
    rw [hpair, hcl.2.2]
    exact hw
  have hsync : ClusterBarrier.Synchronizes L.block L.clusterSize.val
      (X.clusters (L.clusterOfCta (e.1 / L.block))) (e.1, a.2) (f.1, w.2) :=
    ⟨n, hA, hW⟩
  have hcs : ClusterSync L X e f := by
    unfold ClusterSync
    rw [Launch.oneDim_clusterSizeOf hone]
    exact ⟨hcl, a.2, w.2, hsync, hlen_a, hea, hwlt, hfx⟩
  exact Relation.TransGen.single (Or.inr (Or.inr (Or.inr (Or.inl hcs))))

/-- An event `w` whose return resumes a cluster arrival `a` of phase `n` precedes, in the
dependency order, every later event `f` of a thread whose cluster wait `v` observes phase `n`: the
return of `w` precedes the arrival (`Resumes`), the arrival fills the `ClusterCounted` need of the
wait's return, and the return of the wait, a blocking event, precedes `f`. -/
theorem depStep_of_arrival_wait {L : Launch} {K : Kernel} {X : Execution}
    {w f a v : EvId} {n : Nat} {pcv : Nat} {alv : Bool} {release : Bool}
    (hres : Resumes K X w a)
    (hget : X.get v = some ⟨pcv, .cluster (.wait alv)⟩)
    (ha : ClusterBarrier.ArrivalOf L.block (L.clusterSizeOf (v.1 / L.block))
      (X.clusters (L.clusterOfCta (v.1 / L.block))) a n release)
    (hv : ClusterBarrier.WaitOf L.block (L.clusterSizeOf (v.1 / L.block))
      (X.clusters (L.clusterOfCta (v.1 / L.block))) v n)
    (hvf : v.1 = f.1) (hvlt : v.2 < f.2) (hfx : f.2 < (X.tr f.1).length) :
    Relation.TransGen (DepStep L K X) (.thread w, true) (.thread f, false) := by
  have hcounted : ClusterCounted L X v a := .inl ⟨n, release, hv, ha⟩
  obtain ⟨i, s, t, cta, warp, lanes, gg, hi, -, hmem, -, -⟩ := ha
  have hy : a ∈ (X.clusters (L.clusterOfCta (v.1 / L.block))).flatMap
      ClusterBarrier.Record.refs :=
    List.mem_flatMap.mpr
      ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(gg, a), hmem, rfl⟩⟩
  have hneed : Need.node (· = .thread a) ∈ Needs L X v := by
    simp only [Needs, hget, KindNeeds, clusterNeeds, needsIf, List.mem_append, List.mem_flatMap]
    exact .inr ⟨_, List.mem_flatMap.mp hy, by simp [hcounted]⟩
  have h1 : DepStep L K X (.thread w, true) (.thread a, false) := DepStep.of_resumes L hres
  have h2 : DepStep L K X (.thread a, false) (.thread v, true) :=
    DepStep.of_witness L (Witness.of_need L hneed (present_of_len hres.1.2.2) rfl)
  have h3 : DepStep L K X (.thread v, true) (.thread f, false) :=
    DepStep.of_resumes L
      (Resumes.of_blocking hget (b := false) (by simp [Kind.resume]) ⟨hvf, hvlt, hfx⟩)
  exact ((Relation.TransGen.single h1).tail h2).tail h3

end PTX.ClusterPhase

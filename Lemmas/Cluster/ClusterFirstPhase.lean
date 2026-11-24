-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.MBarrier.InitPublication
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Order.OrderWaits
public import Lemmas.Order.StageCausalityThread
public import Lemmas.Cluster.ClusterRecordSnoc
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Cluster.ClusterBarrierSound
public import Mathlib.Logic.Relation
public import Lemmas.Order.WaitOrderWaits

@[expose] public section

/-! # First cluster-barrier phase of a thread

A proof tool. Let `first g` be the index of thread `g`'s first cluster-barrier arrival, of any
qualifier; its matching wait is at `first g + 1`. Before `first g` the thread performs no cluster
operation and does not exit, so that arrival is of generation zero, and a completed cluster wait
in the cluster of `g` forces the arrival to be recorded (`start_of_post_event`). With release
arrivals the start barrier synchronizes every event before a member's first arrival with every
event of a cluster member after its first wait (`clusterSync_of_post_event`). The only inputs
are the shape of these events, given as hypotheses; every phase, history and synchronization
fact is derived from the checked cluster history. The cluster of a thread has its own size
(`L.clusterSizeAt`), so the lemmas that need a thread's cluster-local index
(`first_arrival_of_completed_wait_any` and what is built on it) ask for a one-dimensional launch
(`L.OneDim`). -/

namespace PTX
noncomputable section

namespace ClusterBarrier

def Unstarted (g : Nat) (s : State) : Prop :=
  s.phase = 0 ∧ g ∉ s.arrived ∧ g ∉ s.exited

def Action.Avoids (g : Nat) : Action → Prop
  | .arrive h _ | .exit h => h ≠ g
  | .wait _ => True

def Record.Participates {α : Type} (g : Nat) : Record α → Prop
  | .arrival _ _ _ lanes => ∃ e, (g,e) ∈ lanes
  | .exit h _ => h = g
  | .wait .. => False

private theorem finish_of_missing {threads g : Nat} {s : State}
    (hg : g < threads) (ha : g ∉ s.arrived) (he : g ∉ s.exited) :
    finish threads s = s := by
  have hn : ¬ ∀ h ∈ Finset.range threads, h ∈ s.arrived ∨ h ∈ s.exited := by
    intro hh
    exact (hh g (Finset.mem_range.mpr hg)).elim ha he
  simp only [finish,ite_eq_right hn]

private theorem wait_phase_positive {threads g : Nat} {s t : State}
    (hp : perform threads s (.wait g) = .done t) : 0 < s.phase := by
  by_contra hn
  have hz : s.phase = 0 := by omega
  cases hl : s.lastArrival g <;> simp only [perform,hl,hz,Nat.not_lt_zero] at hp
  all_goals split at hp
  all_goals try cases hp

private theorem perform_unstarted {threads g : Nat} {s t : State} {a : Action}
    (hg : g < threads) (hs : Unstarted g s) (ha : a.Avoids g)
    (hp : perform threads s a = .done t) : Unstarted g t := by
  rcases hs with ⟨hphase,harrived,hexited⟩
  cases a with
  | arrive h release =>
    simp only [Action.Avoids] at ha
    simp only [perform] at hp
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · have hmissing : g ∉ insert h s.arrived := by simpa [ha,Ne.symm ha] using harrived
        let u : State := { s with
          arrived := insert h s.arrived
          lastArrival := fun j => if j = h then some s.phase else s.lastArrival j }
        change Outcome.done (finish threads u) = .done t at hp
        rw [finish_of_missing (s:=u) hg hmissing hexited] at hp
        have htu : u = t := Outcome.done.inj hp
        rw [← htu]
        exact ⟨hphase,hmissing,hexited⟩
  | exit h =>
    simp only [Action.Avoids] at ha
    simp only [perform] at hp
    split at hp
    · cases hp
    · have hmissing : g ∉ insert h s.exited := by simpa [ha,Ne.symm ha] using hexited
      let u : State := { s with exited := insert h s.exited }
      change Outcome.done (finish threads u) = .done t at hp
      rw [finish_of_missing (s:=u) hg harrived hmissing] at hp
      have htu : u = t := Outcome.done.inj hp
      rw [← htu]
      exact ⟨hphase,harrived,hmissing⟩
  | wait h =>
    have hpos := wait_phase_positive hp
    omega

theorem Record.avoids {α : Type} {g : Nat} {r : Record α} (hr : ¬ r.Participates g) {a : Action}
    (ha : a ∈ r.actions) : a.Avoids g := by
  cases r with
  | exit h e =>
    simp only [Record.actions, List.mem_singleton] at ha
    subst ha
    exact hr
  | arrival cta warp release lanes =>
    obtain ⟨⟨h, e⟩, he, rfl⟩ := List.mem_map.mp ha
    intro heq
    exact hr ⟨e, heq ▸ he⟩
  | wait cta warp lanes =>
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp ha
    trivial

private theorem run_unstarted {α : Type} {block ctas g : Nat} {s t : State}
    {h : List (Record α)} (hg : g < block*ctas) (hs : Unstarted g s)
    (ha : ∀ r ∈ h, ¬ r.Participates g) (hp : run block ctas s h = .done t) :
    Unstarted g t :=
  run_lift (R := fun s t => Unstarted g s → Unstarted g t) (fun _ h => h)
    (fun h1 h2 h => h2 (h1 h))
    (fun r hr _ hm _ _ hp hs => perform_unstarted hg hs (Record.avoids (ha r hr) hm) hp) hp hs

private theorem record_wait_phase_positive {α : Type} {block ctas cta warp : Nat}
    {lanes : List (Nat × α)} {s t : State}
    (hp : Record.perform block ctas s (.wait cta warp lanes) = .done t) :
    0 < s.phase := by
  simp only [Record.perform] at hp
  split at hp
  · have hnonempty : lanes ≠ [] := by
      intro hz
      rename_i hlive
      simp [hz,liveWarp] at hlive
    cases lanes with
    | nil => exact absurd rfl hnonempty
    | cons p ps =>
      simp only [List.map_cons,performAll] at hp
      cases hfirst : perform (block*ctas) s (.wait p.1) with
      | blocked => rw [hfirst] at hp; cases hp
      | fault e => rw [hfirst] at hp; cases hp
      | done u => exact wait_phase_positive hfirst
  · cases hp

private theorem run_member_performed {α : Type} {block ctas : Nat} {initial final : State}
    {h : List (Record α)} {r : Record α}
    (hrun : run block ctas initial h = .done final) (hr : r ∈ h) :
    ∃ i s t, h[i]? = some r ∧ run block ctas initial (h.take i) = .done s ∧
      r.perform block ctas s = .done t := by
  induction h generalizing initial with
  | nil => cases hr
  | cons q qs ih =>
    simp only [run] at hrun
    cases hstep : q.perform block ctas initial with
    | fault e => rw [hstep] at hrun; cases hrun
    | blocked => rw [hstep] at hrun; cases hrun
    | done u =>
      rw [hstep] at hrun
      rcases List.mem_cons.mp hr with heq | hmem
      · subst q
        exact ⟨0,initial,u,rfl,rfl,hstep⟩
      · obtain ⟨i,s,t,hi,hs,ht⟩ := ih hrun hmem
        refine ⟨i+1,s,t,by simpa using hi,?_,ht⟩
        simp only [List.take_succ_cons,run,hstep]
        exact hs

/-- Recover the actual object generation of any recorded arrival. -/
theorem arrivalOf_of_record {α : Type} {block ctas cta warp g : Nat} {release : Bool}
    {h : List (Record α)} {lanes : List (Nat × α)} {e : α} {final : State}
    (hrun : run block ctas {} h = .done final)
    (hr : .arrival cta warp release lanes ∈ h) (he : (g,e) ∈ lanes) :
    ∃ phase, ArrivalOf block ctas h e phase release := by
  obtain ⟨i,s,t,hi,hs,ht⟩ := run_member_performed hrun hr
  exact ⟨s.phase,i,s,t,cta,warp,lanes,g,hi,hs,he,rfl,ht⟩

/-- Recover the phase actually observed by a lane of a completed wait record. -/
theorem waitOf_of_record {α : Type} {block ctas cta warp g : Nat}
    {h : List (Record α)} {lanes : List (Nat × α)} {e : α} {final : State}
    (hrun : run block ctas {} h = .done final)
    (hr : .wait cta warp lanes ∈ h) (he : (g,e) ∈ lanes) :
    ∃ phase, WaitOf block ctas h e phase := by
  obtain ⟨i,s,t,hi,hs,ht⟩ := run_member_performed hrun hr
  have hperform := ht
  simp only [Record.perform] at hperform
  split at hperform
  · have hm : g ∈ lanes.map Prod.fst := List.mem_map.mpr ⟨(g,e),he,rfl⟩
    have hwait : performAll (block*ctas) s ((lanes.map Prod.fst).map Action.wait) = .done t := by
      simpa only [List.map_map, Function.comp_def] using hperform
    obtain ⟨phase,hphase,-⟩ := ClusterPhase.performAll_wait_info hwait g hm
    exact ⟨phase,i,s,t,cta,warp,lanes,g,hi,hs,he,hphase,ht⟩
  · cases hperform

/-- A legal object-history prefix cannot complete even its first generation
before a particular live participant has arrived or exited. -/
theorem phase_zero_of_no_arrival_or_exit {α : Type} {block ctas g : Nat}
    {h : List (Record α)} {s : State}
    (hrun : run block ctas {} h = .done s) (hg : g < block*ctas)
    (hnone : ¬ ((∃ cta warp release lanes e,
      .arrival cta warp release lanes ∈ h ∧ (g,e) ∈ lanes) ∨
      ∃ e, .exit g e ∈ h)) : s.phase = 0 := by
  have hn : ∀ r ∈ h, ¬ r.Participates g := by
    intro r hr hp
    cases r with
    | arrival cta warp release lanes =>
      obtain ⟨e,he⟩ := hp
      exact hnone (.inl ⟨cta,warp,release,lanes,e,hr,he⟩)
    | exit j e =>
      have heq : j = g := hp
      subst j
      exact hnone (.inr ⟨e,hr⟩)
    | wait => cases hp
  exact (run_unstarted hg (by simp [Unstarted]) hn hrun).1

/-- A completed cluster wait certifies that every cluster-local thread has a
real arrival or exit record in the checked object history. This is a consequence
of the barrier counter transitions, with no scheduling premise. -/
theorem WaitOf.member_arrival_or_exit {α : Type} {block ctas g phase : Nat}
    {h : List (Record α)} {waiter : α}
    (hw : WaitOf block ctas h waiter phase) (hg : g < block*ctas) :
    (∃ cta warp release lanes e, .arrival cta warp release lanes ∈ h ∧ (g,e) ∈ lanes) ∨
      ∃ e, .exit g e ∈ h := by
  by_contra hn
  have hnone : ∀ r ∈ h, ¬ r.Participates g := by
    intro r hr hp
    cases r with
    | arrival cta warp release lanes =>
      obtain ⟨e,he⟩ := hp
      exact hn (.inl ⟨cta,warp,release,lanes,e,hr,he⟩)
    | exit j e =>
      have heq : j = g := hp
      subst j
      exact hn (.inr ⟨e,hr⟩)
    | wait => cases hp
  obtain ⟨i,s,t,cta,warp,lanes,j,hi,hs,he,hphase,hp⟩ := hw
  have hu : Unstarted g s := run_unstarted hg (by simp [Unstarted])
    (fun r hr => hnone r (List.mem_of_mem_take hr)) hs
  have hz := hu.1
  have hpos := record_wait_phase_positive hp
  omega

private theorem performAll_arrive_other_last {threads g : Nat} {release : Bool}
    {gs : List Nat} {s t : State} (hg : g ∉ gs)
    (hp : performAll threads s (gs.map (fun g => Action.arrive g release)) = .done t) :
    t.lastArrival g = s.lastArrival g :=
  performAll_lift (R := fun s t => t.lastArrival g = s.lastArrival g) (fun _ => rfl)
    (fun h1 h2 => h2.trans h1) (fun _ ha _ _ hp => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact perform_arrive_other_last (by rintro rfl; exact hg hj) hp) hp

private theorem finish_missing {threads g : Nat} {s : State}
    (hg : g < threads) (ha : g ∉ s.arrived) (he : g ∉ s.exited) :
    finish threads s = s := by
  unfold finish
  have hn : ¬ ∀ g ∈ Finset.range threads, g ∈ s.arrived ∨ g ∈ s.exited := by
    intro hh
    exact (hh g (Finset.mem_range.mpr hg)).elim ha he
  rw [ite_eq_right hn]

private theorem performAll_arrive_member_last {threads : Nat} {release : Bool}
    {gs : List Nat} {s t : State} (hs : Sound s) (hnd : gs.Nodup)
    (hlive : ∀ g ∈ gs, g < threads ∧ g ∉ s.exited) (hnot : ∀ g ∈ gs, g ∉ s.arrived)
    (hp : performAll threads s (gs.map (fun g => Action.arrive g release)) = .done t) :
    ∀ g ∈ gs, t.lastArrival g = some s.phase := by
  induction gs generalizing s with
  | nil => simp
  | cons j gs ih =>
    simp only [List.map_cons,performAll] at hp
    cases hstep : perform threads s (.arrive j release) with
    | blocked => rw [hstep] at hp; cases hp
    | fault e => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact (performAll_arrive_other_last (List.nodup_cons.mp hnd).1 hp).trans
          (perform_arrive_own_last hstep)
      · have hphase : u.phase = s.phase := by
          rw [perform_arrive_eq hstep]
          have hne : g ≠ j := by
            intro heq
            subst g
            exact (List.nodup_cons.mp hnd).1 hg
          have ha : g ∉ insert j s.arrived := by
            simp [hne,hnot g (by simp [hg])]
          let v : State := { s with
            arrived := insert j s.arrived
            lastArrival := fun h => if h = j then some s.phase else s.lastArrival h }
          change (finish threads v).phase = s.phase
          rw [finish_missing (s:=v) (g:=g) (hlive g (by simp [hg])).1 ha
            (hlive g (by simp [hg])).2]
        have hmember := ih (sound_perform hs hstep) (List.nodup_cons.mp hnd).2
          (by
            intro k hk
            refine ⟨(hlive k (by simp [hk])).1,?_⟩
            rw [perform_arrive_eq hstep,finish_exited]
            exact (hlive k (by simp [hk])).2)
          (by
            intro k hk hku
            have hkj : k ≠ j := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hk)
            rw [perform_arrive_eq hstep] at hku
            unfold finish at hku
            split at hku
            · simp at hku
            · simp only [Finset.mem_insert, hkj, false_or] at hku
              exact hnot k (by simp [hk]) hku) hp g hg
        rwa [hphase] at hmember

private theorem perform_wait_last {threads g : Nat} {s t : State}
    (hp : perform threads s (.wait g) = .done t) : t.lastArrival = s.lastArrival := by
  rw [ClusterPhase.perform_wait_eq hp]

private theorem performAll_wait_last {α : Type} {threads : Nat} {lanes : List (Nat × α)}
    {s t : State} (hp : performAll threads s (lanes.map (fun p => Action.wait p.1)) = .done t) :
    t.lastArrival = s.lastArrival :=
  performAll_lift (R := fun s t => t.lastArrival = s.lastArrival) (fun _ => rfl)
    (fun h1 h2 => h2.trans h1) (fun _ ha _ _ hp => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha
      exact perform_wait_last hp) hp

private theorem record_lastArrival {α : Type} {block ctas g phase : Nat}
    {r : Record α} {s t : State} (hs : Sound s)
    (hp : r.perform block ctas s = .done t) (hla : t.lastArrival g = some phase) :
    s.lastArrival g = some phase ∨
      ∃ cta warp release lanes e, r = .arrival cta warp release lanes ∧
        (g,e) ∈ lanes ∧ s.phase = phase := by
  cases r with
  | exit j e =>
    left
    simp only [Record.perform,perform] at hp
    split at hp
    · cases hp
    · rw [← Outcome.done.inj hp,finish_lastArrival] at hla
      exact hla
  | wait cta warp lanes =>
    left
    simp only [Record.perform] at hp
    split at hp
    · rwa [performAll_wait_last hp] at hla
    · cases hp
  | arrival cta warp release lanes =>
    have hnotall := record_arrive_not_locked hp
    simp only [Record.perform] at hp
    split at hp
    · rename_i hvalid
      split at hp
      · cases hp
      simp only [liveWarp,decide_eq_true_eq] at hvalid
      have hmap : performAll (block*ctas) s
          ((lanes.map Prod.fst).map (fun g => Action.arrive g release)) = .done t := by
        simpa only [List.map_map,Function.comp_def] using hp
      by_cases hg : g ∈ lanes.map Prod.fst
      · have hknown : t.lastArrival g = some s.phase :=
          performAll_arrive_member_last hs hvalid.2.2.2.2.1 (by
            intro j hj
            have hv := hvalid.2.2.2.2.2.1 j hj
            exact ⟨hv.1,hv.2.2.2⟩) hnotall hmap g hg
        have hphase : s.phase = phase := Option.some.inj (hknown.symm.trans hla)
        obtain ⟨⟨j,e⟩,he,hj⟩ := List.mem_map.mp hg
        have heq : j = g := hj
        subst j
        exact .inr ⟨cta,warp,release,lanes,e,rfl,he,hphase⟩
      · exact .inl (by rwa [performAll_arrive_other_last hg hmap] at hla)
    · cases hp

/-- An arrival witness retaining the cluster-local lane identity, used in
resource-to-source correspondence proofs. -/
def LaneArrival {α : Type} (block ctas : Nat) (h : List (Record α))
    (g : Nat) (e : α) (phase : Nat) (release : Bool) : Prop :=
  ∃ i s t cta warp lanes, h[i]? = some (.arrival cta warp release lanes) ∧
    At block ctas h i s ∧ (g,e) ∈ lanes ∧ s.phase = phase ∧
    Record.perform block ctas s (.arrival cta warp release lanes) = .done t

theorem LaneArrival.arrivalOf {α : Type} {block ctas g phase : Nat}
    {h : List (Record α)} {e : α} {release : Bool}
    (ha : LaneArrival block ctas h g e phase release) :
    ArrivalOf block ctas h e phase release := by
  obtain ⟨i,s,t,cta,warp,lanes,hi,hs,he,hphase,hp⟩ := ha
  exact ⟨i,s,t,cta,warp,lanes,g,hi,hs,he,hphase,hp⟩

theorem LaneArrival.append {α : Type} {block ctas g phase : Nat}
    {xs ys : List (Record α)} {e : α} {release : Bool}
    (ha : LaneArrival block ctas xs g e phase release) :
    LaneArrival block ctas (xs++ys) g e phase release := by
  obtain ⟨i,s,t,cta,warp,lanes,hi,hs,he,hphase,hp⟩ := ha
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨i,s,t,cta,warp,lanes,?_,?_,he,hphase,hp⟩
  · rwa [List.getElem?_append_left hlt]
  · unfold At at hs ⊢
    rwa [List.take_append_of_le_length hlt.le]

theorem LaneArrival.of_take {α : Type} {block ctas g phase k : Nat}
    {h : List (Record α)} {e : α} {release : Bool}
    (ha : LaneArrival block ctas (h.take k) g e phase release) :
    LaneArrival block ctas h g e phase release := by
  have hp := ha.append (ys:=h.drop k)
  rwa [List.take_append_drop] at hp

/-- Every stored last-arrival generation has an actual arrival record of the
same lane and generation. No memory-order premise enters this object proof. -/
theorem lastArrival_source {α : Type} {block ctas g phase : Nat}
    {h : List (Record α)} {s : State}
    (hrun : run block ctas {} h = .done s) (hla : s.lastArrival g = some phase) :
    ∃ e release, LaneArrival block ctas h g e phase release := by
  induction h using List.reverseRecOn generalizing s with
  | nil => cases hrun; simp at hla
  | @append_singleton rs r ih =>
    obtain ⟨before,hbefore⟩ := run_prefix hrun
    rw [run_append,hbefore] at hrun
    change (match r.perform block ctas before with
      | .done t => Outcome.done t | other => other) = Outcome.done s at hrun
    have hstep : r.perform block ctas before = .done s := by
      cases ht : r.perform block ctas before with
      | done u => simpa only [ht] using hrun
      | blocked => simp [ht] at hrun
      | fault e => simp [ht] at hrun
    rcases record_lastArrival (sound_run sound_empty hbefore) hstep hla with
        hold | ⟨cta,warp,release,lanes,e,hr,he,hphase⟩
    · obtain ⟨e,release,ha⟩ := ih hbefore hold
      exact ⟨e,release,ha.append⟩
    · subst r
      refine ⟨e,release,rs.length,before,s,cta,warp,lanes,?_,?_,he,hphase,hstep⟩
      · simp
      · unfold At
        simpa using hbefore

/-- The source association of an arrival retains the exact lane and reference. -/
theorem LaneArrival.member {α : Type} {block ctas g phase : Nat}
    {h : List (Record α)} {e : α} {release : Bool}
    (ha : LaneArrival block ctas h g e phase release) :
    ∃ cta warp lanes, .arrival cta warp release lanes ∈ h ∧ (g,e) ∈ lanes := by
  obtain ⟨i,s,t,cta,warp,lanes,hi,_,he,_,_⟩ := ha
  exact ⟨cta,warp,lanes,List.mem_of_getElem? hi,he⟩

/-- Every completed wait observes an actual prior arrival of its own lane in
the same generation. The arrival witness lies strictly in the wait's history
prefix, rather than being supplied independently by a caller. -/
theorem WaitOf.arrival {α : Type} {block ctas phase : Nat}
    {h : List (Record α)} {waiter : α}
    (hw : WaitOf block ctas h waiter phase) :
    ∃ i g arrival release,
      (∃ s t cta warp lanes,
        h[i]? = some (.wait cta warp lanes) ∧ At block ctas h i s ∧
        (g,waiter) ∈ lanes ∧ s.lastArrival g = some phase ∧
        Record.perform block ctas s (.wait cta warp lanes) = .done t) ∧
      LaneArrival block ctas (h.take i) g arrival phase release := by
  obtain ⟨i,s,t,cta,warp,lanes,g,hi,hs,he,hphase,hp⟩ := hw
  obtain ⟨arrival,release,ha⟩ := lastArrival_source hs hphase
  exact ⟨i,g,arrival,release,⟨s,t,cta,warp,lanes,hi,hs,he,hphase,hp⟩,ha⟩

end ClusterBarrier

private theorem cluster_refs_ne {h : List (ClusterBarrier.Record EvId)}
    (hnd : (h.flatMap ClusterBarrier.Record.refs).Nodup)
    {i j : Nat} {r q : ClusterBarrier.Record EvId} {e f : EvId}
    (hr : h[i]? = some r) (hq : h[j]? = some q) (hij : i < j)
    (he : e ∈ r.refs) (hf : f ∈ q.refs) : e ≠ f := by
  have hjl := (List.getElem?_eq_some_iff.mp hq).1
  have hd : h = h.take j ++ q :: h.drop (j+1) := by
    rw [← (List.getElem?_eq_some_iff.mp hq).2,← List.drop_eq_getElem_cons hjl]
    exact (List.take_append_drop j h).symm
  have hm : r ∈ h.take j := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i,?_,?_⟩
    · simp only [List.length_take]; omega
    · simpa only [List.getElem_take] using (List.getElem?_eq_some_iff.mp hr).2
  have hepre := List.mem_flatMap.mpr ⟨r,hm,he⟩
  have hn := hnd
  rw [hd,List.flatMap_append,List.flatMap_cons] at hn
  intro hef
  subst f
  exact (List.nodup_append.mp hn).2.2 _ hepre _
    (List.mem_append.mpr (.inl hf)) rfl

/-- A checked cluster history cannot reverse a thread's actual source events: the history is
one object's order (`ObjectOrder .cluster`), and program order is causality. -/
theorem ClusterHistoryOk.source_order {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) (hobj : ObjectCoherent L X) {c i j : Nat}
    {r q : ClusterBarrier.Record EvId} {e f : EvId}
    (hr : (X.clusters c)[i]? = some r) (hq : (X.clusters c)[j]? = some q)
    (hij : i < j) (he : e ∈ r.refs) (hf : f ∈ q.refs) (hthread : e.1 = f.1) :
    e.2 < f.2 := by
  obtain ⟨ee,hee⟩ := h.ref_present (List.mem_of_getElem? hr) he
  obtain ⟨ff,hff⟩ := h.ref_present (List.mem_of_getElem? hq) hf
  have hc : c < L.nclusters := by
    by_contra hn
    rw [h.2.1 c (by omega)] at hr
    cases hr
  have hne := cluster_refs_ne (h.2.2 c hc).1 hr hq hij he hf
  have hnidx : e.2 ≠ f.2 := by
    intro hh
    exact hne (Prod.ext hthread hh)
  by_contra hn
  have hrev : f.2 < e.2 := by omega
  have hedge : ObjectOrder L X (.cluster c) (.thread e,ClusterPoint r) (.thread f,ClusterPoint q) :=
    ⟨e,f,rfl,rfl,⟨ee,hee⟩,⟨ff,hff⟩,i,j,r,q,hr,hq,hij,he,hf,rfl,rfl⟩
  have hpo : baseCausality L X f e := .single
      (.inl (po_of_not_access hthread.symm hrev (len_of_get hee)
    (h.ref_not_access (List.mem_of_getElem? hr) he)))
  have hback : Relation.TransGen (WithObject L X (.cluster c))
      (.thread f,ClusterPoint q) (.thread e,ClusterPoint r) := by
    have hmid : Relation.TransGen (WithObject L X (.cluster c))
        (.thread f,ClusterPoint q) (.thread e,false) := by
      cases ClusterPoint q
      · exact .tail (.single (.inl (stageCausality.of_present hff)))
          (.inl (stageCausality.of_baseCausality hpo))
      · exact .single (.inl (stageCausality.of_baseCausality hpo))
    cases ClusterPoint r
    · exact hmid
    · exact hmid.tail (.inl (stageCausality.of_present hee))
  exact hobj _ _ (hback.tail (.inr hedge))

private theorem mem_take_index {α : Type} {xs : List α} {n : Nat} {r : α}
    (hr : r ∈ xs.take n) : ∃ j, j < n ∧ xs[j]? = some r := by
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hr
  simp only [List.length_take] at hj
  have hjn : j < n := by omega
  have hjx : j < xs.length := by omega
  exact ⟨j,hjn,List.getElem?_eq_some_iff.mpr
    ⟨hjx,by simpa only [List.getElem_take] using hget⟩⟩

/-- A recorded actual cluster wait is a completed resource operation; recover
its observed generation from the checked history, rather than from source PC. -/
theorem ClusterHistoryOk.waitOf_recorded {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) {e : EvId} {pc : Nat} {aligned : Bool}
    (hget : X.get e = some ⟨pc,.cluster (.wait aligned)⟩)
    (hrecorded : ClusterRecorded L X e) :
    ∃ phase, ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (e.1/L.block)))
      (X.clusters (L.clusterOfCta (e.1/L.block))) e phase := by
  obtain ⟨r,hr,he⟩ := hrecorded
  have hc : L.clusterOfCta (e.1/L.block) < L.nclusters := by
    by_contra hn
    rw [h.2.1 _ (by omega)] at hr
    cases hr
  obtain ⟨_,hsource,s,hrun⟩ := h.2.2 _ hc
  have hs := hsource r hr
  cases r with
  | exit g f =>
    simp only [ClusterBarrier.Record.refs,List.mem_singleton] at he
    subst f
    obtain ⟨_,_,pc',hp⟩ := hs
    rw [hget] at hp
    cases hp
  | arrival cta warp release lanes =>
    obtain ⟨p,hp,hpe⟩ := List.mem_map.mp he
    obtain ⟨_,_,pc',al,hp'⟩ := hs p hp
    change p.2 = e at hpe
    rw [hpe,hget] at hp'
    cases hp'
  | wait cta warp lanes =>
    obtain ⟨p,hp,hpe⟩ := List.mem_map.mp he
    change p.2 = e at hpe
    have hpair : (p.1,e) ∈ lanes := by rw [←hpe]; exact hp
    exact ClusterBarrier.waitOf_of_record hrun hr hpair

/-- An actual recorded cluster arrival has a generation, of its own qualifier. -/
theorem ClusterHistoryOk.arrivalOf_recorded_any {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) {e : EvId} {pc : Nat} {rel aligned : Bool}
    (hget : X.get e = some ⟨pc, .cluster (.arrive rel aligned)⟩)
    (hrecorded : ClusterRecorded L X e) :
    ∃ phase, ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt (L.clusterOfCta (e.1 / L.block)))
      (X.clusters (L.clusterOfCta (e.1 / L.block))) e phase rel := by
  obtain ⟨r, hr, he⟩ := hrecorded
  have hc : L.clusterOfCta (e.1 / L.block) < L.nclusters := by
    by_contra hn
    rw [h.2.1 _ (by omega)] at hr
    cases hr
  obtain ⟨_, hsource, s, hrun⟩ := h.2.2 _ hc
  have hs := hsource r hr
  cases r with
  | exit g f =>
    simp only [ClusterBarrier.Record.refs, List.mem_singleton] at he
    subst f
    obtain ⟨_, _, pc', hp⟩ := hs
    rw [hget] at hp
    cases hp
  | wait cta warp lanes =>
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp he
    obtain ⟨_, _, pc', al, hp'⟩ := hs p hp
    change p.2 = e at hpe
    rw [hpe, hget] at hp'
    cases hp'
  | arrival cta warp release lanes =>
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp he
    obtain ⟨_, _, pc', al, hp'⟩ := hs p hp
    change p.2 = e at hpe
    have hpair : (p.1, e) ∈ lanes := by rw [← hpe]; exact hp
    rw [hpe, hget] at hp'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.cluster.injEq,
      ClusterOp.arrive.injEq] at hp'
    obtain ⟨-, rfl, -⟩ := hp'
    exact ClusterBarrier.arrivalOf_of_record hrun hr hpair

/-- A later source event is enough to invoke the blocking rule; the phase is
then recovered from the actual completed wait record. -/
theorem ClusterHistoryOk.waitOf_returned {L : Launch} {X : Execution}
    (h : ClusterHistoryOk L X) (hb : ClusterBlocking L X)
    {e : EvId} {pc : Nat} {aligned : Bool}
    (hget : X.get e = some ⟨pc,.cluster (.wait aligned)⟩)
    (hnext : e.2+1 < (X.tr e.1).length) :
    ∃ phase, ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (e.1/L.block)))
      (X.clusters (L.clusterOfCta (e.1/L.block))) e phase :=
  h.waitOf_recorded hget (hb e pc (.wait aligned) hget hnext)

section FirstPhase

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {first : Nat → Nat}

/-- The first arrival of `g` is generation zero: no earlier event of `g` is a cluster
operation or an exit, so the cluster counter has not completed a generation before it. -/
theorem first_arrival_phase_zero (hX : Consistent L K A mem0 X)
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    {g phase : Nat} {release : Bool} (hg : g < L.threads)
    (ha : ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt (L.clusterOfCta (g / L.block)))
      (X.clusters (L.clusterOfCta (g / L.block))) (g, first g) phase release) :
    phase = 0 := by
  obtain ⟨i,s,t,cta,warp,lanes,localg,hi,hs,he,hphase,ht⟩ := ha
  have hc : L.clusterOfCta (g/L.block) < L.nclusters := by
    by_contra hn
    rw [hX.cluster.2.1 _ (by omega)] at hi
    cases hi
  have hsource := (hX.cluster.2.2 _ hc).2.1
  obtain ⟨hlocal,hglobal,_,_,_⟩ := hsource _ (List.mem_of_getElem? hi)
    (localg,(g,first g)) he
  have href : (g,first g) ∈
      (ClusterBarrier.Record.arrival cta warp release lanes).refs :=
    List.mem_map.mpr ⟨(localg,(g,first g)),he,rfl⟩
  have hno : ∀ r ∈ (X.clusters (L.clusterOfCta (g/L.block))).take i,
      ∀ f ∈ r.refs, f.1 = g → False := by
    intro r hr f hf hfg
    obtain ⟨j,hji,hj⟩ := mem_take_index hr
    have hlt : f.2 < first g :=
      hX.cluster.source_order hX.object hj hi hji hf href hfg
    rcases hX.cluster.ref_operation (List.mem_of_mem_take hr) hf with
        ⟨pc,op,hget⟩ | ⟨pc,hget⟩
    · have hget' : X.get (g,f.2) = some ⟨pc,.cluster op⟩ := by
        have hpair : (g,f.2) = f := Prod.ext hfg.symm rfl
        rwa [hpair]
      exact (hbefore g hg f.2 hlt _ hget').1 op rfl
    · have hget' : X.get (g,f.2) = some ⟨pc,.exit⟩ := by
        have hpair : (g,f.2) = f := Prod.ext hfg.symm rfl
        rwa [hpair]
      exact (hbefore g hg f.2 hlt _ hget').2 rfl
  have hnone : ¬ ((∃ cta warp release lanes e,
      ClusterBarrier.Record.arrival cta warp release lanes ∈
        (X.clusters (L.clusterOfCta (g/L.block))).take i ∧ (localg,e) ∈ lanes) ∨
      ∃ e, ClusterBarrier.Record.exit localg e ∈
        (X.clusters (L.clusterOfCta (g/L.block))).take i) := by
    rintro (⟨cta',warp',release,lanes',e,hr,he'⟩ | ⟨e,hr⟩)
    · obtain ⟨_,hglobal',_,_,_⟩ := hsource _ (List.mem_of_mem_take hr) (localg,e) he'
      exact hno _ hr e (List.mem_map.mpr ⟨(localg,e),he',rfl⟩)
        (hglobal'.trans hglobal.symm)
    · obtain ⟨_,hglobal',_,_⟩ := hsource _ (List.mem_of_mem_take hr)
      exact hno _ hr e (by simp [ClusterBarrier.Record.refs]) (hglobal'.trans hglobal.symm)
  have hzero := ClusterBarrier.phase_zero_of_no_arrival_or_exit hs hlocal hnone
  exact hphase.symm.trans hzero

/-- A completed wait at `first g + 1` observes generation zero. -/
theorem first_wait_phase_zero (hX : Consistent L K A mem0 X)
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    {g phase : Nat} (hg : g < L.threads)
    (hw : ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (g/L.block)))
      (X.clusters (L.clusterOfCta (g/L.block))) (g, first g + 1) phase) :
    phase = 0 := by
  obtain ⟨i,localg,arrival,release,⟨s,t,cta,warp,lanes,hi,hs,he,hphase,ht⟩,ha⟩ := hw.arrival
  have hfull := ha.of_take.arrivalOf
  obtain ⟨j,u,v,cta',warp',lanes',hj,hu,he',hphase',ht'⟩ := ha
  have hjlen := (List.getElem?_eq_some_iff.mp hj).1
  have hjget := (List.getElem?_eq_some_iff.mp hj).2
  simp only [List.length_take] at hjlen
  have hji : j < i := by omega
  have hjall : (X.clusters (L.clusterOfCta (g/L.block)))[j]? =
      some (.arrival cta' warp' release lanes') :=
    List.getElem?_eq_some_iff.mpr ⟨by omega,by simpa only [List.getElem_take] using hjget⟩
  have hc : L.clusterOfCta (g/L.block) < L.nclusters := by
    by_contra hn
    rw [hX.cluster.2.1 _ (by omega)] at hi
    cases hi
  have hsource := (hX.cluster.2.2 _ hc).2.1
  obtain ⟨_,hglobal,_,_,_⟩ := hsource _ (List.mem_of_getElem? hi)
    (localg,(g,first g + 1)) he
  obtain ⟨_,hglobal',pc,aligned,hget⟩ := hsource _ (List.mem_of_getElem? hjall)
    (localg,arrival) he'
  have hag : arrival.1 = g := hglobal'.trans hglobal.symm
  have hlt : arrival.2 < first g + 1 :=
    hX.cluster.source_order hX.object hjall hi hji
      (List.mem_map.mpr ⟨(localg,arrival),he',rfl⟩)
      (List.mem_map.mpr ⟨(localg,(g,first g + 1)),he,rfl⟩) hag
  have hge : first g ≤ arrival.2 := by
    by_contra hn
    have hget' : X.get (g,arrival.2) = some ⟨pc,.cluster (.arrive release aligned)⟩ := by
      have hp : (g,arrival.2) = arrival := Prod.ext hag.symm rfl
      rwa [hp]
    exact (hbefore g hg arrival.2 (by omega) _ hget').1 (.arrive release aligned) rfl
  have heq : arrival = (g,first g) := Prod.ext hag (by omega)
  rw [heq] at hfull
  exact first_arrival_phase_zero hX hbefore hg hfull

/-- Any recorded participation of `g` in its cluster history records its first operation. -/
theorem first_recorded_any (hX : Consistent L K A mem0 X)
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (hop : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc op, X.get (g, first g) = some ⟨pc, .cluster op⟩)
    {g : Nat} (hg : g < L.threads) {r : ClusterBarrier.Record EvId} {e : EvId}
    (hr : r ∈ X.clusters (L.clusterOfCta (g / L.block))) (he : e ∈ r.refs) (heg : e.1 = g) :
    ClusterRecorded L X (g, first g) := by
  have hno : ¬ e.2 < first g := by
    intro hlt
    have hp : (g, e.2) = e := Prod.ext heg.symm rfl
    rcases hX.cluster.ref_operation hr he with ⟨pc, op, hget⟩ | ⟨pc, hget⟩
    · exact (hbefore g hg e.2 hlt _ (by rwa [hp])).1 op rfl
    · exact (hbefore g hg e.2 hlt _ (by rwa [hp])).2 rfl
  by_cases heq : e.2 = first g
  · have hpair : e = (g, first g) := Prod.ext heg heq
    subst e
    exact ⟨r, hr, he⟩
  · obtain ⟨ev, hget⟩ := hX.cluster.ref_present hr he
    have hlen : e.2 < (X.tr g).length := by simpa only [heg] using len_of_get hget
    obtain ⟨pc, op, ha⟩ := hop g hg (by omega)
    exact ClusterBlocking.of_consistent hX (g, first g) pc op ha
      (by change first g + 1 < (X.tr g).length; omega)

/-- **A completed cluster wait forces every member of its cluster to have recorded its first
arrival, in generation zero**, whatever the arrival's qualifier, in a one-dimensional launch. -/
theorem first_arrival_of_completed_wait_any (hX : Consistent L K A mem0 X)
    (hblock : 0 < L.block) (hone : L.OneDim) {rel : Bool}
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (harrive : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc al, X.get (g, first g) = some ⟨pc, .cluster (.arrive rel al)⟩)
    {g phase : Nat} {waiter : EvId} (hg : g < L.threads)
    (hw : ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (g / L.block)))
      (X.clusters (L.clusterOfCta (g / L.block))) waiter phase) :
    ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt (L.clusterOfCta (g / L.block)))
      (X.clusters (L.clusterOfCta (g / L.block))) (g, first g) 0 rel := by
  have hop : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc op, X.get (g, first g) = some ⟨pc, .cluster op⟩ := fun g hg hl => by
    obtain ⟨pc, al, h⟩ := harrive g hg hl
    exact ⟨pc, _, h⟩
  have hszc : L.clusterSizeAt (L.clusterOfCta (g / L.block)) = L.clusterSize.val :=
    L.oneDim_clusterSizeAt hone _
  have hsize : 0 < L.block * L.clusterSize.val := Nat.mul_pos hblock L.clusterSize.pos
  let localg := g % (L.block * L.clusterSize.val)
  have hlocal : localg < L.block * L.clusterSize.val := Nat.mod_lt g hsize
  have hglobal : L.clusterStart (L.clusterOfCta (g / L.block)) * L.block + localg = g := by
    have hdm : g / (L.block * L.clusterSize.val) * (L.block * L.clusterSize.val) +
        g % (L.block * L.clusterSize.val) = g := by
      rw [Nat.mul_comm (g / (L.block * L.clusterSize.val)), Nat.add_comm, Nat.mod_add_div]
    dsimp only [localg]
    rw [Launch.oneDim_clusterStart hone, Launch.oneDim_clusterOfCta hone,
      Nat.div_div_eq_div_mul, Nat.mul_assoc, Nat.mul_comm L.clusterSize.val L.block]
    exact hdm
  have hc : L.clusterOfCta (g / L.block) < L.nclusters := by
    obtain ⟨i, s, t, cta, warp, lanes, j, hi, _⟩ := hw
    by_contra hn
    rw [hX.cluster.2.1 _ (by omega)] at hi
    cases hi
  have hsource := (hX.cluster.2.2 _ hc).2.1
  have hr : ClusterRecorded L X (g, first g) := by
    rcases hw.member_arrival_or_exit (by rw [hszc]; exact hlocal) with
        ⟨cta, warp, release, lanes, e, hr, he⟩ | ⟨e, hr⟩
    · obtain ⟨_, hglobal', _, _, _⟩ := hsource _ hr (localg, e) he
      exact first_recorded_any hX hbefore hop hg hr
        (List.mem_map.mpr ⟨(localg, e), he, rfl⟩) (hglobal'.trans hglobal)
    · obtain ⟨_, hglobal', _, _⟩ := hsource _ hr
      exact first_recorded_any hX hbefore hop hg hr
        (by simp [ClusterBarrier.Record.refs]) (hglobal'.trans hglobal)
  obtain ⟨ev, hget⟩ := hX.cluster.ref_present hr.choose_spec.1 hr.choose_spec.2
  obtain ⟨pc, al, hget'⟩ := harrive g hg (len_of_get hget)
  obtain ⟨p, ha⟩ := hX.cluster.arrivalOf_recorded_any hget' hr
  have hp := first_arrival_phase_zero hX hbefore hg ha
  simpa only [hp] using ha

/-- A wait at `first g + 1` followed by a later event `j` of `g` completed in generation zero and
is before the event in program order, whatever its qualifier. -/
theorem wait_of_post_event_any (hX : Consistent L K A mem0 X)
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (hwait : ∀ g < L.threads, first g + 1 < (X.tr g).length →
      ∃ pc al, X.get (g, first g + 1) = some ⟨pc, .cluster (.wait al)⟩)
    {g j : Nat} (hg : g < L.threads) {ev : Event} (he : X.get (g, j) = some ev)
    (hj : first g + 1 < j) :
    ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (g / L.block)))
      (X.clusters (L.clusterOfCta (g / L.block))) (g, first g + 1) 0 ∧
    baseCausality L X (g, first g + 1) (g, j) := by
  have hjlen : j < (X.tr g).length := len_of_get he
  obtain ⟨pc, al, hwget⟩ := hwait g hg (by omega)
  obtain ⟨phase, hw⟩ := hX.cluster.waitOf_returned (ClusterBlocking.of_consistent hX) hwget
    (by change first g + 1 + 1 < (X.tr g).length; omega)
  have hp := first_wait_phase_zero hX hbefore hg hw
  rw [hp] at hw
  exact ⟨hw, Relation.TransGen.single (Or.inl (po_of_source_not_access rfl hj hjlen
    (by simp [hwget, Event.acc])))⟩

/-- The start barrier's facts, for a later event `j` of `g` and a member `g0` of its cluster:
`g`'s wait at `first g + 1` observed generation zero, `g0`'s first arrival is in it, and the wait
is before the event in program order. A one-dimensional launch names the cluster-local index of
`g0`. -/
theorem start_of_post_event (hX : Consistent L K A mem0 X) (hblock : 0 < L.block)
    (hone : L.OneDim) {rel : Bool}
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (harrive : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc al, X.get (g, first g) = some ⟨pc, .cluster (.arrive rel al)⟩)
    (hwait : ∀ g < L.threads, first g + 1 < (X.tr g).length →
      ∃ pc al, X.get (g, first g + 1) = some ⟨pc, .cluster (.wait al)⟩)
    {g0 g j : Nat} (hcluster : SameCluster L g0 g) {ev : Event}
    (he : X.get (g, j) = some ev) (hj : first g + 1 < j) :
    ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (g0 / L.block)))
        (X.clusters (L.clusterOfCta (g0 / L.block))) (g, first g + 1) 0 ∧
    ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt (L.clusterOfCta (g0 / L.block)))
        (X.clusters (L.clusterOfCta (g0 / L.block))) (g0, first g0) 0 rel ∧
    baseCausality L X (g, first g + 1) (g, j) := by
  obtain ⟨hw, hwb⟩ := wait_of_post_event_any hX hbefore hwait hcluster.2.1 he hj
  have hw' : ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (g0 / L.block)))
      (X.clusters (L.clusterOfCta (g0 / L.block))) (g, first g + 1) 0 := by
    rw [hcluster.2.2]
    exact hw
  exact ⟨hw', first_arrival_of_completed_wait_any hX hblock hone hbefore harrive hcluster.1 hw',
    hwb⟩

/-- Every event of a cluster member `g` after its first cluster wait is cluster-synchronized
after every event of its peer `g0` before the peer's first arrival. -/
theorem clusterSync_of_post_event (hX : Consistent L K A mem0 X) (hblock : 0 < L.block)
    (hone : L.OneDim)
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (harrive : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc, X.get (g, first g) = some ⟨pc, .cluster (.arrive true true)⟩)
    (hwait : ∀ g < L.threads, first g + 1 < (X.tr g).length →
      ∃ pc, X.get (g, first g + 1) = some ⟨pc, .cluster (.wait true)⟩)
    {g0 g j i : Nat} (hcluster : SameCluster L g0 g) {ev : Event}
    (he : X.get (g, j) = some ev) (hj : first g + 1 < j) (hi : i < first g0) :
    ClusterSync L X (g0, i) (g, j) := by
  obtain ⟨hw', ha, _⟩ := start_of_post_event hX hblock hone hbefore
    (fun g hg hl => (harrive g hg hl).imp fun _ h => ⟨_, h⟩)
    (fun g hg hl => (hwait g hg hl).imp fun _ h => ⟨_, h⟩) hcluster he hj
  obtain ⟨_, _, hapresent⟩ := hX.cluster.arrival_present ha
  exact ⟨hcluster, first g0, first g + 1, ⟨0, ha, hw'⟩, len_of_get hapresent, hi, hj,
    len_of_get he⟩

/-- The initialization of `g0` at index `i < first g0` is published to every event of a
cluster member `g` after its first cluster wait. -/
theorem init_published_of_post (hX : Consistent L K A mem0 X) (hblock : 0 < L.block)
    (hone : L.OneDim)
    (hbefore : ∀ g < L.threads, ∀ j < first g, ∀ ev, X.get (g, j) = some ev →
      (∀ op : ClusterOp, ev.kind ≠ .cluster op) ∧ ev.kind ≠ .exit)
    (harrive : ∀ g < L.threads, first g < (X.tr g).length →
      ∃ pc, X.get (g, first g) = some ⟨pc, .cluster (.arrive true true)⟩)
    (hwait : ∀ g < L.threads, first g + 1 < (X.tr g).length →
      ∃ pc, X.get (g, first g + 1) = some ⟨pc, .cluster (.wait true)⟩)
    {g0 g j i : Nat} (m : Loc) (hcluster : SameCluster L g0 g) {ev : Event}
    (he : X.get (g, j) = some ev) (hj : first g + 1 < j) (hi : i < first g0) :
    InitPublished L X (g0, i) (g, j) m :=
  Or.inl (Relation.TransGen.single (Or.inr (Or.inr (Or.inr (Or.inl
    (clusterSync_of_post_event hX hblock hone hbefore harrive hwait hcluster he hj hi))))))

end FirstPhase

end
end PTX

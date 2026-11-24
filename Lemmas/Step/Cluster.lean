-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Released
public import Lemmas.Cluster.ClusterRecordSnoc
public import Lemmas.Cluster.ClusterFirstPhase
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Tcgen05.TcReadSemanticFrame
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Async.AsyncChain
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Tmem.TmemPairCompletionFrame
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Protocol.ClusterPhase
public import Lemmas.Cluster.ClusterExitCompletion
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Order.WaitingClosure

@[expose] public section

/-! # Cluster barrier warp records as a progress step

A proof tool for the progress argument about `barrier.cluster.arrive` and `barrier.cluster.wait`.
When every lane of a warp of a CTA has its last event at the same cluster operation, unrecorded,
the warp's record can be appended to the cluster history of the CTA's cluster. Generically in the
kernel `K` and the assumptions `A`:

* `arrival_consistent`, `wait_consistent`: when the cluster barrier run accepts the record, the
  extended execution is `Consistent`, extends the old one, and has the same size (records are not
  counted by `Execution.size`).
* `arrival_maximal`, `wait_maximal`: appending the record to a maximal execution gives a maximal
  execution.
* `wait_open_witness`: the converse for waits. If the lane's own arrival belongs to the open
  phase, some live thread of the cluster has not arrived in that phase, and the number of arrival
  records containing it is at most the phase index.

The caller supplies the lane facts, the acceptance by the run, and the well-formedness of the
assumptions in the extended execution (`hasm`), as in `Lemmas/Step/Released.lean`. Acceptance is
the condition `ClusterHistoryOk` already requires of the extended history: an arrival is rejected
exactly when a lane still has an unwaited earlier arrival, and a wait exactly when its own
generation is still open. The dependency and happens-before facts are derived here: the appended
lanes are terminal cluster operations, so their needs (`clusterNeeds`) are the only ones that the
record adds, they fill only needs of lanes of the same record, and the append creates
synchronization only into a wait, which has no later event. The readiness of every returned event
(`DependencyOk.ready`) carries over because a cluster operation outside the record keeps its
records, arrivals and exits. -/

namespace PTX.Step
open PTX
noncomputable section

/-- The execution with the record `r` appended to the cluster history of cluster `c`. Only the
cluster histories change; threads, memory, objects and every other resource stay the same. -/
def _root_.PTX.Execution.withClusterRecord (X : Execution) (c : Nat)
    (r : ClusterBarrier.Record EvId) : Execution :=
  {X with clusters := ClusterRecordSnoc.clusters X c r}

theorem _root_.PTX.Execution.clusters_withClusterRecord_self (X : Execution) (c : Nat)
    (r : ClusterBarrier.Record EvId) :
    (X.withClusterRecord c r).clusters c = X.clusters c ++ [r] := by
  simp [Execution.withClusterRecord, ClusterRecordSnoc.clusters]

theorem _root_.PTX.Execution.clusters_withClusterRecord_ne (X : Execution) {c c' : Nat}
    (h : c' ≠ c) (r : ClusterBarrier.Record EvId) :
    (X.withClusterRecord c r).clusters c' = X.clusters c' := by
  simp [Execution.withClusterRecord, ClusterRecordSnoc.clusters, h]


theorem wait_open_finish_wit (threads : Nat) (s : ClusterBarrier.State) :
    ∀ x ∈ (ClusterBarrier.finish threads s).arrived,
      ∃ h, h < threads ∧ h ∉ (ClusterBarrier.finish threads s).arrived ∧
        h ∉ (ClusterBarrier.finish threads s).exited := by
  by_cases hc : ∀ x ∈ Finset.range threads, x ∈ s.arrived ∨ x ∈ s.exited
  · simp only [ClusterBarrier.finish, ite_eq_left hc]
    intro x hx
    simp at hx
  · simp only [ClusterBarrier.finish, ite_eq_right hc]
    intro x _
    simp only [not_forall, not_or] at hc
    obtain ⟨g, hg, hna, hne⟩ := hc
    exact ⟨g, Finset.mem_range.mp hg, hna, hne⟩

theorem wait_open_finish_J (threads : Nat) (u : ClusterBarrier.State)
    (hb : ∀ g phase, u.lastArrival g = some phase → phase ≤ u.phase)
    (hJ : ∀ g, u.lastArrival g = some u.phase → g ∈ u.arrived) :
    ∀ g, (ClusterBarrier.finish threads u).lastArrival g =
        some (ClusterBarrier.finish threads u).phase →
      g ∈ (ClusterBarrier.finish threads u).arrived := by
  by_cases hc : ∀ x ∈ Finset.range threads, x ∈ u.arrived ∨ x ∈ u.exited
  · intro g hg
    simp only [ClusterBarrier.finish, ite_eq_left hc] at hg ⊢
    exact absurd (hb g (u.phase + 1) hg) (by omega)
  · intro g hg
    simp only [ClusterBarrier.finish, ite_eq_right hc] at hg ⊢
    exact hJ g hg

theorem wait_open_perform {threads : Nat} {s t : ClusterBarrier.State}
    {a : ClusterBarrier.Action} (hs : ClusterBarrier.Sound s)
    (hJ : ∀ g, s.lastArrival g = some s.phase → g ∈ s.arrived)
    (hW : ∀ x ∈ s.arrived, ∃ h, h < threads ∧ h ∉ s.arrived ∧ h ∉ s.exited)
    (hp : ClusterBarrier.perform threads s a = .done t) :
    (∀ g, t.lastArrival g = some t.phase → g ∈ t.arrived) ∧
      ∀ x ∈ t.arrived, ∃ h, h < threads ∧ h ∉ t.arrived ∧ h ∉ t.exited := by
  cases a with
  | arrive j _ =>
    have ht := ClusterBarrier.perform_arrive_eq hp
    subst ht
    refine ⟨wait_open_finish_J threads _ ?_ ?_, wait_open_finish_wit threads _⟩
    · intro g phase hg
      by_cases hgj : g = j
      · subst hgj
        have h1 : s.phase = phase := by simpa using hg
        exact le_of_eq h1.symm
      · have h1 : s.lastArrival g = some phase := by simpa [hgj] using hg
        exact hs.2 g phase h1
    · intro g hg
      by_cases hgj : g = j
      · subst hgj
        exact Finset.mem_insert_self _ _
      · have h1 : s.lastArrival g = some s.phase := by simpa [hgj] using hg
        exact Finset.mem_insert_of_mem (hJ g h1)
  | wait j =>
    have ht := ClusterPhase.perform_wait_eq hp
    subst ht
    exact ⟨hJ, hW⟩
  | exit j =>
    have ht := ClusterPhase.perform_exit_eq hp
    subst ht
    exact ⟨wait_open_finish_J threads { s with exited := insert j s.exited } hs.2 hJ,
      wait_open_finish_wit threads { s with exited := insert j s.exited }⟩

theorem wait_open_performAll {threads : Nat} {s t : ClusterBarrier.State}
    {actions : List ClusterBarrier.Action} (hs : ClusterBarrier.Sound s)
    (hJ : ∀ g, s.lastArrival g = some s.phase → g ∈ s.arrived)
    (hW : ∀ x ∈ s.arrived, ∃ h, h < threads ∧ h ∉ s.arrived ∧ h ∉ s.exited)
    (hp : ClusterBarrier.performAll threads s actions = .done t) :
    (∀ g, t.lastArrival g = some t.phase → g ∈ t.arrived) ∧
      ∀ x ∈ t.arrived, ∃ h, h < threads ∧ h ∉ t.arrived ∧ h ∉ t.exited := by
  induction actions generalizing s with
  | nil => cases hp; exact ⟨hJ, hW⟩
  | cons a actions ih =>
    simp only [ClusterBarrier.performAll] at hp
    cases hstep : ClusterBarrier.perform threads s a with
    | blocked => rw [hstep] at hp; cases hp
    | fault _ => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      obtain ⟨hJu, hWu⟩ := wait_open_perform hs hJ hW hstep
      exact ih (ClusterBarrier.sound_perform hs hstep) hJu hWu hp

theorem wait_open_record {α : Type} {block ctas : Nat} {s t : ClusterBarrier.State}
    {r : ClusterBarrier.Record α} (hs : ClusterBarrier.Sound s)
    (hJ : ∀ g, s.lastArrival g = some s.phase → g ∈ s.arrived)
    (hW : ∀ x ∈ s.arrived, ∃ h, h < block * ctas ∧ h ∉ s.arrived ∧ h ∉ s.exited)
    (hp : r.perform block ctas s = .done t) :
    (∀ g, t.lastArrival g = some t.phase → g ∈ t.arrived) ∧
      ∀ x ∈ t.arrived, ∃ h, h < block * ctas ∧ h ∉ t.arrived ∧ h ∉ t.exited := by
  cases r with
  | exit g _ => exact wait_open_perform (threads := block * ctas) (a := .exit g) hs hJ hW hp
  | arrival _ _ _ _ =>
    simp only [ClusterBarrier.Record.perform] at hp
    split at hp
    · split at hp
      · cases hp
      exact wait_open_performAll hs hJ hW hp
    · cases hp
  | wait _ _ _ =>
    simp only [ClusterBarrier.Record.perform] at hp
    split at hp
    · exact wait_open_performAll hs hJ hW hp
    · cases hp

theorem wait_open_run {α : Type} {block ctas : Nat} {s t : ClusterBarrier.State}
    {h : List (ClusterBarrier.Record α)} (hs : ClusterBarrier.Sound s)
    (hJ : ∀ g, s.lastArrival g = some s.phase → g ∈ s.arrived)
    (hW : ∀ x ∈ s.arrived, ∃ k, k < block * ctas ∧ k ∉ s.arrived ∧ k ∉ s.exited)
    (hp : ClusterBarrier.run block ctas s h = .done t) :
    (∀ g, t.lastArrival g = some t.phase → g ∈ t.arrived) ∧
      ∀ x ∈ t.arrived, ∃ k, k < block * ctas ∧ k ∉ t.arrived ∧ k ∉ t.exited := by
  induction h generalizing s with
  | nil => cases hp; exact ⟨hJ, hW⟩
  | cons r rs ih =>
    simp only [ClusterBarrier.run] at hp
    cases hstep : r.perform block ctas s with
    | blocked => rw [hstep] at hp; cases hp
    | fault _ => rw [hstep] at hp; cases hp
    | done u =>
      rw [hstep] at hp
      obtain ⟨hJu, hWu⟩ := wait_open_record hs hJ hW hstep
      exact ih (ClusterBarrier.sound_record hs hstep) hJu hWu hp

theorem wait_open_witness {block ctas g : Nat} {H : List (ClusterBarrier.Record EvId)}
    {s : ClusterBarrier.State} (hs : ClusterBarrier.run block ctas {} H = .done s)
    (hopen : s.lastArrival g = some s.phase) :
    ∃ h, h < block * ctas ∧ h ∉ s.exited ∧ H.countP (ClusterPhase.ownArrival h) ≤ s.phase := by
  obtain ⟨hJ, hW⟩ := wait_open_run ClusterBarrier.sound_empty
    (by intro x hx; simp at hx) (by intro x hx; simp at hx) hs
  obtain ⟨k, hk, hna, hne⟩ := hW g (hJ g hopen)
  have hcount := ClusterPhase.run_weight ClusterBarrier.sound_empty hs hk hne
  have h0 : ClusterPhase.weight k ({} : ClusterBarrier.State) = 0 := by
    simp [ClusterPhase.weight]
  have h1 : ClusterPhase.weight k s = s.phase := by
    simp [ClusterPhase.weight, hna]
  exact ⟨k, hk, hne, by omega⟩


section TerminalWaits
open PTX AsyncCopy MBarrier

/-- A cluster barrier operation issues no asynchronous stage. -/
theorem cluster_no_async {L : Launch} {X : Execution} (hv : EffectValidity L X) {i : EvId}
    {pc : Nat} {op : ClusterOp} (hi : X.get i = some ⟨pc, .cluster op⟩) (p : Part) :
    ¬ X.AsyncPresent i p := by
  intro hp
  have ht := hv.tma
  have copyOrigin (hn : nonempty (X.async.copies i)) : False := by
    obtain ⟨s, hs, _⟩ := ht.1 i hn
    simp [issuedBy, hi] at hs
  have mmaOrigin (hs : X.async.mmaStarted i = true) : False := by
    rcases ht.2.1.1 i hs with
      ⟨d, spec, accum, mask, operands, ⟨pc', hm⟩, _⟩ | ⟨c, operands, ⟨pc', hm⟩, _⟩ |
      ⟨s, operands, ⟨pc', hm⟩, _⟩ <;> (rw [hi] at hm; cases hm)
  have tensorOrigin {o : TensorCopy.Observation} (ho : X.tensor i = some o) : False := by
    obtain ⟨addr, pc', hk⟩ := (hv.tensor i o ho).1
    rw [hi] at hk
    cases hk
  have storeOrigin {o : TensorStore.Observation} (ho : X.tensorStores i = some o) : False := by
    obtain ⟨addr, pc', hk⟩ := (hv.store i o ho).1
    rw [hi] at hk
    cases hk
  have clcOrigin (hn : (X.clc i).resolved.isSome ∨ (X.clc i).written.Nonempty ∨
      (X.clc i).notified.Nonempty) : False := by
    obtain ⟨s, targets, pc', hk⟩ := hv.clc.2.2.1 i hn
    rw [hi] at hk
    cases hk
  cases p with
  | readCopy => exact copyOrigin ⟨.read .copy, hp⟩
  | writeCopy => exact copyOrigin ⟨.write .copy, hp⟩
  | notifyCopy => exact copyOrigin ⟨.notify .copy, hp⟩
  | writeElem j => exact copyOrigin ⟨.write (.elem j), hp⟩
  | oldElem j => exact copyOrigin ⟨.old (.elem j), hp⟩
  | mmaDone => exact mmaOrigin (ht.2.1.2 i hp)
  | readLoad x y k | notifyLoad => obtain ⟨o, ho, _⟩ := hp; exact tensorOrigin ho
  | writeLoad x y k => obtain ⟨o, slot, value, ho, _⟩ := hp; exact tensorOrigin ho
  | readStore x y k | writeStore x y k | oldStore x y k | readsDone | fullDone =>
    obtain ⟨o, ho, _⟩ := hp; exact storeOrigin ho
  | readCta | readElem j | oldCopy | oldLoad | oldCta | readPrefetch | writePrefetch |
      oldPrefetch => exact hp.elim
  | resolve => exact clcOrigin (.inl hp)
  | writeCta c => exact clcOrigin (.inr (.inl ⟨c, hp⟩))
  | notifyCta c => exact clcOrigin (.inr (.inr ⟨c, hp⟩))
  | tcNotify r =>
    obtain ⟨⟨s, m, ⟨pc', hk⟩, _⟩, _⟩ := hv.tcCommit i r hp
    rw [hi] at hk
    cases hk
  | mmaRead b k =>
    obtain ⟨l, byte, hf, -⟩ := hp
    rcases hf with ⟨_, _, _, _, ⟨pc', hm⟩, _⟩ | ⟨_, _, _, ⟨pc', hm⟩, _, _, _, _⟩ <;>
      (rw [hi] at hm; cases hm)
  | arriveOn =>
    obtain ⟨⟨m, noinc, pc', hk⟩, _⟩ := ht.2.2.2 i hp
    rw [hi] at hk
    cases hk

/-- A cluster barrier operation is the source of no mbarrier record. -/
theorem cluster_no_object_before {L : Launch} {X : Execution} (hv : EffectValidity L X)
    {i : EvId} {pc : Nat} {op : ClusterOp} (hi : X.get i = some ⟨pc, .cluster op⟩) (m : Loc)
    (f : Ref) : ¬ MBarrier.Before (X.objects m) (.thread i) f := by
  rintro ⟨a, b, ra, rb, ha, hid, _⟩
  have ho := ((hv.tma.2.2.1 m).2.1 ra (List.mem_of_getElem? ha)).1
  rw [hid] at ho
  simp [objectAction, hi] at ho

/-- No reference of a CTA barrier record is a cluster barrier operation: an arrival record holds
`bar` events and an exit record an exit. -/
theorem ctaBarRef_not_cluster {L : Launch} {X : Execution} (hb : CtaBarHistoryOk L X) {c : Nat}
    {r : CtaBarrier.Record EvId} {x : EvId} {pc : Nat} {op : ClusterOp}
    (hr : r ∈ X.barriers c) (hx : x ∈ r.refs) (hget : X.get x = some ⟨pc, .cluster op⟩) :
    False := by
  have hcl : c < L.grid := by
    by_contra hn
    rw [hb.1 c (by omega)] at hr
    cases hr
  have hs := (hb.2 c hcl).2.1 r hr
  cases r with
  | exit g f =>
    simp only [CtaBarrier.Record.refs, List.mem_singleton] at hx
    subst hx
    obtain ⟨_, _, pc', hk⟩ := hs
    rw [hk] at hget
    cases hget
  | arrival id warp count lanes =>
    simp only [CtaBarrier.Record.refs, List.mem_map] at hx
    obtain ⟨p, hp', rfl⟩ := hx
    obtain ⟨_, _, pc', mode, hk⟩ := hs p hp'
    rw [hk] at hget
    cases hget

/-- A cluster barrier operation fills no need of a masked warp collective: the lane of such a need
is an event of the collective's class or an exit. -/
theorem maskNeeds_not_cluster {Q V : Type} {L : Launch} {X : Execution} {e j : EvId} {pc : Nat}
    {op : ClusterOp} {c : Kind → Option (WarpPart Q V)} (hc : ∀ op, c (.cluster op) = none)
    (he : X.get e = some ⟨pc, .cluster op⟩) {fills : AsyncCopy.Ref → Prop}
    (hm : Need.node fills ∈ maskNeeds L c X j) (hf : fills (.thread e)) : False := by
  unfold maskNeeds at hm
  split at hm
  · obtain ⟨l, -, hl⟩ := List.mem_map.mp hm
    cases hl
    obtain ⟨j', heq, hmw⟩ := hf
    cases heq
    rcases MaskWait.src (L := L) hmw with ⟨pc', k, p, hget, hk⟩ | ⟨pc', hget⟩
    · rw [he] at hget
      cases hget
      rw [hc] at hk
      cases hk
    · rw [he] at hget
      cases hget
  · simp at hm

/-- A cluster barrier operation `e` that fills a need of `j` is a lane of a record of `j`'s cluster
that holds `j` as well, or an arrival of the phase that the cluster wait `j` waits for: the needs
of every other kind are filled by events of that kind, by exits, by CTA barrier or allocator
participants, by object records or by asynchronous stages. -/
theorem cluster_witness_cases {L : Launch} {X : Execution} {e j : EvId} {pc : Nat}
    {op : ClusterOp} (hv : EffectValidity L X) (hc : ClusterHistoryOk L X)
    (hb : CtaBarHistoryOk L X) (he : X.get e = some ⟨pc, .cluster op⟩)
    (ho : Witness L X (.thread e) j) :
    (∃ r ∈ X.clusters (L.clusterOfCta (j.1 / L.block)), e ∈ r.refs ∧ j ∈ r.refs) ∨
      ∃ phase release,
        ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt (L.clusterOfCta (j.1 / L.block)))
          (X.clusters (L.clusterOfCta (j.1 / L.block))) e phase release ∧
        ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (j.1 / L.block)))
          (X.clusters (L.clusterOfCta (j.1 / L.block))) j phase := by
  obtain ⟨fills, hmem, -, hfill⟩ := ho
  have hp := hv.tmemPair
  have exitRef : ∀ {c i g : Nat}, (X.clusters c)[i]? = some (ClusterBarrier.Record.exit g e) →
      False := by
    intro c i g hi
    have hr := List.mem_of_getElem? hi
    have hcn : c < L.nclusters := by
      by_contra hn
      rw [hc.2.1 c (by omega)] at hr
      cases hr
    obtain ⟨-, -, pc', hget⟩ := (hc.2.2 c hcn).2.1 _ hr
    rw [he] at hget
    cases hget
  cases hg : X.get j with
  | none => simp only [Needs, hg, List.not_mem_nil] at hmem
  | some ev =>
    obtain ⟨pcj, kind⟩ := ev
    simp only [Needs, hg] at hmem
    cases kind
    case cluster op' =>
      simp only [KindNeeds, clusterNeeds, List.mem_append] at hmem
      rcases hmem with hwarp | hcount
      · obtain ⟨h, -, hfl⟩ := List.mem_map.mp hwarp
        cases hfl
        obtain ⟨i, r, y, hi, hjmem, heq, -, hopt⟩ := hfill
        cases heq
        rcases hopt with hymem | ⟨i', g, -, hexit⟩
        · exact .inl ⟨r, List.mem_of_getElem? hi, hymem, hjmem⟩
        · exact (exitRef hexit).elim
      · cases op' with
        | arrive release aligned => simp only [List.not_mem_nil] at hcount
        | wait aligned =>
          obtain ⟨y, -, hcc⟩ := List.mem_flatMap.mp hcount
          by_cases hcl : ClusterCounted L X j y
          · simp only [needsIf, hcl, ite_true, List.mem_singleton, Need.node.injEq] at hcc
            rw [hcc] at hfill
            cases hfill
            rcases hcl with ⟨phase, release, hw, ha⟩ | ⟨i, i', r, g, -, -, -, -, hexit⟩
            · exact .inr ⟨phase, release, ha, hw⟩
            · exact (exitRef hexit).elim
          · simp only [needsIf, hcl, ite_false, List.not_mem_nil] at hcc
    case bar id count mode =>
      exfalso
      simp only [KindNeeds, ctaBarNeeds, List.mem_append] at hmem
      rcases hmem with hwarp | hrest
      · obtain ⟨h, -, hfl⟩ := List.mem_map.mp hwarp
        cases hfl
        obtain ⟨i, r, y, hi, -, heq, -, hopt⟩ := hfill
        cases heq
        rcases hopt with hymem | ⟨i', g, -, hexit⟩
        · exact ctaBarRef_not_cluster hb (List.mem_of_getElem? hi) hymem he
        · exact ctaBarRef_not_cluster hb (List.mem_of_getElem? hexit)
            (by simp [CtaBarrier.Record.refs]) he
      · cases mode with
        | arrive => simp only [List.not_mem_nil] at hrest
        | sync =>
          simp only [List.mem_cons] at hrest
          rcases hrest with hcond | hcount
          · cases hcond
          · obtain ⟨y, -, hcc⟩ := List.mem_flatMap.mp hcount
            by_cases hcl : CtaBarCounted L X j y
            · simp only [needsIf, hcl, ite_true, List.mem_singleton, Need.node.injEq] at hcc
              rw [hcc] at hfill
              cases hfill
              obtain ⟨key, ic, -, -, i, r, hi, hyr, -, -⟩ := hcl
              exact ctaBarRef_not_cluster hb (List.mem_of_getElem? hi) hyr he
            · simp only [needsIf, hcl, ite_false, List.not_mem_nil] at hcc
    case shfl =>
      simp only [KindNeeds] at hmem
      exact (maskNeeds_not_cluster (fun _ => rfl) he hmem hfill).elim
    case vote =>
      simp only [KindNeeds] at hmem
      exact (maskNeeds_not_cluster (fun _ => rfl) he hmem hfill).elim
    case voteMode =>
      simp only [KindNeeds] at hmem
      exact (maskNeeds_not_cluster (fun _ => rfl) he hmem hfill).elim
    case redux =>
      simp only [KindNeeds] at hmem
      exact (maskNeeds_not_cluster (fun _ => rfl) he hmem hfill).elim
    case match_ =>
      simp only [KindNeeds] at hmem
      exact (maskNeeds_not_cluster (fun _ => rfl) he hmem hfill).elim
    case elect mask inst leader =>
      exfalso
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', pc', leader', heq, hget⟩ := hfill
      cases heq
      rw [he] at hget
      cases hget
    case warpBar mask inst =>
      exfalso
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', heq, ⟨pc', hget⟩⟩ := hfill
      cases heq
      rw [he] at hget
      cases hget
    case matrix op own recv =>
      exfalso
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', heq, hmat | hexit⟩ := hfill
      · cases heq
        obtain ⟨⟨ev', hget, hbit⟩, -⟩ := hmat
        rw [he] at hget
        cases hget
        simp [isMatrix] at hbit
      · cases heq
        obtain ⟨⟨pc', hget⟩, -⟩ := hexit
        rw [he] at hget
        cases hget
    case setMaxReg increase count' inst =>
      exfalso
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', heq, hsr⟩ := hfill
      cases heq
      obtain ⟨-, -, pc', inc', n', einst', finst', -, hreq⟩ := hsr
      simp only [SetMaxNReg.Request] at hreq
      rw [he] at hreq
      cases hreq
    case bulkWait mode remaining =>
      exfalso
      simp only [KindNeeds, groupNeeds, List.mem_flatMap] at hmem
      obtain ⟨y, -, hfl⟩ := hmem
      unfold needsIf at hfl
      split at hfl
      · obtain ⟨p, -, hfl⟩ := List.mem_map.mp hfl
        cases hfl
        cases hfill
      · simp at hfl
    case asyncWait remaining =>
      exfalso
      simp only [KindNeeds, groupNeeds, List.mem_flatMap] at hmem
      obtain ⟨y, -, hfl⟩ := hmem
      unfold needsIf at hfl
      split at hfl
      · obtain ⟨p, -, hfl⟩ := List.mem_map.mp hfl
        cases hfl
        cases hfill
      · simp at hfl
    case wait m parity ok acquire scope =>
      exfalso
      cases ok with
      | false => simp only [KindNeeds, Bool.false_eq_true, ite_false, List.not_mem_nil] at hmem
      | true =>
        simp only [KindNeeds, ite_true, pollNeeds] at hmem
        obtain ⟨r, hr, hfl⟩ := List.mem_flatMap.mp hmem
        by_cases hmo : MbarObserved X r.id (.thread j)
        · simp only [needsIf, hmo, ite_true, List.mem_singleton, Need.node.injEq] at hfl
          rw [hfl] at hfill
          have hact := ((hv.tma.2.2.1 m).2.1 r hr).1
          rw [← hfill] at hact
          simp [objectAction, he] at hact
        · simp only [needsIf, hmo, ite_false, List.not_mem_nil] at hfl
    case tc k =>
      exfalso
      have tcLane : ∀ {fills : AsyncCopy.Ref → Prop}, Need.node fills ∈ tcNeeds L X j →
          fills (.thread e) → False := by
        intro fills hm hf
        obtain ⟨h, -, hfl⟩ := List.mem_map.mp hm
        cases hfl
        obtain ⟨j', heq, ⟨⟨ev', hget, hbit⟩, -⟩⟩ := hf
        cases heq
        rw [he] at hget
        cases hget
        simp [isTcColl] at hbit
      cases k
      case resource group dst request =>
        simp only [KindNeeds, resourceNeeds, List.mem_append, List.mem_cons] at hmem
        rcases hmem with (htc | hcond | hrest) | hresult
        · exact tcLane htc hfill
        · cases hcond
        · by_cases hmw : Tmem.Pair.MustWait X j
          · simp only [needsIf, hmw, ite_true] at hrest
            rcases List.mem_cons.mp hrest with hcond | hrest
            · cases hcond
            · rcases List.mem_append.mp hrest with hpair | hreuse
              · cases group with
                | two =>
                  simp only [List.mem_map] at hpair
                  obtain ⟨l, -, hfl⟩ := hpair
                  cases hfl
                  obtain ⟨q, hq, hpe⟩ := hfill
                  rcases hpe with ⟨-, heq⟩ | ⟨-, heq⟩
                  · cases heq
                    obtain ⟨-, -, hgetall, -⟩ := (hp.2.1 q hq).1.2.2.1
                    have hget := hgetall l
                    rw [he] at hget
                    cases hget
                  · cases heq
                    obtain ⟨-, -, hgetall, -⟩ := (hp.2.1 q hq).1.2.1
                    have hget := hgetall l
                    rw [he] at hget
                    cases hget
                | one => simp only [List.not_mem_nil] at hpair
              · cases request with
                | alloc columns =>
                  simp only [List.mem_flatMap] at hreuse
                  obtain ⟨jj, -, hfl⟩ := hreuse
                  by_cases hrr : ReuseRelease L X j jj
                  · simp only [hrr, ite_true, List.mem_map] at hfl
                    obtain ⟨l, -, hfl⟩ := hfl
                    cases hfl
                    obtain ⟨d, hdmem, heq⟩ := hfill
                    cases heq
                    obtain ⟨-, -, hgetall, -⟩ :=
                      ((hp.1 (j.1 / L.block)).1 d (List.mem_of_getElem? hdmem)).2.2
                    have hget := hgetall l
                    rw [he] at hget
                    cases hget
                  · simp only [hrr, ite_false, List.not_mem_nil] at hfl
                | dealloc base columns => simp only [List.not_mem_nil] at hreuse
                | relinquish => simp only [List.not_mem_nil] at hreuse
          · simp only [needsIf, hmw, ite_false, List.not_mem_nil] at hrest
        · cases Tmem.Pair.allocResultNeeds_node L hresult
          obtain ⟨store, _, _, _, heq, hwrite⟩ := Tmem.Pair.AllocResultFill.written L hfill
          cases heq
          rw [he] at hwrite
          cases hwrite
      case ld => exact tcLane hmem hfill
      case st => exact tcLane hmem hfill
      case waitLd => exact tcLane hmem hfill
      case waitSt => exact tcLane hmem hfill
      all_goals simp only [KindNeeds, List.not_mem_nil] at hmem
    all_goals simp only [KindNeeds, List.not_mem_nil] at hmem

/-- A terminal cluster operation that no cluster barrier history records has no waiting
dependency except its own return: it issues no asynchronous or object effect, it is no lane of a
CTA barrier, shuffle, collective, election, warp barrier, register-pool or allocator record, it
writes no memory and is no fence, and it fills no need of another event. -/
theorem terminal_cluster_waits_cases {L : Launch} {X : Execution} {e : EvId} {pc : Nat}
    {op : ClusterOp} (hv : EffectValidity L X) (hc : ClusterHistoryOk L X)
    (hb : CtaBarHistoryOk L X)
    (he : X.get e = some ⟨pc, .cluster op⟩) (ht : e.2 + 1 = (X.tr e.1).length)
    (hun : ¬ ClusterRecorded L X e)
    {b : Bool} {v : Ref × Bool} (hw : Waits L X (.thread e, b) v) :
    b = false ∧ v = (.thread e, true) := by
  have hp := hv.tmemPair
  have recordedOf {c : Nat} {r : ClusterBarrier.Record EvId}
      (hr : r ∈ X.clusters c) (her : e ∈ r.refs) : ClusterRecorded L X e := by
    refine ⟨r, ?_, her⟩
    rw [hc.ref_cluster hr her]
    exact hr
  have arrivalRec {c phase ctas : Nat} {release : Bool}
      (ha : ClusterBarrier.ArrivalOf L.block ctas (X.clusters c) e phase release) :
      ClusterRecorded L X e := by
    obtain ⟨i', _, _, cta, warp, lanes, g, hi', _, hmem, _⟩ := ha
    exact recordedOf (List.mem_of_getElem? hi') (List.mem_map.mpr ⟨(g, e), hmem, rfl⟩)
  have clusterRec {f : EvId} {b1 b2 : Bool} (hcl : ClusterWaits L X e f b1 b2) :
      ClusterRecorded L X e := by
    rcases hcl.2.2 with ⟨c, _, _, r, _, hr, _, _, her, _, _, _⟩ |
      ⟨_, _, c, r, hr, her, _⟩ | ⟨_, _, _, c, ha, _⟩ | ⟨_, _, _, c, ha, _⟩
    · exact recordedOf (List.mem_of_getElem? hr) her
    · exact recordedOf hr her
    · exact arrivalRec ha
    · exact arrivalRec ha
  have noWrite {a : Acc} {bs : List Byte} (h : X.MemWrites (.thread e) a bs) : False := by
    rcases h with ⟨pc', hw'⟩ | ⟨old, pc', hw'⟩ <;> (rw [he] at hw'; cases hw')
  have noFence {sem : FenceSem} {s : MbarScope} (h : X.ThreadFence e sem s) : False := by
    obtain ⟨pc', h'⟩ := h
    rw [he] at h'
    cases h'
  obtain ⟨f, b'⟩ := v
  rcases hw with ⟨heq, hb0, hb', _⟩ | ⟨_, _, i, j, hi, hj, hij, hnext, hlen⟩ |
    ⟨i, j, hi, hj, hbar⟩ | ⟨_, _, i, j, hi, _, _, n, ⟨⟨p, md, a, bv, cv, recv, ok, hh⟩, _⟩, _⟩ |
    ⟨_, _, i, j, hi, _, _, n, ⟨⟨ev, hh, hcoll⟩, _⟩, _⟩ | ⟨hb1, -, hst⟩ | ⟨_, _, m, ho⟩ |
    ⟨i, j, hi, _, hcluster⟩ | ⟨_, _, j, _, hwit⟩ | ⟨_, _, i, j, hi, _, hwarp⟩ |
    ⟨_, _, i, j, hi, _, hsw⟩ | ⟨i, j, hi, _, hr⟩ | ⟨_, _, i, j, hi, _, cta, hpre⟩ |
    ⟨_, _, i, j, hi, _, hfs⟩ | ⟨-, -, -, -, i, p, hi, -, -, hap, -⟩
  · exact ⟨hb0, Prod.ext heq.symm hb'⟩
  · cases hi
    rw [← hij, ← ht] at hlen
    omega
  · cases hi
    exfalso
    rcases hbar.2.2 with ⟨_, _, c, _, _, r, _, hr, _, _, her, _⟩ |
      ⟨_, _, _, key, hke, _⟩ | ⟨_, _, key, _, r, _, hr, her, _⟩
    · exact ctaBarRef_not_cluster hb (List.mem_of_getElem? hr) her he
    · obtain ⟨count, pc', mode, hk⟩ := hke.2.1
      rw [he] at hk
      cases hk
    · exact ctaBarRef_not_cluster hb (List.mem_of_getElem? hr) her he
  · cases hi; rw [he] at hh; cases hh
  · cases hi; rw [he] at hh; cases hh; cases hcoll
  · exfalso
    rcases hst with ⟨-, hbf, -⟩ | ⟨-, -, hse⟩
    · rw [hb1] at hbf
      cases hbf
    · cases f <;> simp [StageEdge] at hse
  · exact (cluster_no_object_before hv he m _ ho).elim
  · cases hi
    exact (hun (clusterRec hcluster)).elim
  · exfalso
    rcases cluster_witness_cases hv hc hb he hwit with ⟨r, hr, her, -⟩ | ⟨_, _, ha, -⟩
    · exact hun (recordedOf hr her)
    · exact hun (arrivalRec ha)
  · cases hi
    obtain ⟨_, mask, inst, ⟨p, hh'⟩, _⟩ := hwarp
    rw [he] at hh'
    cases hh'
  · cases hi
    obtain ⟨a, b2, bs, cs, hw', -⟩ := hsw
    exact (noWrite hw').elim
  · cases hi
    have noRequest {j' : EvId} (hs : SetMaxNReg.SameRequest L X e j') : False := by
      obtain ⟨_, _, p, inc, n', einst, finst, hh', _⟩ := hs
      change X.get e = some ⟨p, .setMaxReg inc n' einst⟩ at hh'
      rw [he] at hh'
      cases hh'
    exact (noRequest hr.2.2).elim
  · cases hi
    obtain ⟨_, _, _, _, hh'⟩ := Tmem.Pair.Precedes.actual hp hpre
    rw [he] at hh'
    cases hh'
  · cases hi
    exfalso
    rcases hfs with ⟨w, r, a, b2, bs, cs, se, sf, hw', -, -, hrh, -⟩ | ⟨⟨s, s', hfe, -⟩, -⟩
    · rcases hrh with ⟨rfl, -, -⟩ | ⟨sem, hfe, -⟩
      · exact noWrite hw'
      · exact noFence hfe
    · exact noFence hfe
  · cases hi
    exact (cluster_no_async hv he p hap).elim

end TerminalWaits

namespace ClusterRec

open ClusterBarrier

variable {α : Type}

/-! ## Appending one record to a history -/

theorem getElem?_snoc_cases {H : List (Record α)} {R x : Record α} {i : Nat}
    (h : (H ++ [R])[i]? = some x) : (i < H.length ∧ H[i]? = some x) ∨ (i = H.length ∧ x = R) := by
  by_cases hi : i < H.length
  · exact .inl ⟨hi, by rwa [List.getElem?_append_left hi] at h⟩
  · right
    rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at h
    obtain ⟨k, hk⟩ : ∃ k, i - H.length = k := ⟨_, rfl⟩
    rw [hk] at h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩
    | succ k => simp at h

theorem take_snoc_of_le {H : List (Record α)} {R : Record α} {i : Nat} (h : i ≤ H.length) :
    (H ++ [R]).take i = H.take i :=
  List.take_append_of_le_length h

/-- An arrival of the old history stays an arrival of the old history when the appended record
does not contain its reference. -/
theorem arrivalOf_old {block ctas p : Nat} {H : List (Record EvId)} {R : Record EvId}
    {e : EvId} {release : Bool} (he : e ∉ R.refs)
    (h : ArrivalOf block ctas (H ++ [R]) e p release) : ArrivalOf block ctas H e p release := by
  obtain ⟨i, s, t, cta, warp, lanes, g, hi, hs, hm, hph, hp⟩ := h
  rcases getElem?_snoc_cases hi with ⟨hlt, hold⟩ | ⟨rfl, hR⟩
  · refine ⟨i, s, t, cta, warp, lanes, g, hold, ?_, hm, hph, hp⟩
    unfold At at hs ⊢
    rw [take_snoc_of_le hlt.le] at hs
    exact hs
  · subst hR
    exact (he (by
      simp only [Record.refs]
      exact List.mem_map.mpr ⟨(g, e), hm, rfl⟩)).elim

/-- A wait of the old history stays a wait of the old history when the appended record does
not contain its reference. -/
theorem waitOf_old {block ctas p : Nat} {H : List (Record EvId)} {R : Record EvId}
    {e : EvId} (he : e ∉ R.refs) (h : WaitOf block ctas (H ++ [R]) e p) :
    WaitOf block ctas H e p := by
  obtain ⟨i, s, t, cta, warp, lanes, g, hi, hs, hm, hph, hp⟩ := h
  rcases getElem?_snoc_cases hi with ⟨hlt, hold⟩ | ⟨rfl, hR⟩
  · refine ⟨i, s, t, cta, warp, lanes, g, hold, ?_, hm, hph, hp⟩
    unfold At at hs ⊢
    rw [take_snoc_of_le hlt.le] at hs
    exact hs
  · subst hR
    exact (he (by
      simp only [Record.refs]
      exact List.mem_map.mpr ⟨(g, e), hm, rfl⟩)).elim

/-- A wait of a history that completes at `s` observes a phase strictly before `s.phase`. -/
theorem waitOf_phase_lt {block ctas p : Nat} {H : List (Record EvId)} {s : State}
    (hs : ClusterBarrier.run block ctas {} H = .done s) {e : EvId}
    (h : WaitOf block ctas H e p) : p < s.phase := by
  obtain ⟨i, s', t, cta, warp, lanes, g, hi, hsA, hm, hlast, hp⟩ := h
  have hA := ClusterBarrier.run_append block ctas {} (H.take i) (H.drop i)
  rw [List.take_append_drop, hs] at hA
  unfold At at hsA
  rw [hsA] at hA
  have hmono := ClusterPhase.run_phase_le hA.symm
  have hlt := ClusterPhase.wait_phase_lt hm hlast hp
  omega

/-- An arrival of a fresh reference, in the history extended by a record containing it, is
performed at the phase where the old history ends. -/
theorem arrivalOf_snoc_phase {block ctas p : Nat} {H : List (Record EvId)} {R : Record EvId}
    {s : State} (hs : ClusterBarrier.run block ctas {} H = .done s) {e : EvId} {release : Bool}
    (hfresh : ∀ r ∈ H, e ∉ r.refs)
    (h : ArrivalOf block ctas (H ++ [R]) e p release) : p = s.phase := by
  obtain ⟨i, s', t, cta, warp, lanes, g, hi, hsA, hm, hph, hp⟩ := h
  rcases getElem?_snoc_cases hi with ⟨hlt, hold⟩ | ⟨hlen, hR⟩
  · exact (hfresh _ (List.mem_of_getElem? hold) (by
      simp only [Record.refs]
      exact List.mem_map.mpr ⟨(g, e), hm, rfl⟩)).elim
  · have ht : (H ++ [R]).take i = H := by
      rw [hlen, take_snoc_of_le le_rfl, List.take_length]
    unfold At at hsA
    rw [ht, hs] at hsA
    rw [← hph, Outcome.done.inj hsA]

/-- Appending a cluster record only extends the cluster histories. -/
theorem le_withClusterRecord (X : Execution) (c : Nat) (R : ClusterBarrier.Record EvId) :
    X.le (X.withClusterRecord c R) := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9, h10, h11, h12, h13⟩ := Execution.le_refl X
  refine ⟨h1, h2, h3, h4, h5, fun c' => ?_, h7, h8, h9, h10, h11, h12, h13⟩
  by_cases hc : c' = c
  · subst hc
    rw [Execution.clusters_withClusterRecord_self]
    exact List.prefix_append _ _
  · rw [Execution.clusters_withClusterRecord_ne X hc]

/-! ## Which facts a record append can change -/

/-- An arrival of the extended history comes from an arrival of the old history when the
appended record is a wait. -/
theorem arrivalOf_of_snoc_wait {block ctas p : Nat} {H : List (Record EvId)} {R : Record EvId}
    {cta warp : Nat} {lanes : List (Nat × EvId)} (hR : R = .wait cta warp lanes)
    {e : EvId} {release : Bool} (h : ArrivalOf block ctas (H ++ [R]) e p release) :
    ArrivalOf block ctas H e p release := by
  obtain ⟨i, s, t, cta', warp', lanes', g, hi, hs, hm, hph, hp⟩ := h
  rcases getElem?_snoc_cases hi with ⟨hlt, hold⟩ | ⟨-, hx⟩
  · refine ⟨i, s, t, cta', warp', lanes', g, hold, ?_, hm, hph, hp⟩
    unfold At at hs ⊢
    rw [take_snoc_of_le hlt.le] at hs
    exact hs
  · rw [hR] at hx
    cases hx

/-- A wait of the extended history comes from a wait of the old history when the appended record
is an arrival. -/
theorem waitOf_of_snoc_arrival {block ctas p : Nat} {H : List (Record EvId)} {R : Record EvId}
    {cta warp : Nat} {release : Bool} {lanes : List (Nat × EvId)}
    (hR : R = .arrival cta warp release lanes) {e : EvId}
    (h : WaitOf block ctas (H ++ [R]) e p) : WaitOf block ctas H e p := by
  obtain ⟨i, s, t, cta', warp', lanes', g, hi, hs, hm, hph, hp⟩ := h
  rcases getElem?_snoc_cases hi with ⟨hlt, hold⟩ | ⟨-, hx⟩
  · refine ⟨i, s, t, cta', warp', lanes', g, hold, ?_, hm, hph, hp⟩
    unfold At at hs ⊢
    rw [take_snoc_of_le hlt.le] at hs
    exact hs
  · rw [hR] at hx
    cases hx

/-- Membership in a history of the reference of an arrival of that history. -/
theorem arrivalOf_mem {block ctas p : Nat} {h : List (Record EvId)} {e : EvId} {b : Bool}
    (hA : ArrivalOf block ctas h e p b) : ∃ r ∈ h, e ∈ r.refs := by
  obtain ⟨i, s, t, cta, warp, lanes, g, hi, -, hm, -, -⟩ := hA
  exact ⟨_, List.mem_of_getElem? hi, by
    simp only [Record.refs]
    exact List.mem_map.mpr ⟨(g, e), hm, rfl⟩⟩

/-- In the history extended by a fresh arrival or wait record, an arrival of a phase that a wait
outside the record waits for is an arrival of the old history, and that wait is one of the old
history: a fresh arrival is performed at the phase where the old history ends, which no old wait
has passed, and a wait record contributes no arrival. -/
theorem arrivalWait_old {block ctas phase : Nat} {H : List (Record EvId)} {R : Record EvId}
    (hR : ∀ g ref, R ≠ .exit g ref) {s : State}
    (hs : ClusterBarrier.run block ctas {} H = .done s) (hfresh : ∀ r ∈ H, ∀ e ∈ R.refs, e ∉ r.refs)
    {a w : EvId} {release : Bool} (hw : w ∉ R.refs)
    (ha : ArrivalOf block ctas (H ++ [R]) a phase release)
    (hwt : WaitOf block ctas (H ++ [R]) w phase) :
    ArrivalOf block ctas H a phase release ∧ WaitOf block ctas H w phase := by
  have hwt' := waitOf_old hw hwt
  refine ⟨?_, hwt'⟩
  by_cases haR : a ∈ R.refs
  · exfalso
    cases R with
    | arrival cta warp rel lanes =>
      have hp := arrivalOf_snoc_phase hs (fun r hr => hfresh r hr a haR) ha
      have hlt := waitOf_phase_lt hs hwt'
      omega
    | wait cta warp lanes =>
      obtain ⟨r, hr, har⟩ := arrivalOf_mem (arrivalOf_of_snoc_wait rfl ha)
      exact hfresh r hr a haR har
    | exit g ref => exact hR g ref rfl
  · exact arrivalOf_old haR ha

/-- In the history extended by a fresh arrival or wait record, no fresh arrival is of a phase that
some wait waits for. -/
theorem new_arrival_not_waited {block ctas phase : Nat} {H : List (Record EvId)}
    {R : Record EvId} (hR : ∀ g ref, R ≠ .exit g ref) {s : State}
    (hs : ClusterBarrier.run block ctas {} H = .done s) (hfresh : ∀ r ∈ H, ∀ e ∈ R.refs, e ∉ r.refs)
    {a w : EvId} {release : Bool} (haR : a ∈ R.refs)
    (ha : ArrivalOf block ctas (H ++ [R]) a phase release)
    (hwt : WaitOf block ctas (H ++ [R]) w phase) : False := by
  cases R with
  | arrival cta warp rel lanes =>
    have hp := arrivalOf_snoc_phase hs (fun r hr => hfresh r hr a haR) ha
    have hlt := waitOf_phase_lt hs (waitOf_of_snoc_arrival rfl hwt)
    omega
  | wait cta warp lanes =>
    obtain ⟨r, hr, har⟩ := arrivalOf_mem (arrivalOf_of_snoc_wait rfl ha)
    exact hfresh r hr a haR har
  | exit g ref => exact hR g ref rfl

/-- Appending an arrival adds no `Synchronizes` pair between the old records: the new arrival
is performed at the open phase, and no old wait has observed that phase. -/
theorem synchronizes_snoc_arrival {block ctas : Nat} {H : List (Record EvId)} {R : Record EvId}
    {s : State} (hs : ClusterBarrier.run block ctas {} H = .done s) {cta warp : Nat}
    {release : Bool} {lanes : List (Nat × EvId)} (hR : R = .arrival cta warp release lanes)
    (hfresh : ∀ e ∈ R.refs, ∀ r ∈ H, e ∉ r.refs) (a w : EvId) :
    Synchronizes block ctas (H ++ [R]) a w ↔ Synchronizes block ctas H a w := by
  constructor
  · rintro ⟨p, ha, hw⟩
    by_cases hae : a ∈ R.refs
    · have hp := arrivalOf_snoc_phase hs (fun r hr => hfresh a hae r hr) ha
      have hwo := waitOf_of_snoc_arrival hR hw
      have hlt := waitOf_phase_lt hs hwo
      omega
    · exact ⟨p, arrivalOf_old hae ha, waitOf_of_snoc_arrival hR hw⟩
  · rintro ⟨p, ha, hw⟩
    exact ⟨p, ha.append, hw.append⟩

/-- Appending a wait adds no `Synchronizes` pair whose waiting side is outside the record. -/
theorem synchronizes_snoc_wait {block ctas : Nat} {H : List (Record EvId)} {R : Record EvId}
    {cta warp : Nat} {lanes : List (Nat × EvId)} (hR : R = .wait cta warp lanes) (a w : EvId)
    (h : Synchronizes block ctas (H ++ [R]) a w) :
    w ∈ R.refs ∨ Synchronizes block ctas H a w := by
  obtain ⟨p, ha, hw⟩ := h
  by_cases hwR : w ∈ R.refs
  · exact .inl hwR
  · exact .inr ⟨p, arrivalOf_of_snoc_wait hR ha, waitOf_old hwR hw⟩

/-- Cluster synchronization is unchanged by appending an arrival to the cluster of `e`. -/
theorem clusterSync_snoc_arrival {L : Launch} {X : Execution} {c : Nat} {e f : EvId}
    {s : State}
    (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s)
    {R : Record EvId} {cta warp : Nat} {release : Bool} {lanes : List (Nat × EvId)}
    (hR : R = .arrival cta warp release lanes)
    (hfresh : ∀ e ∈ R.refs, ∀ r ∈ X.clusters c, e ∉ r.refs)
    (he : L.clusterOfCta (e.1 / L.block) = c) :
    ClusterSync L (X.withClusterRecord c R) e f ↔ ClusterSync L X e f := by
  have hsz : L.clusterSizeOf (e.1 / L.block) = L.clusterSizeAt c := by
    rw [Launch.clusterSizeOf, he]
  have key : ∀ a w, Synchronizes L.block (L.clusterSizeOf (e.1 / L.block))
      ((X.withClusterRecord c R).clusters (L.clusterOfCta (e.1 / L.block))) a w ↔
      Synchronizes L.block (L.clusterSizeOf (e.1 / L.block))
        (X.clusters (L.clusterOfCta (e.1 / L.block))) a w := by
    intro a w
    rw [hsz, he, Execution.clusters_withClusterRecord_self]
    exact synchronizes_snoc_arrival hs hR hfresh a w
  constructor
  · rintro ⟨hsame, i, j, hsy, hrest⟩
    exact ⟨hsame, i, j, (key _ _).mp hsy, hrest⟩
  · rintro ⟨hsame, i, j, hsy, hrest⟩
    exact ⟨hsame, i, j, (key _ _).mpr hsy, hrest⟩

/-- Appending a wait cannot create a cluster synchronization into an event of the history: the
waiting side of the new edge would be the last event of its thread, which has no later event. -/
theorem clusterSync_of_snoc_wait {L : Launch} {X : Execution} {c : Nat} {e f : EvId}
    {cta warp : Nat} {lanes : List (Nat × EvId)} {R : ClusterBarrier.Record EvId}
    (hR : R = .wait cta warp lanes) (hlast : ∀ g ∈ R.refs, g.2 + 1 = (X.tr g.1).length)
    (he : L.clusterOfCta (e.1 / L.block) = c)
    (h : ClusterSync L (X.withClusterRecord c R) e f) : ClusterSync L X e f := by
  obtain ⟨hsame, i, j, hsync, hi, hei, hjf, hf⟩ := h
  have hf' : f.2 < (X.tr f.1).length := hf
  have hi' : i < (X.tr e.1).length := hi
  refine ⟨hsame, i, j, ?_, hi', hei, hjf, hf'⟩
  rw [he] at hsync ⊢
  rw [Execution.clusters_withClusterRecord_self] at hsync
  rcases synchronizes_snoc_wait hR (e.1, i) (f.1, j) hsync with hmem | hsy
  · exfalso
    have h1 := hlast _ hmem
    dsimp only at h1
    omega
  · exact hsy

/-- The extended cluster histories satisfy the cluster history invariant when the record is
accepted by the run, its references are fresh and form a duplicate-free list. -/
theorem clusterHistoryOk_withClusterRecord {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId} (hX : ClusterHistoryOk L X)
    (hcl : c < L.nclusters) (hsrc : ClusterSources L X c R)
    (hnd : R.refs.Nodup) (hfresh : ∀ r ∈ X.clusters c, ∀ e ∈ R.refs, e ∉ r.refs)
    (hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c ++ [R]) =
      .done t) :
    ClusterHistoryOk L (X.withClusterRecord c R) := by
  obtain ⟨hvalid, hempty, hall⟩ := hX
  have hle := le_withClusterRecord X c R
  refine ⟨hvalid, ?_, ?_⟩
  · intro c' hc'
    by_cases hcc : c' = c
    · exact absurd (hcc ▸ hc') (not_le.mpr hcl)
    · rw [Execution.clusters_withClusterRecord_ne X hcc]
      exact hempty c' hc'
  · intro c' hc'
    obtain ⟨hnd0, hsrc0, hrun⟩ := hall c' hc'
    by_cases hcc : c' = c
    · subst hcc
      rw [Execution.clusters_withClusterRecord_self]
      refine ⟨?_, ?_, hacc⟩
      · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        refine List.nodup_append.mpr ⟨hnd0, hnd, fun a ha b hb hab => ?_⟩
        obtain ⟨r, hr, har⟩ := List.mem_flatMap.mp ha
        exact hfresh r hr b hb (hab ▸ har)
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact (hsrc0 r hr).mono hle
        · obtain rfl := List.mem_singleton.mp hr
          exact hsrc.mono hle
    · rw [Execution.clusters_withClusterRecord_ne X hcc]
      exact ⟨hnd0, fun r hr => (hsrc0 r hr).mono hle, hrun⟩

/-! ## Happens-before and visibility are unchanged -/

/-- Equal step relations have equal transitive closures. -/
theorem transGen_congr_of_iff {α : Type} {r s : α → α → Prop}
    (hiff : ∀ a b, r a b ↔ s a b) : ∀ {x y : α}, Relation.TransGen r x y →
      Relation.TransGen s x y := by
  intro x y hxy
  induction hxy with
  | single hr => exact .single ((hiff _ _).mp hr)
  | tail _ hr ih => exact .tail ih ((hiff _ _).mp hr)

/-- Happens-before is the transitive closure of the synchronization steps; equal steps give equal
happens-before. -/
theorem baseCausality_withClusterRecord_iff {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId}
    (h : ∀ e f, ClusterSync L (X.withClusterRecord c R) e f ↔ ClusterSync L X e f) (e f : EvId) :
    baseCausality L (X.withClusterRecord c R) e f ↔ baseCausality L X e f := by
  have step : ∀ a b, (po (X.withClusterRecord c R) a b ∨
      CtaBarSync L (X.withClusterRecord c R) a b ∨
      MSync L (X.withClusterRecord c R) a b ∨ ClusterSync L (X.withClusterRecord c R) a b ∨
      WarpBarSync L (X.withClusterRecord c R) a b ∨
      synchronizesWith L (X.withClusterRecord c R) a b ∨
      FenceSync L (X.withClusterRecord c R) a b) ↔
      (po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
      WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b) := fun a b =>
    or_congr Iff.rfl (or_congr Iff.rfl (or_congr Iff.rfl (or_congr (h a b) Iff.rfl)))
  unfold baseCausality
  exact ⟨fun hh => transGen_congr_of_iff step hh,
    fun hh => transGen_congr_of_iff (fun a b => (step a b).symm) hh⟩

/-- Visibility depends on happens-before and on fields that the record append does not change. -/
theorem modelCausality_withClusterRecord_iff {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId}
    (hb' : ∀ e f, baseCausality L (X.withClusterRecord c R) e f ↔ baseCausality L X e f)
    (l : Loc) (e f : AsyncCopy.Ref) :
    modelCausality L (X.withClusterRecord c R) l e f ↔ modelCausality L X l e f := by
  have hcb (i w f : EvId) (p : AsyncCopy.Part) :
      ObservedCompletionBefore L (X.withClusterRecord c R) l i p w f ↔
        ObservedCompletionBefore L X l i p w f :=
    observedCompletionBefore_congr rfl rfl (hb' _ _) (by simp only [ProxyBefore, hb']; rfl)
  cases e <;> cases f <;> simp only [modelCausality, ProxyBefore, hb', hcb]
  all_goals first
    | rfl
    | exact and_congr_right fun _ =>
      AsyncChain.congr (fun _ _ => by simp only [AsyncBefore, hb']; rfl)
        (fun _ p => by cases p <;> rfl)

/-! ## The needs of old events -/

/-- A record of an extended history that holds an event outside the appended record is a record
of the old history at the same index. -/
theorem old_index_of_mem {X : Execution} {c c1 i : Nat} {R r : ClusterBarrier.Record EvId}
    {j : EvId} (hj : j ∉ R.refs) (hjr : j ∈ r.refs)
    (h : ((X.withClusterRecord c R).clusters c1)[i]? = some r) :
    (X.clusters c1)[i]? = some r ∧ i < (X.clusters c1).length := by
  rcases ClusterRecordSnoc.history_get_cases (c0 := c) (r := R) h with ho | ⟨-, -, rfl⟩
  · exact ⟨ho, (List.getElem?_eq_some_iff.mp ho).1⟩
  · exact (hj hjr).elim

/-- A record of an old history is a record of the extended history at the same index. -/
theorem get_withClusterRecord_of_old {X : Execution} {c c1 i : Nat}
    {R r : ClusterBarrier.Record EvId} (h : (X.clusters c1)[i]? = some r) :
    ((X.withClusterRecord c R).clusters c1)[i]? = some r := by
  by_cases hc : c1 = c
  · subst hc
    rw [Execution.clusters_withClusterRecord_self,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
    exact h
  · rw [Execution.clusters_withClusterRecord_ne X hc]
    exact h

/-- The needs of an event that is no cluster barrier operation do not read the cluster
histories. -/
theorem kindNeeds_withClusterRecord {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId} {k : Kind} (hk : ∀ op, k ≠ .cluster op) (j : EvId) :
    KindNeeds L (X.withClusterRecord c R) k j = KindNeeds L X k j := by
  cases k
  case cluster op => exact absurd rfl (hk op)
  case tc t => cases t <;> rfl
  all_goals rfl

/-- An event counted by the wait `j` of the extended history, when `j` is outside the appended
fresh arrival or wait record, is counted in the old history and is a reference of it. -/
theorem clusterCounted_old {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId} (hR : ∀ g ref, R ≠ .exit g ref) {s : State}
    (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs) {j y : EvId}
    (hj : j ∉ R.refs) (h : ClusterCounted L (X.withClusterRecord c R) j y) :
    ClusterCounted L X j y ∧
      y ∈ (X.clusters (L.clusterOfCta (j.1 / L.block))).flatMap ClusterBarrier.Record.refs := by
  rcases h with ⟨phase, rel, hw, ha⟩ | ⟨i, i', r, g, hi, hjr, hrw, hii, hexit⟩
  · have hold : ClusterBarrier.ArrivalOf L.block
        (L.clusterSizeAt (L.clusterOfCta (j.1 / L.block)))
        (X.clusters (L.clusterOfCta (j.1 / L.block))) y phase rel ∧
        ClusterBarrier.WaitOf L.block (L.clusterSizeAt (L.clusterOfCta (j.1 / L.block)))
          (X.clusters (L.clusterOfCta (j.1 / L.block))) j phase := by
      by_cases hc1 : L.clusterOfCta (j.1 / L.block) = c
      · rw [hc1] at hw ha ⊢
        rw [Execution.clusters_withClusterRecord_self] at hw ha
        exact arrivalWait_old hR hs (fun r hr => hfresh c r hr) hj ha hw
      · rw [Execution.clusters_withClusterRecord_ne X hc1] at hw ha
        exact ⟨ha, hw⟩
    obtain ⟨r, hr, hyr⟩ := arrivalOf_mem hold.1
    exact ⟨.inl ⟨phase, rel, hold.2, hold.1⟩, List.mem_flatMap.mpr ⟨r, hr, hyr⟩⟩
  · obtain ⟨hi', hlen⟩ := old_index_of_mem hj hjr hi
    have hexit' := ClusterRecordSnoc.old_history_get (by omega) hexit
    refine ⟨.inr ⟨i, i', r, g, hi', hjr, hrw, hii, hexit'⟩,
      List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hexit', ?_⟩⟩
    simp [Record.refs]

/-- A witness of an event outside the appended fresh arrival or wait record is a witness of it in
the old execution: the needs of other kinds do not read the cluster histories, and the needs of a
cluster operation outside the record are the old records of its warp and the old arrivals and
exits counted by its wait. -/
theorem witness_old {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId} (hR : ∀ g ref, R ≠ .exit g ref) {s : State}
    (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs) {x : AsyncCopy.Ref}
    {j : EvId} (hj : j ∉ R.refs) (h : Witness L (X.withClusterRecord c R) x j) :
    Witness L X x j := by
  obtain ⟨fills, hmem, hx, hf⟩ := h
  cases hg : X.get j with
  | none =>
    have hgY : (X.withClusterRecord c R).get j = none := hg
    simp only [Needs, hgY, List.not_mem_nil] at hmem
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    have hgY : (X.withClusterRecord c R).get j = some ⟨pc, k⟩ := hg
    simp only [Needs, hgY] at hmem
    by_cases hk : ∃ op, k = .cluster op
    · obtain ⟨op, rfl⟩ := hk
      simp only [KindNeeds, clusterNeeds, List.mem_append] at hmem
      rcases hmem with hwarp | hcount
      · obtain ⟨h, hh, hfl⟩ := List.mem_map.mp hwarp
        cases hfl
        obtain ⟨i, r, y, hi, hjr, hxy, hy1, hopt⟩ := hf
        obtain ⟨hi', hlen⟩ := old_index_of_mem hj hjr hi
        refine Witness.of_need L (fills := fun x => ∃ i, ∃ r : ClusterBarrier.Record EvId, ∃ y,
          (X.clusters (L.clusterOfCta (j.1 / L.block)))[i]? = some r ∧ j ∈ r.refs ∧
          x = .thread y ∧ y.1 = h ∧ (y ∈ r.refs ∨ ∃ (j' g : Nat), j' < i ∧
            (X.clusters (L.clusterOfCta (j.1 / L.block)))[j']? =
              some (ClusterBarrier.Record.exit g y))) ?_ hx ⟨i, r, y, hi', hjr, hxy, hy1, ?_⟩
        · simp only [Needs, hg, KindNeeds, clusterNeeds, List.mem_append]
          exact .inl (List.mem_map.mpr ⟨h, hh, rfl⟩)
        · rcases hopt with hy | ⟨j', g, hj', hex⟩
          · exact .inl hy
          · exact .inr ⟨j', g, hj', ClusterRecordSnoc.old_history_get (by omega) hex⟩
      · cases op with
        | arrive release aligned => simp only [List.not_mem_nil] at hcount
        | wait aligned =>
          obtain ⟨y, -, hcc⟩ := List.mem_flatMap.mp hcount
          by_cases hcl : ClusterCounted L (X.withClusterRecord c R) j y
          · simp only [needsIf, hcl, ite_true, List.mem_singleton, Need.node.injEq] at hcc
            subst hcc
            obtain ⟨hcl', hy⟩ := clusterCounted_old hR hs hfresh hj hcl
            refine Witness.of_need L (fills := (· = .thread y)) ?_ hx hf
            simp only [Needs, hg, KindNeeds, clusterNeeds, List.mem_append]
            refine .inr (List.mem_flatMap.mpr ⟨y, hy, ?_⟩)
            simp [needsIf, hcl']
          · simp only [needsIf, hcl, ite_false, List.not_mem_nil] at hcc
    · push Not at hk
      rw [kindNeeds_withClusterRecord hk] at hmem
      exact Witness.of_need L (by simp only [Needs, hg]; exact hmem) hx hf

/-- An event outside the appended fresh arrival or wait record that is ready in the old execution
is ready in the extended one. -/
theorem ready_withClusterRecord {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId} (hR : ∀ g ref, R ≠ .exit g ref) {s : State}
    (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs) {j : EvId}
    (hj : j ∉ R.refs) (h : Ready L X j) : Ready L (X.withClusterRecord c R) j := by
  intro n hn
  cases hg : X.get j with
  | none =>
    have hgY : (X.withClusterRecord c R).get j = none := hg
    simp only [Needs, hgY, List.not_mem_nil] at hn
  | some ev =>
    obtain ⟨pc, k⟩ := ev
    have hgY : (X.withClusterRecord c R).get j = some ⟨pc, k⟩ := hg
    have hX : ∀ n ∈ KindNeeds L X k j, (match n with
        | .node fills => ∃ x, X.RefPresent x ∧ fills x
        | .cond holds => holds) := by
      intro n hn
      exact h n (by simp only [Needs, hg]; exact hn)
    simp only [Needs, hgY] at hn
    by_cases hk : ∃ op, k = .cluster op
    · obtain ⟨op, rfl⟩ := hk
      simp only [KindNeeds, clusterNeeds, List.mem_append] at hn
      rcases hn with hwarp | hcount
      · obtain ⟨h', hh, rfl⟩ := List.mem_map.mp hwarp
        obtain ⟨x, hx, i, r, y, hi, hjr, hxy, hy1, hopt⟩ := hX _ (by
          simp only [KindNeeds, clusterNeeds, List.mem_append]
          exact .inl (List.mem_map.mpr ⟨h', hh, rfl⟩))
        refine ⟨x, hx, i, r, y, get_withClusterRecord_of_old hi, hjr, hxy, hy1, ?_⟩
        rcases hopt with hy | ⟨j', g, hj', hex⟩
        · exact .inl hy
        · exact .inr ⟨j', g, hj', get_withClusterRecord_of_old hex⟩
      · cases op with
        | arrive release aligned => simp only [List.not_mem_nil] at hcount
        | wait aligned =>
          obtain ⟨y, -, hcc⟩ := List.mem_flatMap.mp hcount
          by_cases hcl : ClusterCounted L (X.withClusterRecord c R) j y
          · simp only [needsIf, hcl, ite_true, List.mem_singleton] at hcc
            subst hcc
            obtain ⟨hcl', hy⟩ := clusterCounted_old hR hs hfresh hj hcl
            exact hX (Need.node (· = .thread y)) (by
              simp only [KindNeeds, clusterNeeds, List.mem_append]
              refine .inr (List.mem_flatMap.mpr ⟨y, hy, ?_⟩)
              simp [needsIf, hcl'])
          · simp only [needsIf, hcl, ite_false, List.not_mem_nil] at hcc
    · push Not at hk
      rw [kindNeeds_withClusterRecord hk] at hn
      exact hX n hn

/-! ## The dependency edges of the appended record -/

/-- A thread reference of the appended record. -/
def NewNode (R : ClusterBarrier.Record EvId) (u : AsyncCopy.Ref × Bool) : Prop :=
  ∃ f ∈ R.refs, u.1 = .thread f

/-- Cluster dependencies out of a fresh reference of an appended arrival or wait record: the only
targets are fresh references of the same record. An arrival of the record is performed at the
phase where the old history ends, which no old wait has passed; a wait record contributes no
arrival. -/
theorem clusterWaits_new {L : Launch} {X : Execution} {c : Nat} {R : ClusterBarrier.Record EvId}
    (hR : ∀ g ref, R ≠ .exit g ref) {s : State}
    (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs)
    (hecl : ∀ e ∈ R.refs, L.clusterOfCta (e.1 / L.block) = c)
    {e f : EvId} {b b' : Bool} (he : e ∈ R.refs)
    (hw : ClusterWaits L (X.withClusterRecord c R) e f b b') :
    f ∈ R.refs ∧ b = false ∧ b' = true := by
  obtain ⟨-, -, hcase⟩ := hw
  have hsz : L.clusterSizeOf (e.1 / L.block) = L.clusterSizeAt c := by
    rw [Launch.clusterSizeOf, hecl e he]
  rw [hsz] at hcase
  rcases hcase with ⟨c1, i, j, r, q, hr, hq, hij, he1, hf, hb, hb'⟩ |
    ⟨hb, hb', c1, r, hr, he1, hf⟩ | ⟨hb, hb', phase, c1, ha, hwt⟩ | ⟨hb, hb', phase, c1, ha, hwt⟩
  · exfalso
    have hr' : (ClusterRecordSnoc.clusters X c R c1)[i]? = some r := hr
    have hq' : (ClusterRecordSnoc.clusters X c R c1)[j]? = some q := hq
    rcases ClusterRecordSnoc.history_get_cases hr' with hro | ⟨-, hi, -⟩
    · exact hfresh c1 r (List.mem_of_getElem? hro) e he he1
    · rcases ClusterRecordSnoc.history_get_cases hq' with hqo | ⟨-, hj, -⟩
      · have hlt := (List.getElem?_eq_some_iff.mp hqo).1
        omega
      · omega
  · have hr' : r ∈ ClusterRecordSnoc.clusters X c R c1 := hr
    refine ⟨?_, hb, hb'⟩
    by_cases hc1 : c1 = c
    · simp only [ClusterRecordSnoc.clusters, ite_eq_left hc1] at hr'
      rcases List.mem_append.mp hr' with ho | hn
      · exact (hfresh c1 r ho e he he1).elim
      · rw [List.mem_singleton.mp hn] at hf
        exact hf
    · simp only [ClusterRecordSnoc.clusters, ite_eq_right hc1] at hr'
      exact (hfresh c1 r hr' e he he1).elim
  all_goals
    exfalso
    by_cases hc1 : c1 = c
    · rw [hc1, Execution.clusters_withClusterRecord_self] at ha hwt
      exact new_arrival_not_waited hR hs (fun r hr => hfresh c r hr) he ha hwt
    · rw [Execution.clusters_withClusterRecord_ne X hc1] at ha
      obtain ⟨r', hr', her'⟩ := arrivalOf_mem ha
      exact hfresh c1 r' hr' e he her'

/-- A need of `j` that a fresh reference of the appended record fills makes `j` a reference of
the record: a cluster operation fills only the needs of the lanes of its own record and of the
waits of its arrival's phase. -/
theorem witness_new {L : Launch} {X : Execution} {c : Nat} {R : ClusterBarrier.Record EvId}
    (hR : ∀ g ref, R ≠ .exit g ref) {s : State}
    (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs)
    (hv : EffectValidity L X) (hcb : CtaBarHistoryOk L X)
    (hH : ClusterHistoryOk L (X.withClusterRecord c R)) {e j : EvId} {pc : Nat} {op : ClusterOp}
    (hget : X.get e = some ⟨pc, .cluster op⟩) (he : e ∈ R.refs)
    (hw : Witness L (X.withClusterRecord c R) (.thread e) j) : j ∈ R.refs := by
  have hvY : EffectValidity L (X.withClusterRecord c R) :=
    ⟨hv.tma, hv.tensor, hv.store, hv.clc, hv.tmemPair, hv.tcCommit⟩
  rcases cluster_witness_cases hvY hH hcb hget hw with ⟨r, hr, her, hjr⟩ |
    ⟨phase, rel, ha, hwt⟩
  · have hr' : r ∈ ClusterRecordSnoc.clusters X c R (L.clusterOfCta (j.1 / L.block)) := hr
    by_cases hc1 : L.clusterOfCta (j.1 / L.block) = c
    · simp only [ClusterRecordSnoc.clusters, ite_eq_left hc1] at hr'
      rcases List.mem_append.mp hr' with ho | hn
      · exact (hfresh _ r ho e he her).elim
      · rw [List.mem_singleton.mp hn] at hjr
        exact hjr
    · simp only [ClusterRecordSnoc.clusters, ite_eq_right hc1] at hr'
      exact (hfresh _ r hr' e he her).elim
  · exfalso
    by_cases hc1 : L.clusterOfCta (j.1 / L.block) = c
    · rw [hc1, Execution.clusters_withClusterRecord_self] at ha hwt
      exact new_arrival_not_waited hR hs (fun r hr => hfresh c r hr) he ha hwt
    · rw [Execution.clusters_withClusterRecord_ne X hc1] at ha
      obtain ⟨r', hr', her'⟩ := arrivalOf_mem ha
      exact hfresh _ r' hr' e he her'

/-- The order of a cluster history between references outside the appended record is the old
order. -/
theorem objectOrder_withClusterRecord_old {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId} {o : OrderObject} {u v : AsyncCopy.Ref × Bool}
    (hu : ¬ NewNode R u) (hv : ¬ NewNode R v)
    (h : ObjectOrder L (X.withClusterRecord c R) o u v) : ObjectOrder L X o u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  rcases o with m | ⟨d, id⟩ | d | d
  · exact h
  · exact h
  · obtain ⟨i, j, rfl, rfl, hpi, hpj, k, l, r, q, hr, hq, hkl, hir, hjq, hb, hb'⟩ := h
    have hr' : (ClusterRecordSnoc.clusters X c R d)[k]? = some r := hr
    have hq' : (ClusterRecordSnoc.clusters X c R d)[l]? = some q := hq
    rcases ClusterRecordSnoc.history_get_cases hr' with hro | ⟨-, -, hrR⟩
    · rcases ClusterRecordSnoc.history_get_cases hq' with hqo | ⟨-, -, hqR⟩
      · exact ⟨i, j, rfl, rfl, hpi, hpj, k, l, r, q, hro, hqo, hkl, hir, hjq, hb, hb'⟩
      · exact (hv ⟨j, hqR ▸ hjq, rfl⟩).elim
    · exact (hu ⟨i, hrR ▸ hir, rfl⟩).elim
  · exact h

/-- Cluster synchronization is unchanged by an appended record of a cluster other than the one
of `e`. -/
theorem clusterSync_withClusterRecord_ne {L : Launch} {X : Execution} {c : Nat}
    {R : ClusterBarrier.Record EvId} {e f : EvId} (h : L.clusterOfCta (e.1 / L.block) ≠ c) :
    ClusterSync L (X.withClusterRecord c R) e f ↔ ClusterSync L X e f := by
  unfold ClusterSync
  rw [Execution.clusters_withClusterRecord_ne X h]
  rfl

/-- The waiting edges out of a fresh reference of an appended record stay on fresh references, and
they leave a fresh thread only through its own return. -/
theorem waits_from_new {L : Launch} {X : Execution} {c : Nat} {R : ClusterBarrier.Record EvId}
    (hX : ClusterHistoryOk L X) (hv : EffectValidity L X) (hb : CtaBarHistoryOk L X)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs)
    (hterm : ∀ e ∈ R.refs, ∃ pc op, X.get e = some ⟨pc, .cluster op⟩ ∧
      e.2 + 1 = (X.tr e.1).length)
    (hcwNew : ∀ {i j : EvId} {b b' : Bool}, i ∈ R.refs →
      ClusterWaits L (X.withClusterRecord c R) i j b b' → j ∈ R.refs ∧ b = false ∧ b' = true)
    (hwNew : ∀ {i j : EvId}, i ∈ R.refs →
      Witness L (X.withClusterRecord c R) (.thread i) j → j ∈ R.refs)
    {u v : AsyncCopy.Ref × Bool} (hu : NewNode R u) (hw : Waits L (X.withClusterRecord c R) u v) :
    NewNode R v ∧ u.2 = false ∧ v.2 = true := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  obtain ⟨e, he, hue⟩ := hu
  simp only at hue
  subst hue
  rcases ClusterRecordSnoc.waits_transport hw with ⟨i, j, hi, hj, hcw⟩ |
    ⟨h1, h2, j, hj, hwit⟩ | hW
  · have hie : i = e := (AsyncCopy.Ref.thread.inj hi).symm
    subst hie
    obtain ⟨hjR, hb2, hb2'⟩ := hcwNew he hcw
    exact ⟨⟨j, hjR, hj⟩, hb2, hb2'⟩
  · exact ⟨⟨j, hwNew he hwit, hj⟩, h1, h2⟩
  · obtain ⟨pc, op, hget, ht⟩ := hterm e he
    have hun : ¬ ClusterRecorded L X e := fun ⟨r, hr, her⟩ => hfresh _ r hr e he her
    obtain ⟨hu2, hvv⟩ := terminal_cluster_waits_cases hv hX hb hget ht hun hW
    obtain ⟨hv1, hv2⟩ := Prod.mk.inj hvv
    exact ⟨⟨e, he, hv1⟩, hu2, hv2⟩

/-- Appending a fresh arrival or wait record whose references are terminal cluster operations
extends the execution by the record's references: a dependency out of a fresh reference goes
from its issue to a fresh return and stops there, and between other nodes every relation is one of
`X`. -/
theorem sinkFrame_withClusterRecord {L : Launch} {K : Kernel} {A : List Assumption}
    {X : Execution} {c : Nat} {R : ClusterBarrier.Record EvId} (hX : ClusterHistoryOk L X)
    (hv : EffectValidity L X) (hcb : CtaBarHistoryOk L X)
    (hH : ClusterHistoryOk L (X.withClusterRecord c R)) (hR : ∀ g ref, R ≠ .exit g ref)
    {s : State} (hs : ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c) = .done s)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs)
    (hecl : ∀ e ∈ R.refs, L.clusterOfCta (e.1 / L.block) = c)
    (hterm : ∀ e ∈ R.refs, ∃ pc op, X.get e = some ⟨pc, .cluster op⟩ ∧
      e.2 + 1 = (X.tr e.1).length)
    (hbo : ∀ e f, baseCausality L (X.withClusterRecord c R) e f ↔ baseCausality L X e f)
    (hasync : AsyncObjectOrdered L X) (hinit : InitFenceOrdered L X) :
    SinkFrame L K A X (X.withClusterRecord c R) (NewNode R) := by
  have notNew {i : EvId} {b : Bool} (h : ¬ NewNode R (.thread i, b)) : i ∉ R.refs :=
    fun hi => h ⟨i, hi, rfl⟩
  have hwNew : ∀ {i j : EvId}, i ∈ R.refs →
      Witness L (X.withClusterRecord c R) (.thread i) j → j ∈ R.refs := by
    intro i j hi hw
    obtain ⟨pc, op, hget, -⟩ := hterm i hi
    exact witness_new hR hs hfresh hv hcb hH hget hi hw
  have hrank : ∀ u v, Waits L (X.withClusterRecord c R) u v → NewNode R u →
      NewNode R v ∧ (fun p : AsyncCopy.Ref × Bool => if p.2 then 1 else 0) u <
        (fun p : AsyncCopy.Ref × Bool => if p.2 then 1 else 0) v := by
    intro u v hw hu
    obtain ⟨hvN, hu2, hv2⟩ := waits_from_new hX hv hcb hfresh hterm
      (fun hi hcw => clusterWaits_new hR hs hfresh hecl hi hcw) hwNew hu hw
    exact ⟨hvN, by simp [hu2, hv2]⟩
  have hcause : ∀ u v, stageCausality L (X.withClusterRecord c R) u v →
      stageCausality L X u v := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ (h | ⟨h1, h2, i, j, hi, hj, hc⟩ | h)
    · exact .inl h
    · exact .inr (.inl ⟨h1, h2, i, j, hi, hj, (hbo i j).mp hc⟩)
    · exact .inr (.inr h)
  refine
    { closed := ⟨_, hrank⟩
      cause := fun u v _ _ h => .single (hcause u v h)
      observed := fun _ _ _ _ h => h
      object := fun _ _ _ hu hv h => objectOrder_withClusterRecord_old hu hv h
      objectSync := ?_
      dep := ?_
      issue := ?_
      asyncSelf := fun m i p y hb => (hasync m i p y hb).1
      asyncObserved := fun _ _ _ _ _ _ h => h
      initFence := ?_
      get := fun _ _ => rfl }
  · intro o u v hu hv h
    cases o with
    | mbar m => exact h
    | ctaBar cta id => exact h
    | cluster d => exact objectOrder_withClusterRecord_old (L := L) (o := .cluster d) hu hv h
    | tmem cta => exact h
  · rintro ⟨x, b⟩ ⟨y, b'⟩ hu hv (h | h | ⟨h1, h2, j, rfl, hw⟩ | h)
    · exact .single (.inl h)
    · exact .single (.inr (.inl h))
    · exact .single (.inr (.inr (.inl ⟨h1, h2, j, rfl, witness_old hR hs hfresh (notNew hv) hw⟩)))
    · exact .single (.inr (.inr (.inr h)))
  · rintro m i p y hbef ⟨f, hf, hfi⟩
    have hif : i = f := AsyncCopy.Ref.thread.inj hfi
    subst hif
    obtain ⟨pc, op, hget, -⟩ := hterm i hf
    exact (sync_no_async_before hv.tma hget (.inr ⟨op, rfl⟩) m p y hbef).elim
  · intro m init w y hsync hc hbef
    obtain ⟨count, fence, arrival, pc, pca, release, aligned, pcw, alignedw, h1, h2, h3, h4, h5,
      h6, h7, h8, h9, h10, c1, phase, harr, hwt⟩ := hsync
    by_cases hwR : w ∈ R.refs
    · obtain ⟨⟨i, hiR, hieq⟩, -⟩ := SinkFrame.closed_path hrank
        (fun _ _ h => stageCausality.waits h) hc ⟨w, hwR, rfl⟩
      obtain ⟨pci, opi, hgeti, -⟩ := hterm i hiR
      cases y with
      | thread j =>
        have hji : j = i := AsyncCopy.Ref.thread.inj hieq
        subst hji
        exact cluster_no_object_before hv hgeti m _ hbef
      | async j p =>
        have hji : j = i := AsyncCopy.Ref.thread.inj hieq
        subst hji
        exact sync_no_async_before hv.tma hgeti (.inr ⟨opi, rfl⟩) m p _ hbef
    · have hold : ClusterBarrier.ArrivalOf L.block (L.clusterSizeAt c1) (X.clusters c1) arrival
          phase release ∧ ClusterBarrier.WaitOf L.block (L.clusterSizeAt c1) (X.clusters c1) w
          phase := by
        by_cases hc1 : c1 = c
        · subst hc1
          rw [Execution.clusters_withClusterRecord_self] at harr hwt
          exact arrivalWait_old hR hs (fun r hr => hfresh _ r hr) hwR harr hwt
        · rw [Execution.clusters_withClusterRecord_ne X hc1] at harr hwt
          exact ⟨harr, hwt⟩
      exact hinit m init w y
        ⟨count, fence, arrival, pc, pca, release, aligned, pcw, alignedw, h1, h2, h3, h4, h5, h6,
          h7, h8, h9, h10, c1, phase, hold.1, hold.2⟩
        (Relation.TransGen.mono (fun a b h => hcause a b h) _ _ hc) hbef

end ClusterRec

open ClusterRec

/-! ## Warp records of a CTA

The lanes of warp `w` of CTA `cta` are the threads of the block whose index in the warp is `w`.
Each lane contributes its cluster-local thread and its last event. -/

/-- The lanes of warp `w` of CTA `cta` in the cluster barrier record. -/
def warpLanes (L : Launch) (X : Execution) (cta w : Nat) : List (Nat × EvId) :=
  ((List.range L.block).filter fun lt => decide (lt / 32 = w)).map fun lt =>
    (L.rankOfCta cta * L.block + lt, (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1))

/-- The arrival record of warp `w` of CTA `cta`. -/
def warpArrival (L : Launch) (X : Execution) (cta w : Nat) (release : Bool) :
    ClusterBarrier.Record EvId :=
  .arrival (L.rankOfCta cta) w release (warpLanes L X cta w)

/-- The wait record of warp `w` of CTA `cta`. -/
def warpWait (L : Launch) (X : Execution) (cta w : Nat) : ClusterBarrier.Record EvId :=
  .wait (L.rankOfCta cta) w (warpLanes L X cta w)

theorem mem_warpLanes {L : Launch} {X : Execution} {cta w : Nat} {p : Nat × EvId}
    (hp : p ∈ warpLanes L X cta w) :
    ∃ lt, lt < L.block ∧ lt / 32 = w ∧
      p = (L.rankOfCta cta * L.block + lt,
        (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1)) := by
  unfold warpLanes at hp
  obtain ⟨lt, hlt, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hlt
  exact ⟨lt, hlt.1, hlt.2, rfl⟩

theorem warpLanes_refs_nodup {L : Launch} {X : Execution} {cta w : Nat} :
    ((warpLanes L X cta w).map Prod.snd).Nodup := by
  unfold warpLanes
  rw [List.map_map]
  refine List.Nodup.map ?_ (List.Nodup.filter _ (List.nodup_range))
  intro x y hxy
  have h := congrArg Prod.fst hxy
  simp only [Function.comp_apply] at h
  omega

/-- `Launch.locate` names a cluster and a rank in it: the CTA at offset `c` after the first `k`
clusters, when it lies in the next `n` clusters, is the CTA of that rank of that cluster. -/
theorem locate_spec (L : Launch) : ∀ n k c, L.clusterStart k + c < L.clusterStart (k + n) →
    k ≤ (L.locate n k c).1 ∧ (L.locate n k c).1 < k + n ∧
      (L.locate n k c).2 < L.clusterSizeAt (L.locate n k c).1 ∧
      L.clusterStart (L.locate n k c).1 + (L.locate n k c).2 = L.clusterStart k + c := by
  intro n
  induction n with
  | zero => intro k c h; simp at h
  | succ n ih =>
    intro k c h
    have hsz : L.clusterSizeAt k = (L.clusterPlaces k).shape.prod := rfl
    have hstep : L.clusterStart (k + 1) = L.clusterStart k + L.clusterSizeAt k := rfl
    simp only [Launch.locate]
    split
    · rename_i hc
      exact ⟨le_rfl, by omega, by rw [hsz]; exact hc, rfl⟩
    · rename_i hc
      have hk : k + 1 + n = k + (n + 1) := by omega
      obtain ⟨h1, h2, h3, h4⟩ := ih (k + 1) (c - (L.clusterPlaces k).shape.prod)
        (by rw [hk, hstep]; omega)
      exact ⟨by omega, by omega, h3, by rw [h4, hstep]; omega⟩

/-- In a valid cluster grid each CTA of the grid is the CTA of its rank in its cluster. -/
theorem cta_cluster {L : Launch} (hv : L.clusterGridValid) {cta : Nat} (hcta : cta < L.grid) :
    L.clusterOfCta cta < L.nclusters ∧ L.rankOfCta cta < L.clusterSizeAt (L.clusterOfCta cta) ∧
      L.clusterStart (L.clusterOfCta cta) + L.rankOfCta cta = cta := by
  have h := locate_spec L L.nclusters 0 cta (by
    rw [Nat.zero_add, Launch.clusterGridValid_start hv]
    simpa [Launch.clusterStart] using hcta)
  simp only [Launch.clusterStart, Nat.zero_add] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- In a valid cluster grid the cluster of a CTA of the grid is a cluster of the launch. -/
theorem clusterOf_lt {L : Launch} (hv : L.clusterGridValid) {cta : Nat} (hcta : cta < L.grid) :
    L.clusterOfCta cta < L.nclusters :=
  (cta_cluster hv hcta).1

/-- The cluster-local index of a lane lies in its cluster, and the global thread of the lane is
the cluster base plus that index. -/
theorem lane_index {L : Launch} (hv : L.clusterGridValid) {cta lt : Nat} (hcta : cta < L.grid)
    (hlt : lt < L.block) :
    L.rankOfCta cta * L.block + lt < L.block * L.clusterSizeAt (L.clusterOfCta cta) ∧
      cta * L.block + lt =
        L.clusterStart (L.clusterOfCta cta) * L.block + (L.rankOfCta cta * L.block + lt) := by
  obtain ⟨-, hr, hs⟩ := cta_cluster hv hcta
  constructor
  · have hle : (L.rankOfCta cta + 1) * L.block ≤
        L.clusterSizeAt (L.clusterOfCta cta) * L.block := Nat.mul_le_mul_right _ hr
    nlinarith
  · conv_lhs => rw [← hs]
    ring

theorem warpArrival_sources {L : Launch} {X : Execution} (hv : L.clusterGridValid)
    {cta w pc : Nat} {release aligned : Bool} (hcta : cta < L.grid)
    (hlast : ∀ lt, lt < L.block → lt / 32 = w →
      X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) =
        some ⟨pc, .cluster (.arrive release aligned)⟩) :
    ClusterSources L X (L.clusterOfCta cta) (warpArrival L X cta w release) := by
  intro p hp
  obtain ⟨lt, hlt, hw, rfl⟩ := mem_warpLanes hp
  obtain ⟨h1, h2⟩ := lane_index hv hcta hlt
  exact ⟨h1, h2, pc, aligned, hlast lt hlt hw⟩

theorem warpWait_sources {L : Launch} {X : Execution} (hv : L.clusterGridValid)
    {cta w pc : Nat} {aligned : Bool} (hcta : cta < L.grid)
    (hlast : ∀ lt, lt < L.block → lt / 32 = w →
      X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) =
        some ⟨pc, .cluster (.wait aligned)⟩) :
    ClusterSources L X (L.clusterOfCta cta) (warpWait L X cta w) := by
  intro p hp
  obtain ⟨lt, hlt, hw, rfl⟩ := mem_warpLanes hp
  obtain ⟨h1, h2⟩ := lane_index hv hcta hlt
  exact ⟨h1, h2, pc, aligned, hlast lt hlt hw⟩

/-- The references of a warp record are not recorded before it, when no lane is recorded. -/
theorem warp_refs_not_recorded {L : Launch} {X : Execution} {cta w : Nat}
    {R : ClusterBarrier.Record EvId} (hR : R.refs = (warpLanes L X cta w).map Prod.snd)
    (hfree : ∀ lt, lt < L.block → lt / 32 = w →
      ¬ ClusterRecorded L X (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1)) :
    ∀ e ∈ R.refs, ¬ ClusterRecorded L X e := by
  intro e he
  rw [hR] at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  obtain ⟨lt, hlt, hw, rfl⟩ := mem_warpLanes hp
  exact hfree lt hlt hw

theorem warp_refs_terminal {L : Launch} {X : Execution} {cta w pc : Nat}
    {R : ClusterBarrier.Record EvId}
    {op : ClusterOp} (hR : R.refs = (warpLanes L X cta w).map Prod.snd)
    (hlast : ∀ lt, lt < L.block → lt / 32 = w →
      X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) = some ⟨pc, .cluster op⟩) :
    ∀ e ∈ R.refs, ∃ pc' op', X.get e = some ⟨pc', .cluster op'⟩ ∧
      e.2 + 1 = (X.tr e.1).length := by
  intro e he
  rw [hR] at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  obtain ⟨lt, hlt, hw, rfl⟩ := mem_warpLanes hp
  have hg := hlast lt hlt hw
  have hl : (X.tr (cta * L.block + lt)).length - 1 < (X.tr (cta * L.block + lt)).length :=
    len_of_get hg
  exact ⟨pc, op, hg, by dsimp only; omega⟩

/-- A reference of the warp record is no reference of an older cluster record. -/
theorem fresh_of_not_recorded {L : Launch} {X : Execution} (hX : ClusterHistoryOk L X)
    {R : ClusterBarrier.Record EvId} (hnr : ∀ e ∈ R.refs, ¬ ClusterRecorded L X e) :
    ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs := by
  intro c' r hr e he her
  apply hnr e he
  refine ⟨r, ?_, her⟩
  rw [hX.ref_cluster hr her]
  exact hr

/-! ## The extension as a `Consistent` execution -/

/-- Appending a fresh arrival or wait record whose references are terminal cluster operations and
that the cluster run accepts gives a consistent execution, provided the cluster synchronization
is unchanged. -/
theorem consistent_withClusterRecord {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {c : Nat} {R : ClusterBarrier.Record EvId}
    (hX : Consistent L K A mem0 X) (hcl : c < L.nclusters) (hsrc : ClusterSources L X c R)
    (hnd : R.refs.Nodup) (hR : ∀ g ref, R ≠ .exit g ref)
    (hfresh : ∀ c', ∀ r ∈ X.clusters c', ∀ e ∈ R.refs, e ∉ r.refs)
    (hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt c) {} (X.clusters c ++ [R]) =
      .done t)
    (hterm : ∀ e ∈ R.refs, ∃ pc op, X.get e = some ⟨pc, .cluster op⟩ ∧
      e.2 + 1 = (X.tr e.1).length)
    (hsync : ∀ e f, ClusterSync L (X.withClusterRecord c R) e f ↔ ClusterSync L X e f)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.withClusterRecord c R)) :
    Consistent L K A mem0 (X.withClusterRecord c R) := by
  obtain ⟨s, hs⟩ := (hX.cluster.2.2 c hcl).2.2
  have hecl : ∀ e ∈ R.refs, L.clusterOfCta (e.1 / L.block) = c :=
    fun e he => hsrc.ref_cluster he hcl
  have hH : ClusterHistoryOk L (X.withClusterRecord c R) :=
    clusterHistoryOk_withClusterRecord hX.cluster hcl hsrc hnd (fun r hr e he => hfresh c r hr e he)
      hacc
  have hb' : ∀ e f, baseCausality L (X.withClusterRecord c R) e f ↔ baseCausality L X e f :=
    fun e f => baseCausality_withClusterRecord_iff hsync e f
  have horder : OrderOk L K A (X.withClusterRecord c R) :=
    (sinkFrame_withClusterRecord hX.cluster hX.effectValidity hX.ctaBar hH hR hs hfresh hecl
      hterm hb' hX.asyncObject hX.initFence).orderOk hX.orderOk
  have notReturned {e : EvId} (hr : Returned X e) : e ∉ R.refs := by
    intro he
    obtain ⟨pc, op, hget, ht⟩ := hterm e he
    unfold Returned at hr
    rw [hget] at hr
    simp only [Kind.resume] at hr
    omega
  refine
    { thr := hX.thr, outside := hX.outside, rf := hX.rf, ctaBar := hX.ctaBar, cluster := hH,
      dependency := ⟨fun e hr => ready_withClusterRecord hR hs hfresh (notReturned hr)
        (hX.dependency.ready e hr), horder.depAcyclic⟩,
      shfl := hX.shfl, vote := hX.vote, warpValue := hX.warpValue, matrix := hX.matrix,
      elect := hX.elect, warpBar := hX.warpBar,
      observation := horder.observation, object := horder.object,
      asyncObject := horder.asyncObject, initFence := horder.initFence, noFuture := ?_,
      hidden := ?_, tma := hX.tma, clc := hX.clc, tensor := hX.tensor, store := hX.store,
      reduce := ⟨hX.reduce.values, hX.reduce.copies⟩,
      atomic := ⟨hX.atomic.unique, hX.atomic.acyclic⟩, fenceSc := ?_, tmemPair := hX.tmemPair,
      tmemPairCompletion := hX.tmemPairCompletion, tmemPairResult := hX.tmemPairResult,
      tcCommit := hX.tcCommit,
      mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl, tcRead := ?_,
      asm := hasm }
  · exact hX.noFuture.of_frame (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context
        (X := X) (Y := X.withClusterRecord c R) rfl rfl
        (fun {l e f} => (modelCausality_withClusterRecord_iff hb' l e f).mp) (fun h => h))
  · exact hX.hidden.of_frame (fun _ _ _ h => h) (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context
        (X := X) (Y := X.withClusterRecord c R) rfl rfl
        (fun {l e f} => (modelCausality_withClusterRecord_iff hb' l e f).mp) (fun h => h))
  · exact ⟨hX.fenceSc.total, hX.fenceSc.acyclic,
      fun e f hs hc => hX.fenceSc.causal e f hs ((hb' e f).mp hc)⟩
  · have frame : TcMma.SemanticFrame L X (X.withClusterRecord c R) :=
      ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, hb', fun _ _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
    exact frame.readOk.mpr hX.tcRead

/-! ## The statements -/

/-- Appending the arrival record of a warp whose lanes are all at the same arrival, unrecorded, and
accepted by the cluster barrier run gives a consistent execution with the same size. -/
theorem arrival_consistent {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    {L : Launch} (hX : Consistent L K A mem0 X) {cta w pc : Nat} {release aligned : Bool}
    (hcta : cta < L.grid)
    (hlast : ∀ lt, lt < L.block → lt / 32 = w →
      X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) =
        some ⟨pc, .cluster (.arrive release aligned)⟩)
    (hfree : ∀ lt, lt < L.block → lt / 32 = w →
      ¬ ClusterRecorded L X (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1))
    (hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt (L.clusterOfCta cta)) {}
      (X.clusters (L.clusterOfCta cta) ++ [warpArrival L X cta w release]) = .done t)
    (hasm : ∀ a ∈ A, a.wf L mem0
      (X.withClusterRecord (L.clusterOfCta cta) (warpArrival L X cta w release))) :
    Consistent L K A mem0 (X.withClusterRecord (L.clusterOfCta cta) (warpArrival L X cta w release))
      ∧
      X.le (X.withClusterRecord (L.clusterOfCta cta) (warpArrival L X cta w release)) ∧
      (X.withClusterRecord (L.clusterOfCta cta) (warpArrival L X cta w release)).size L =
        X.size L := by
  have hcl := clusterOf_lt hX.cluster.1 hcta
  obtain ⟨s, hs⟩ := (hX.cluster.2.2 _ hcl).2.2
  have hnr := warp_refs_not_recorded (R := warpArrival L X cta w release) rfl hfree
  have hfresh := fresh_of_not_recorded hX.cluster hnr
  have hsync : ∀ e f, ClusterSync L (X.withClusterRecord (L.clusterOfCta cta)
      (warpArrival L X cta w release)) e f ↔ ClusterSync L X e f := by
    intro e f
    by_cases he : L.clusterOfCta (e.1 / L.block) = L.clusterOfCta cta
    · exact clusterSync_snoc_arrival hs rfl (fun e' he' r hr => hfresh _ r hr e' he') he
    · exact clusterSync_withClusterRecord_ne he
  refine ⟨consistent_withClusterRecord hX hcl (warpArrival_sources hX.cluster.1 hcta hlast)
    warpLanes_refs_nodup (fun _ _ h => by cases h) hfresh hacc (warp_refs_terminal rfl hlast)
    hsync hasm, le_withClusterRecord _ _ _, rfl⟩

/-- Appending the wait record of a warp whose lanes all wait at the same cluster wait, unrecorded,
and accepted by the cluster barrier run gives a consistent execution with the same size. -/
theorem wait_consistent {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    {L : Launch} (hX : Consistent L K A mem0 X) {cta w pc : Nat} {aligned : Bool}
    (hcta : cta < L.grid)
    (hlast : ∀ lt, lt < L.block → lt / 32 = w →
      X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) =
        some ⟨pc, .cluster (.wait aligned)⟩)
    (hfree : ∀ lt, lt < L.block → lt / 32 = w →
      ¬ ClusterRecorded L X (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1))
    (hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt (L.clusterOfCta cta)) {}
      (X.clusters (L.clusterOfCta cta) ++ [warpWait L X cta w]) = .done t)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.withClusterRecord (L.clusterOfCta cta) (warpWait L X cta w))) :
    Consistent L K A mem0 (X.withClusterRecord (L.clusterOfCta cta) (warpWait L X cta w)) ∧
      X.le (X.withClusterRecord (L.clusterOfCta cta) (warpWait L X cta w)) ∧
      (X.withClusterRecord (L.clusterOfCta cta) (warpWait L X cta w)).size L = X.size L := by
  have hcl := clusterOf_lt hX.cluster.1 hcta
  have hnr := warp_refs_not_recorded (R := warpWait L X cta w) rfl hfree
  have hfresh := fresh_of_not_recorded hX.cluster hnr
  have hterm := warp_refs_terminal (R := warpWait L X cta w) rfl hlast
  have hlast' : ∀ g ∈ (warpWait L X cta w).refs, g.2 + 1 = (X.tr g.1).length :=
    fun g hg => (hterm g hg).choose_spec.choose_spec.2
  have hsync : ∀ e f, ClusterSync L (X.withClusterRecord (L.clusterOfCta cta)
      (warpWait L X cta w)) e f ↔ ClusterSync L X e f := by
    intro e f
    by_cases he : L.clusterOfCta (e.1 / L.block) = L.clusterOfCta cta
    · exact ⟨clusterSync_of_snoc_wait rfl hlast' he,
        fun h => ClusterSync.mono h (le_withClusterRecord _ _ _)⟩
    · exact clusterSync_withClusterRecord_ne he
  refine ⟨consistent_withClusterRecord hX hcl (warpWait_sources hX.cluster.1 hcta hlast)
    warpLanes_refs_nodup (fun _ _ h => by cases h) hfresh hacc hterm hsync hasm,
    le_withClusterRecord _ _ _, rfl⟩

/-- Appending the arrival record of a warp to a maximal execution gives a maximal execution: the
record adds no size, so every consistent extension of the new execution extends the old one. -/
theorem arrival_maximal {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    {L : Launch} (hmax : Maximal L K A mem0 X) {cta w pc : Nat} {release aligned : Bool}
    (hcta : cta < L.grid)
    (hlast : ∀ lt, lt < L.block → lt / 32 = w →
      X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) =
        some ⟨pc, .cluster (.arrive release aligned)⟩)
    (hfree : ∀ lt, lt < L.block → lt / 32 = w →
      ¬ ClusterRecorded L X (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1))
    (hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt (L.clusterOfCta cta)) {}
      (X.clusters (L.clusterOfCta cta) ++ [warpArrival L X cta w release]) = .done t)
    (hasm : ∀ a ∈ A, a.wf L mem0
      (X.withClusterRecord (L.clusterOfCta cta) (warpArrival L X cta w release))) :
    Maximal L K A mem0 (X.withClusterRecord (L.clusterOfCta cta) (warpArrival L X cta w release)) :=
      by
  obtain ⟨hY, hle, hsize⟩ := arrival_consistent hmax.1 hcta hlast hfree hacc hasm
  refine ⟨hY, fun Z hZ hYZ => ?_⟩
  have h1 := hmax.2 Z hZ (Execution.le_trans hle hYZ)
  omega

/-- Appending the wait record of a warp to a maximal execution gives a maximal execution. -/
theorem wait_maximal {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    {L : Launch} (hmax : Maximal L K A mem0 X) {cta w pc : Nat} {aligned : Bool}
    (hcta : cta < L.grid)
    (hlast : ∀ lt, lt < L.block → lt / 32 = w →
      X.get (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1) =
        some ⟨pc, .cluster (.wait aligned)⟩)
    (hfree : ∀ lt, lt < L.block → lt / 32 = w →
      ¬ ClusterRecorded L X (cta * L.block + lt, (X.tr (cta * L.block + lt)).length - 1))
    (hacc : ∃ t, ClusterBarrier.run L.block (L.clusterSizeAt (L.clusterOfCta cta)) {}
      (X.clusters (L.clusterOfCta cta) ++ [warpWait L X cta w]) = .done t)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.withClusterRecord (L.clusterOfCta cta) (warpWait L X cta w))) :
    Maximal L K A mem0 (X.withClusterRecord (L.clusterOfCta cta) (warpWait L X cta w)) := by
  obtain ⟨hY, hle, hsize⟩ := wait_consistent hmax.1 hcta hlast hfree hacc hasm
  refine ⟨hY, fun Z hZ hYZ => ?_⟩
  have h1 := hmax.2 Z hZ (Execution.le_trans hle hYZ)
  omega

end
end PTX.Step

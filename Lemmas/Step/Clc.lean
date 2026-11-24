-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Issue
public import Lemmas.Step.Drain
public import Lemmas.Clc.ClcCompleteConsistentLaunch
public import Lemmas.Clc.ClcExecution
public import Lemmas.Flow.Fire

@[expose] public section

/-! # Issuing a cancellation request

A proof tool. A request issued at a thread's next index has no effects yet: the origin rule
admits effects only of actual requests (`fresh_effects`). Once every running cluster's task is
launched, a released thread can issue a request whose targets are the CTAs the request selects:
the execution with it appended is consistent and counts one more event
(`clc_issue_counted_extension`). Launching the running clusters' tasks is itself a consistent
extension of the same size that changes only the arbitration state (`prepare_launched`), so a
request steps after it. -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0} {g : Nat}

/-- No request has effects before it is issued. -/
theorem fresh_effects (hc : ClcOk L X) (g : Nat) : X.clc (g, (X.tr g).length) = {} := by
  let i : EvId := (g, (X.tr g).length)
  have absent (hn : (X.clc i).resolved.isSome ∨ (X.clc i).written.Nonempty ∨
      (X.clc i).notified.Nonempty) : False := by
    obtain ⟨s, targets, pc, hget⟩ := hc.2.2.1 i hn
    have hb := len_of_get hget
    dsimp only [i] at hb
    omega
  have hr : (X.clc i).resolved = none := by
    cases hh : (X.clc i).resolved with
    | none => rfl
    | some response => exact (absent (.inl (by simp [hh]))).elim
  have hw : (X.clc i).written = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    exact absent (.inr (.inl ⟨c, hc⟩))
  have hn : (X.clc i).notified = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    exact absent (.inr (.inr ⟨c, hc⟩))
  change X.clc i = {}
  cases he : X.clc i with
  | mk resolved written notified =>
    simp only [he] at hr hw hn
    cases hr
    cases hw
    cases hn
    rfl

/-- A request appended at a thread's next index, with the targets it selects, keeps the
cancellation rules once every running cluster's task is launched. -/
theorem issue_clcOk (hc : ClcOk L X) (hne : X.tr g ≠ []) {pc : Nat} {s : Clc.Spec}
    {ts : List Nat} (hts : ts.Nodup ∧ ∀ c, c ∈ ts ↔ Clc.Target L (g, (X.tr g).length) s c)
    (hown : ∀ h < L.threads, X.tr h ≠ [] →
      X.clcState.owner (L.clusterOfCta (h / L.block)) = some .launched) :
    ClcOk L (X.snoc g ⟨pc, .clcIssue s ts⟩ (fun _ => none)) := by
  have hempty := fresh_effects hc g
  obtain ⟨ha, hr, he, hi, -⟩ := hc
  have hle : X.le (X.snoc g ⟨pc, .clcIssue s ts⟩ (fun _ => none)) := le_snoc
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · intro request answer hh
    obtain ⟨i, s', ts', hid, hget⟩ := hr request answer hh
    exact ⟨i, s', ts', hid, by obtain ⟨q, hq⟩ := hget; exact ⟨q, Execution.le_get hle hq⟩⟩
  · intro i hh
    obtain ⟨s', ts', q, hget⟩ := he i hh
    exact ⟨s', ts', q, Execution.le_get hle hget⟩
  · intro i s' ts' ⟨q, hget⟩
    rcases snoc_get_cases hget with ⟨hindex, hnew⟩ | ⟨hold, hget⟩
    · subst i
      have hkind := congrArg Event.kind hnew
      obtain ⟨rfl, rfl⟩ := Kind.clcIssue.inj hkind
      refine ⟨⟨ha, ?_, ?_, ?_⟩, hts⟩
      · intro response hr'
        change (X.clc (g, (X.tr g).length)).resolved = some response at hr'
        simp [hempty] at hr'
      · intro c hc'
        change c ∈ (X.clc (g, (X.tr g).length)).written at hc'
        simp [hempty] at hc'
      · intro c hc'
        change c ∈ (X.clc (g, (X.tr g).length)).notified at hc'
        simp [hempty] at hc'
    · exact hi i s' ts' ⟨q, hget⟩
  · intro _ h hh hn
    apply hown h hh
    by_cases hg : h = g
    · simpa only [hg] using hne
    · simpa only [snoc_tr, ite_eq_right hg] using hn

/-- **A released thread issues a cancellation request** with the targets it selects, once every
running cluster's task is launched: a counted extension of a safe prefix. -/
theorem clc_issue_counted_extension (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X)
    (hr : ¬ Race L X) (hst : StrongOrdered L X) (hg : g < L.threads) (hne : X.tr g ≠
      []) (hrel : Released L X g)
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {pc : Nat} {s : Clc.Spec} {ts : List Nat}
    (he : EStep K A L g t1 ⟨pc, .clcIssue s ts⟩ o)
    (hts : ts.Nodup ∧ ∀ c, c ∈ ts ↔ Clc.Target L (g, (X.tr g).length) s c)
    (hown : ∀ h < L.threads, X.tr h ≠ [] →
      X.clcState.owner (L.clusterOfCta (h / L.block)) = some .launched)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .clcIssue s ts⟩ (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g ⟨pc, .clcIssue s ts⟩ (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hextra : ExtensionObligations L A (X.snoc g ⟨pc, .clcIssue s ts⟩ (fun _ => none)) :=
    .snoc_frame hX nofun nofun nofun (issue_clcOk hX.clc hne hts hown)
      (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc nofun nofun nofun nofun nofun)
      (hX.atomic.snoc hX.store hX.tma.1 nofun) (hX.fenceSc_snoc nofun nofun nofun nofun)
      (hX.matrix.snoc rfl) (fun _ h => Kind.noConfusion h)
  have htma : TmaOk (X.snoc g ⟨pc, .clcIssue s ts⟩ (fun _ => none)) :=
    hX.tmaOk_snoc_unobserved (fun _ h => by cases h)
      (objectAction_snoc_new (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h))
  exact snoc_counted_extension hX hm hr hst hg hrel hrun hl he
    (Kind.WaitFree.mk trivial (fun _ h => by cases h))
    nofun nofun rfl rfl nofun nofun nofun nofun nofun rfl htma hextra hasm hsg

/-- The targets of a request of a thread of the launch are the CTAs it selects. -/
theorem cancelSpec_targets (hv : L.oneDimLaunch) (hg : g < L.threads) {s : Clc.Spec}
    {ts : List Nat} (h : Flow.CancelSpec L g s ts) (k : Nat) :
    ts.Nodup ∧ ∀ c, c ∈ ts ↔ Clc.Target L (g, k) s c := by
  obtain ⟨hrs, hrc, hms, hmc, rfl⟩ := h
  have hcta : g / L.block < L.grid := by
    have hb : 0 < L.block := by
      rcases Nat.eq_zero_or_pos L.block with h0 | h0
      · simp [Launch.threads, h0] at hg
      · exact h0
    exact (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [Launch.threads] using hg)
  have hcv := Launch.oneDimLaunch_clusterGridValid hv
  refine ⟨?_, fun c => ?_⟩
  · split
    · exact (List.nodup_range).filter _
    · exact List.nodup_singleton _
  · simp only [Clc.Target, hrs, hrc, hms, hmc, true_and]
    split
    · simp only [List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨hcv, hg, h1, h2⟩, fun ⟨_, _, h1, h2⟩ => ⟨h1, h2⟩⟩
    · simp only [List.mem_singleton]
      exact ⟨fun h1 => ⟨hcv, hg, h1 ▸ hcta, h1⟩, fun ⟨_, _, _, h1⟩ => h1⟩

/-- A thread's release does not depend on the arbitration state. -/
theorem Released.clcState (h : Released L X g) (st : Clc.State) :
    Released L { X with clcState := st } g :=
  ⟨h.ready⟩

/-- A task that has an owner keeps it in every extension. -/
theorem owner_present_mono {Y : Execution} (hle : X.le Y) {task : Nat}
    (ho : (X.clcState.owner task).isSome) : (Y.clcState.owner task).isSome := by
  have hs : Clc.StateExtends X.clcState Y.clcState := hle.2.2.2.2.2.2.2.1
  cases hh : X.clcState.owner task with
  | none => simp [hh] at ho
  | some owner => simp [hs.1 task owner hh]

/-- A running cluster whose task has an owner has been launched: a cancellation owner has a
request, after which every running cluster is launched. -/
theorem running_present_launched (hc : ClcOk L X) (hg : g < L.threads) (hn : X.tr g ≠ [])
    (ho : (X.clcState.owner (L.clusterOfCta (g / L.block))).isSome) :
    X.clcState.owner (L.clusterOfCta (g / L.block)) = some .launched := by
  cases hh : X.clcState.owner (L.clusterOfCta (g / L.block)) with
  | none => simp [hh] at ho
  | some owner =>
    cases owner with
    | launched => rfl
    | canceled request =>
      obtain ⟨i, s, targets, _, hi, _⟩ := hc.canceled_has_issue hh
      simpa only [hh] using hc.2.2.2.2 ⟨i, s, targets, hi⟩ g hg hn

/-- Launching tasks changes only the arbitration state. -/
theorem prepare_owners (hA : Assumption.WfFree L mem0 A) (tasks : List Nat)
    (hX : Consistent L K A mem0 X) (hv : ∀ task ∈ tasks, Clc.ValidTask L task) :
    ∃ st, Consistent L K A mem0 { X with clcState := st } ∧ X.le { X with clcState := st } ∧
      ∀ task ∈ tasks, (st.owner task).isSome := by
  induction tasks generalizing X with
  | nil => exact ⟨X.clcState, hX, Execution.le_refl X, by simp⟩
  | cons task tasks ih =>
    have hhead : ∃ st, Consistent L K A mem0 { X with clcState := st } ∧
        X.le { X with clcState := st } ∧ (st.owner task).isSome := by
      cases ho : X.clcState.owner task with
      | none =>
        exact ⟨(X.launchClc task).clcState,
          consistent_launchClc hX (hv task (by simp)) ho (fun a ha => hA a ha _),
          launchClc_le ho, by simp [Execution.launchClc]⟩
      | some owner => exact ⟨X.clcState, hX, Execution.le_refl X, by simp [ho]⟩
    obtain ⟨st1, hY, hxy, howner⟩ := hhead
    obtain ⟨st2, hZ, hyz, howners⟩ := ih hY (fun k hk => hv k (by simp [hk]))
    refine ⟨st2, hZ, Execution.le_trans hxy hyz, ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact owner_present_mono (X := { X with clcState := st1 }) hyz howner
    · exact howners k hk

/-- **The running clusters' tasks can be launched**: a consistent extension changing only the
arbitration state, in which every running cluster's task is launched. -/
theorem prepare_launched (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hv : ∀ h < L.threads, Clc.ValidTask L (L.clusterOfCta (h / L.block))) :
    ∃ st, Consistent L K A mem0 { X with clcState := st } ∧ X.le { X with clcState := st } ∧
      ∀ h < L.threads, X.tr h ≠ [] → st.owner (L.clusterOfCta (h / L.block)) = some .launched := by
  obtain ⟨st, hZ, hle, hown⟩ := prepare_owners hA
    ((List.range L.threads).map fun h => L.clusterOfCta (h / L.block)) hX (by
      intro task ht
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ht
      exact hv h (List.mem_range.mp hh))
  refine ⟨st, hZ, hle, fun h hh hn => ?_⟩
  exact running_present_launched (X := { X with clcState := st }) hZ.clc hh hn
    (hown _ (List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩))

end
end PTX.Step

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.NextPlain
public import Lemmas.Step.Clc
public import Kernels.Fp16Gemm8192.Proof.Support.Scheduling

@[expose] public section

/-! # Progress at a copy issue or a cancellation request

A released pending thread whose next event issues a TMA load or a TMA store issues it
(`Step.issue_counted_extension`): the copy's effects are independent observations, none at
issue. A thread whose next event is a cancellation request issues it after the running clusters'
tasks are launched (`Step.prepare_launched`, an extension of the same size), with the targets the
request selects (`Step.cancelSpec_targets`, `Step.clc_issue_counted_extension`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at a TMA load steps.** -/
theorem tensorLoad_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
      (hk : nextKind d = .tensorLoad)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX (fun h => hsafe (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, s, u, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · exact .inl (Step.issue_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
      (strongOrdered hpre hX)
      hg hne hrel hrun hl (e := ⟨t1.pc, .tensorIssue a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩
      (.inl ⟨a, s, rfl⟩) (prod_wf _) (hsg.snoc ht.no_release (rmw_no_release ht hX) (no_fence ht hX)
        (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h)))

/-- **A released pending thread at a TMA store steps.** -/
theorem tensorStore_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
      (hk : nextKind d = .tensorStore)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX (fun h => hsafe (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, s, u, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · exact .inl (Step.issue_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
      (strongOrdered hpre hX)
      hg hne hrel hrun hl (e := ⟨t1.pc, .tensorStore a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩
      (.inr (.inl ⟨a, s, rfl⟩)) (prod_wf _) (hsg.snoc ht.no_release (rmw_no_release ht hX)
        (no_fence ht hX)
        (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h)))

/-- Every running cluster's task is a valid task of the launch. -/
theorem cluster_validTask (hpre : Pre P L mem0) {h : Nat} (hh : h < L.threads) :
    Clc.ValidTask L (L.clusterOfCta (h / L.block)) := by
  have hb := hpre.block
  have hh' : h < 1024 * 384 := by simpa [Launch.threads, hb, hpre.grid] using hh
  rw [clc_valid_task_iff hpre.oneDimLaunch hpre.grid hpre.cluster, clusterOfCta_eq hpre, hb]
  omega

/-- **A released pending thread at a cancellation request steps**, after the running clusters'
tasks are launched. -/
theorem clcIssue_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X)
    (hsafe : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ Unsafe L kernel Prod mem0 Y)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .clcIssue)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ :=
    next_fire ht hX (fun h => hsafe X hX (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨s, ts, u, rfl, hspec⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  obtain ⟨st, hZ, hle, hown⟩ := Step.prepare_launched (A := Prod)
    (fun a ha Y => prod_wf (L := L) (mem0 := mem0) Y a ha) hX
    (fun h hh => cluster_validTask hpre hh)
  have hv : L.oneDimLaunch := hpre.oneDimLaunch
  obtain ⟨Y, hY, hZY, hsize⟩ := Step.clc_issue_counted_extension (X := { X with clcState := st })
    hZ (noMixed_of_safe (hsafe _ hZ)) (noRace_of_safe (hsafe _ hZ))
    (strongOrdered hpre hZ) hg hne
    (hrel.clcState st) hrun hl
    (o := some u) (pc := t1.pc) ⟨_, hout, rfl, rfl⟩
    (Step.cancelSpec_targets hv hg hspec _) hown (prod_wf _)
    (SyncGuarded.snoc (X := { X with clcState := st })
      ⟨hsg.spin, hsg.noMemSync, hsg.noFault⟩ ht.no_release
      (fun e pc a o n h => rmw_no_release ht hX e pc a o n h)
      (fun e sem sc ⟨pc, h⟩ => no_fence ht hX e sem sc ⟨pc, h⟩) (fun _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h))
  exact .inl ⟨Y, hY, Execution.le_trans hle hZY, hsize⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress

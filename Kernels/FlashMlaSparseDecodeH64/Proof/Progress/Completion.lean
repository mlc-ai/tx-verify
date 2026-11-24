-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.CtaClosing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.RawGather
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingObjects
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorLoadSources
import Lemmas.Kernel.ProgressDescent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions

public section

/-! # Complete executions from closing arrivals and the two asynchronous producers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The single-CTA resource instructions wait for their operation before a later event,
so all allocator work is drained once every lane has returned. -/
theorem resources_drained_of_exits (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hexit : ∀ g < L.threads, ∃ i tag, X.get (g, i) = some ⟨tag, .exit⟩) :
    Tmem.Pair.Drained L X := by
  intro e tag grp dst req he
  obtain ⟨g, i⟩ := e
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, et, hExit⟩ := hexit g hg
  have hLast := Execution.exit_last hX hg hExit
  have hi : i < (X.tr g).length := PTX.len_of_get he
  have hne : i ≠ j := by
    rintro rfl
    rw [he] at hExit
    cases hExit
  have hLater : i + 1 < (X.tr g).length := by omega
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  have hGroup := (ResourceEvents.ordinal hpre hX (hs g hg).machine he hd).2.1
  exact hX.tmemPairBlocking.covered
    ⟨tag, grp, dst, req, he, by cases req <;> simp [hGroup]⟩ hLater

variable (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hmax hs ht

/-- Actual tensor-load notifications and Tensor Core completions suffice for the asynchronous
part of completeness at maximality. Output stores and commit notifications can then advance
while their effects remain pending. -/
theorem async_drained_of_inputs (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hTc : ∀ i, X.TcAsync i → X.async.mmaDone i = true)
    (hLoad : ∀ i addr sp, X.TensorIssue i addr sp →
      ∃ o, X.tensor i = some o ∧ o.effects.notified = true) :
    AsyncDrained X := by
  apply (asyncDrained_iff X).mpr
  refine ⟨fun i s hi => (GlobalWrites.no_copy hmax.1 hi).elim, ?_, hTc,
    fun i s ts hi _ _ => (GlobalWrites.no_clc hmax.1 hi).elim, hLoad, ?_, ?_⟩
  · intro i m noinc hi
    obtain ⟨tag, he⟩ := hi
    exact (Protocol.no_async_arrive hmax.1 he rfl).elim
  · intro i addr sp hi
    exact output_full_done hpre hmax hs ht hsafe hi
  · intro i s rank m hi hTarget
    exact completed_commit_notified hpre hmax hs ht hi hTarget (fun j hTrack => hTc j hTrack.2.2.1)

/-- Maximality turns actual closing arrivals and completed asynchronous producers into a complete
execution. The remaining progress inputs are arrivals of every launched lane, notification of
every actual query or gather load, and completion of every actual Tensor Core MMA or copy. -/
theorem complete_of_closing
    (hsafe : ∀ Y, Consistent L kernel Assumptions.all mem0 Y →
      ¬ Unsafe L kernel Assumptions.all mem0 Y)
    (hArrived : ∀ cta < L.grid, ∀ lane < L.block, ∃ i tag,
      X.get (cta * L.block + lane, i) = some ⟨tag, .bar 12 none .sync⟩)
    (hTc : ∀ i, X.TcAsync i → X.async.mmaDone i = true)
    (hLoad : ∀ i addr sp, X.TensorIssue i addr sp →
      ∃ o, X.tensor i = some o ∧ o.effects.notified = true) :
    Complete L X := by
  have hExit (g : Nat) (hg : g < L.threads) :
      ∃ i tag, X.get (g, i) = some ⟨tag, .exit⟩ := by
    have hb : 0 < L.block := by rw [hpre.block]; decide
    have hCta : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).2 hg
    have hLane : g % L.block < L.block := Nat.mod_lt _ hb
    obtain ⟨i, tag, he⟩ := cta_exited_of_arrived hpre hmax hs ht hsafe hCta (hArrived _ hCta)
      _ hLane
    rw [Nat.mul_comm, Nat.div_add_mod] at he
    exact ⟨i, tag, he⟩
  refine ⟨?_, async_drained_of_inputs hpre hmax hs ht (hsafe _ hmax.1) hTc hLoad,
    resources_drained_of_exits hpre hmax.1 hs ht hExit⟩
  intro g hg
  obtain ⟨i, tag, he⟩ := hExit g hg
  refine .inr ⟨tag, ?_⟩
  have hLast := Execution.exit_last hmax.1 hg he
  rw [List.getLast?_eq_getElem?, ← hLast]
  exact he

/-- Each actual query or gather load has delivered its notification in a maximal execution. -/
theorem tensor_loads_drained {i : EvId} {addr : Nat} {sp : TensorCopy.Spec}
    (hi : X.TensorIssue i addr sp) :
    ∃ o, X.tensor i = some o ∧ o.effects.notified = true := by
  classical
  by_contra hn
  have hPending : (X.tensor i).any (fun o => o.effects.notified) = false := by
    cases ho : X.tensor i with
    | none => rfl
    | some o =>
      cases hnote : o.effects.notified
      · exact hnote
      · exact (hn ⟨o, ho, hnote⟩).elim
  obtain ⟨g, j⟩ := i
  apply hmax.not_grows
  rcases TensorLoadSources.issue_kind hpre hmax.1 hs ht hi with ⟨k, rfl, rfl⟩ | ⟨d, k, hd, hk⟩
  · exact query_tensor_extension hpre k hs hmax.1 ht hi hPending
  · exact raw_gather_extension hpre hs hmax.1 ht hi hd hk hPending

/-- Actual arrival of every lane and completion of its Tensor Core operations suffice for
completeness at maximality, once the safety and tracking facts are available. -/
theorem complete_of_closing_and_tc
    (hsafe : ∀ Y, Consistent L kernel Assumptions.all mem0 Y →
      ¬ Unsafe L kernel Assumptions.all mem0 Y)
    (hArrived : ∀ cta < L.grid, ∀ lane < L.block, ∃ i tag,
      X.get (cta * L.block + lane, i) = some ⟨tag, .bar 12 none .sync⟩)
    (hTc : ∀ i, X.TcAsync i → X.async.mmaDone i = true) :
    Complete L X :=
  complete_of_closing hpre hmax hs ht hsafe hArrived hTc
    (fun _ _ _ hi => tensor_loads_drained hpre hmax hs ht hi)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

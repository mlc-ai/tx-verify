-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.AllocatorBlocked
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.BarrierBlocked
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.BulkWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingResourceBlocked
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.RegisterBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.TcCollective
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RegisterRequestTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceWaitTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StaticCollectiveEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WaitSources

public section

/-! # Every pending lane has strictly earlier pending work at maximality -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem body_after_prologue {g : Nat} {d : Machine.ThreadD}
    (h : ∀ s, d ≠ .prologue s) : 99 < priority P L g d := by
  cases d
  case prologue s => exact (h s rfl).elim
  case head => simp [priority]
  case idle s => cases s <;> simp [priority, completionTime, blockTime]
  case done => simp [priority, completionTime, blockTime]
  case wg0 d | mma d | tma d | index d | wg2 d =>
    all_goals cases hd : d.site <;> simp [hd, priority, completionTime, blockTime,
      softmaxTime, matmulTime, gatherTime, indexTime, quantTime]
    all_goals omega

/-- Every pending represented state of a maximal followed trace descends strictly. -/
theorem pending_earlier {g : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (htrack : ∀ Y, Consistent L kernel Assumptions.all mem0 Y →
      Frame.Tracked (Machine.code P L) Y)
    (hp : PendingState P L X g d) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
  let tail := (g, (X.tr g).length - 1)
  have hX := hmax.1
  have ht := htrack X hX
  by_cases hRel : PTX.Step.Released L X g
  · exact pending_released_earlier hpre hmax hs ht hp hRel
  have hLast : ∃ tag k, X.get tail = some ⟨tag, k⟩ ∧
      k.resume = .blocking false ∧ ¬ Ready L X tail := by
    by_contra! h
    exact hRel ⟨fun tag k he hResume => h tag k he hResume⟩
  obtain ⟨tag, k, he, hResume, hWait⟩ := hLast
  cases k
  case setMaxReg inc n inst =>
    obtain ⟨h, q, hP, hLe⟩ := waiting_register_prologue hpre hX hs ht he hWait
    have hBody : ∀ s, d ≠ .prologue s := by
      intro s hS
      subst d
      exact RegisterRequestTrace.no_request_at_prologue hX (hs g hp.1.1).machine hp.1.1 hp.2
        _ _ _ _ _ he
    exact ⟨h, .prologue q, hP, lt_of_le_of_lt hLe (body_after_prologue hBody)⟩
  case bar id count mode => exact pending_barrier_earlier hpre hmax hs htrack hp he
  case cluster op => exact (StaticCollectiveEvents.no_cluster hX he).elim
  case asyncWait n => exact (WaitSources.no_async_wait hX he).elim
  case bulkWait mode n =>
    obtain ⟨rfl, rfl, w, hw, hSite⟩ := WaitSources.opening_bulk_wait hX hs ht he
    exact (hRel (opening_bulk_wait_released hpre hX hs ht he hSite hw)).elim
  case tc c =>
    have data (hc : isTcColl ⟨tag, .tc c⟩ = true)
        (hn : ∀ grp dst req, c ≠ .resource grp dst req) :
        ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
      obtain ⟨w, hS, hResult⟩ := tc_data_release_or_earlier hpre hX hs ht
        (Safety.no_ub hpre hX hs ht) (fun _ h => pending_followed hpre hX hs ht h)
        hp.1 he hc hn
      obtain rfl : d = .wg0 w := Option.some.inj (Option.some.inj (hp.2.symm.trans hS))
      rcases hResult with hRel' | ⟨h, q, _, hP, hT, hLt⟩
      · exact (hRel hRel').elim
      · exact ⟨h, q, ⟨hP, hT⟩, hLt⟩
    cases c
    case resource grp dst req =>
      obtain ⟨_, rfl, n, hN, rfl, _⟩ := ResourceEvents.request_origin hpre hX hs ht he
      by_cases hn : n < 2
      · exact pending_allocator_earlier hpre hmax hs ht hp hn he
      · obtain rfl : n = 2 := by omega
        exact pending_deallocation_earlier hpre hmax hs ht hp he
    all_goals first | exact data rfl nofun | cases hResume
  all_goals cases hResume

/-- The CTA closing arrivals occur in every maximal execution of the followed machine. -/
theorem all_closing_arrived_of_tracking
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (htrack : ∀ Y, Consistent L kernel Assumptions.all mem0 Y →
      Frame.Tracked (Machine.code P L) Y) :
    AllClosingArrived L X :=
  closing_arrivals_of_descent hpre hmax.1 hs (htrack X hmax.1)
    (fun _ _ hp => pending_earlier hpre hmax hs htrack hp)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

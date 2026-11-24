-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Lemmas.Step.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.DequantReleased
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.DispatchBroadcast
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.GatherReleased
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.IdleReleased
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.IndexReleased
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaReleased
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.SoftmaxReleased
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.StartupBroadcast
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MemoryConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressAllocation
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressHandoff
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPrologueIssue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressStartupElection
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace

public section

/-! # A released pending lane makes progress or descends to an earlier lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem pending_prologue_released {g : Nat} {s : Site}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g (.prologue s)) (hRel : PTX.Step.Released L X g) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.prologue s) := by
  have hX := hmax.1
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hub : ¬ HasUb X := fun h => hSafe (.inl h)
  have hOrd := Safety.reads_ordered hpre hX hs ht
  have election (second : Bool)
      (hS : s = if second then .elect1 else .elect0) : False := by
    have hState := hp.2
    rw [hS] at hState
    obtain ⟨hLen, hWarp⟩ := PrologueRoleTrace.election_position hpre hX
      (fun h hh => (hs h hh).machine) le_rfl hState
    exact hmax.not_grows (startup_election_extension hpre hX hs hub hp.1.1 second
      (startup_election_peers hpre hX hs hWarp second hLen))
  cases s
  case shfl0 => exact (first_broadcast_not_pending hpre hmax hs hub hp).elim
  case shfl1 => exact pending_second_broadcast_earlier hpre hmax hs hub hp
  case elect0 => exact (election false rfl).elim
  case elect1 => exact (election true rfl).elim
  case init j => exact (hmax.not_grows (prologue_init_extension hpre hX hs hOrd hSafe
                        hp.1 hRel hp.2)).elim
  case fence => exact (hmax.not_grows (prologue_fence_extension hX hs hOrd hSafe
                      hp.1 hRel hp.2)).elim
  case alloc => exact (hmax.not_grows (prologue_resource_extension hpre hX hs hub
                      hp.1 hRel hp.2 (.inl rfl))).elim
  case allocStore =>
    have hAlloc := PrologueAllocation.alloc_store_predecessor hpre hX hs hp.2
    exact (hmax.not_grows (PrologueAllocation.alloc_store_extension hpre hX hs hub
      (Safety.no_resourceUnsafe hpre hX hs ht) hp.1 hRel hp.2 hAlloc)).elim
  case allocRead =>
    exact (hmax.not_grows (PrologueAllocation.alloc_read_extension hpre hX hs hub
      (sync_guarded hX hSafe) hp.1 hRel hp.2)).elim
  case relinquish => exact (hmax.not_grows (prologue_resource_extension hpre hX hs hub
                           hp.1 hRel hp.2 (.inr rfl))).elim
  case barrier => exact (hmax.not_grows (prologue_gate_extension hX hs hub hp.1 hRel hp.2)).elim
  case handoff w => exact (hmax.not_grows (prologue_handoff_extension hX hs hub
                          hp.1 hRel hp.2)).elim

/-- Every released machine state has strict pending-thread descent at maximality. -/
theorem pending_released_earlier {g : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g d) (hRel : PTX.Step.Released L X g) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
  cases d with
  | prologue _ => exact pending_prologue_released hpre hmax hs ht hp hRel
  | head => exact pending_dispatch_earlier hpre hmax hs ht hp
  | wg0 _ => exact pending_softmax_released hpre hmax hs ht hp hRel
  | mma _ =>
    obtain ⟨h, q, _, hP, hLt⟩ := pending_mma_released hpre hmax hs ht hp hRel
    exact ⟨h, q, hP, hLt⟩
  | tma _ => exact pending_gather_released hpre hmax hs ht hp hRel
  | index _ => exact pending_index_earlier hpre hmax hs ht hp
  | wg2 _ => exact pending_dequant_released hpre hmax hs ht hp hRel
  | idle _ => exact (idle_released_not_pending hpre hmax hs ht hp hRel).elim
  | done => exact (done_released_not_pending hpre hmax hs ht hp hRel).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

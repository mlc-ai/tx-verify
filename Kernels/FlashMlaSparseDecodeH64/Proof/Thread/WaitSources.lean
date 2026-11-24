-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Flow.NotAsyncWait
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotClc
import Lemmas.Flow.OpPcsFast

public section

/-! # The frozen sources of bulk and per-thread async waits -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.WaitSources

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 100000 in
private theorem no_async_wait_site : OpPcsFast kernel.code asyncWaitOp [] = true := by
  decide +kernel

/-- There is no ordinary cp.async group wait in the frozen instruction stream. -/
theorem no_async_wait (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {tag n : Nat} (he : X.get i = some ⟨tag, .asyncWait n⟩) : False := by
  rcases PTX.Flow.get_source hX he with ⟨_, h⟩ | ⟨_, _, _, _, hc, hf⟩
  · cases h
  · exact List.not_mem_nil
      (OpPcsFast.mem no_async_wait_site hc (fires_asyncWait_op hf rfl))

set_option maxRecDepth 100000 in
private theorem bulk_wait_sites : OpPcsFast kernel.code bulkWaitOp [Flow.bulkWait_0] = true := by
  decide +kernel

local macro "exclude_bulk_wait" : tactic =>
  `(tactic| first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide))

private theorem bulk_wait_site {g : Nat} {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d = Flow.bulkWait_0) :
    ∃ w, d = .wg0 w ∧ w.site = .bulkWait := by
  cases d
  case wg0 w =>
    refine ⟨w, rfl, ?_⟩
    change w.site.pc = Flow.bulkWait_0 at h
    generalize w.site = s at h ⊢
    clear w
    cases s <;> first | rfl | (exfalso; revert h; exclude_bulk_wait)
  case head => exact (show (1843 : Nat) ≠ Flow.bulkWait_0 by decide) h |>.elim
  case done => exact (show (3611 : Nat) ≠ Flow.bulkWait_0 by decide) h |>.elim
  case prologue s | idle s =>
    exfalso
    change s.pc = Flow.bulkWait_0 at h
    cases s <;> revert h <;> exclude_bulk_wait
  case mma w | tma w | index w | wg2 w =>
    all_goals exfalso
    all_goals change w.site.pc = Flow.bulkWait_0 at h
    all_goals generalize w.site = s at h
    all_goals clear w
    all_goals cases s <;> revert h <;> exclude_bulk_wait

/-- The only bulk-group wait is the opening softmax read wait for zero remaining groups. -/
theorem opening_bulk_wait (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g i tag n : Nat} {mode : BulkGroup.WaitMode}
    (he : X.get (g, i) = some ⟨tag, .bulkWait mode n⟩) :
    mode = .read ∧ n = 0 ∧ ∃ d,
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧ d.site = .bulkWait := by
  obtain ⟨d, o, hd, hf⟩ := RingSourceSites.fired_from_trace hX
    (hs g (Frame.lt_of_get hX he)).machine ht he (by simp)
  obtain ⟨t, _, hFire⟩ := hf
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) ⟨tag, .bulkWait mode n⟩ o at hFire
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none => rw [hc] at hFire; cases hFire.1
  | some ins =>
    rw [hc] at hFire
    have hSite := List.mem_singleton.mp (OpPcsFast.mem bulk_wait_sites hc
      (fires_bulkWait_op hFire rfl))
    obtain ⟨w, rfl, hw⟩ := bulk_wait_site hSite
    rw [hSite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkWait_0)
    have hKind := Kind.bulkWait.inj (congrArg Event.kind hFire.1)
    exact ⟨hKind.1, hKind.2, w, hd, hw⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.WaitSources

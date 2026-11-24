-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Lemmas.Tmem.PairProtocol
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcTrace

public section

/-! # The Tensor Memory resource request at a lane's actual tail -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents

open PTX PTX.Flow Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

theorem request_index {g i tag n : Nat} {dst : Option Loc} (hn : n < 3)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource .one dst (opAct 0 n).request)⟩) :
    opsAt X g i = n := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨_, _, hLt, hReq⟩ := ordinal hpre hX (hs g hg).machine he hd
  generalize hk : opsAt X g i = k at hLt hReq ⊢
  interval_cases n <;> interval_cases k <;> first | rfl | contradiction

/-- A resource request's group and operation are recovered from its trace ordinal. -/
theorem request_origin {g i tag : Nat} {grp : CtaGroup} {dst : Option Loc} {req : Tmem.Request}
    (he : X.get (g, i) = some ⟨tag, .tc (.resource grp dst req)⟩) :
    warpOf L g = 0 ∧ grp = .one ∧
      ∃ n < 3, req = (opAct 0 n).request ∧ opsAt X g i = n := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨hw, hGroup, hLt, hKind⟩ := ordinal hpre hX (hs g hg).machine he hd
  exact ⟨hw, hGroup, _, hLt, hKind, rfl⟩

/-- At the first two allocator requests the collective ordinal is their resource ordinal. -/
theorem prologue_wait_state {g tag n : Nat} {dst : Option Loc} (hn : n < 2)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨tag, .tc (.resource .one dst (opAct 0 n).request)⟩)
    :
    X.TcK (g, (X.tr g).length - 1) n ∧ ∃ s,
      Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.prologue s)) ∧
      (if n = 0 then s = .allocStore ∨ s = .allocRead else s = .barrier) := by
  let i := (X.tr g).length - 1
  have hg := Frame.lt_of_get hX he
  have hi : i < (X.tr g).length := PTX.len_of_get he
  have hl : i + 1 = (X.tr g).length := by dsimp [i]; omega
  obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht he
    (by simp)
  have hEmit := emits hpre hf rfl
  rcases n with _ | n
  · have hAlloc : d = .prologue .alloc := by cases hEmit <;> first | rfl | contradiction
    subst d
    have hF := (Wg0TcTrace.prologue_rank_at hpre hX (hs g hg).machine hg hi.le hd).2
    refine ⟨⟨⟨_, he, rfl⟩, hF⟩, if laneOf L g = 0 then .allocStore else .allocRead, ?_, ?_⟩
    · rw [← hl, Frame.stateAt_succ he, hd]
      change Machine.next P L g (.prologue .alloc)
        ⟨tag, .tc (.resource .one dst (.alloc 512))⟩ = _
      simp only [Machine.next, Proof.next]
      split_ifs <;> rfl
    · dsimp
      split_ifs <;> simp
  · obtain rfl : n = 0 := by omega
    have hRel : d = .prologue .relinquish := by cases hEmit <;> first | rfl | contradiction
    subst d
    have hF := (Wg0TcTrace.prologue_rank_at hpre hX (hs g hg).machine hg hi.le hd).2
    refine ⟨⟨⟨_, he, rfl⟩, hF⟩, .barrier, ?_, rfl⟩
    rw [← hl, Frame.stateAt_succ he, hd]
    rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents

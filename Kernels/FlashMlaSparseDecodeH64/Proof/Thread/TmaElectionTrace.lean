-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueShuffleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineSound

public section

/-! # The gather election follows the warpgroup-one dispatch exactly once -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaElectionTrace

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

set_option maxRecDepth 4096

private theorem role_no_election_return {q d : Wg1Tma.D} {e : Event}
    (hD : d.site = .elect)
    (hn : Wg1Tma.next P L g q e = some (some d)) : False := by
  cases hSite : q.site
  all_goals simp only [Wg1Tma.next, hSite] at hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals
    have he := congrArg Wg1Tma.D.site hn
    rw [hD] at he
    try rw [hSite] at he
    try simp only [Wg1Tma.firstLenSite, Wg1Tma.beginLoop, Wg1Tma.afterCoord,
      Wg1Tma.afterIssue, Wg1Tma.afterFree] at he
    try split_ifs at he
    all_goals cases he

/-- The only predecessor of the followed election is the dispatch shuffle. -/
theorem election_after_dispatch (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) {i : Nat} {d : Wg1Tma.D} (hi : i ≤ (X.tr g).length)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hElect : d.site = .elect) :
    ∃ k, k + 1 = i ∧ Frame.stateAt (Machine.code P L) X g k = some (some .head) := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hState; cases hState
  | succ k =>
    obtain ⟨before, hBefore⟩ := Frame.stateAt_live ht hg hState (Nat.le_succ k)
    have he : X.get (g, k) = some (X.tr g)[k] := List.getElem?_eq_getElem hi
    have hNext := (Frame.stateAt_succ (C := Machine.code P L) he).symm.trans hState
    rw [hBefore, Option.bind_some] at hNext
    change Machine.next P L g before (X.tr g)[k] = some (some (.tma d)) at hNext
    cases before
    case head => exact ⟨k, rfl, hBefore⟩
    case tma q =>
      simp only [Machine.next] at hNext
      split at hNext
      · rename_i p hp
        cases hNext
        exact (role_no_election_return hElect hp).elim
      · repeat' split at hNext
        all_goals cases hNext
      · split at hNext <;> cases hNext
    case prologue s =>
      simp only [Machine.next] at hNext
      split at hNext
      · cases hNext
      · split at hNext
        · rename_i w _
          split_ifs at hNext
          · fin_cases w <;> cases hNext
          · cases hNext
        · cases hNext
      · cases hNext
    all_goals simp only [Machine.next] at hNext
    all_goals repeat' split at hNext
    all_goals cases hNext

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
include hpre hX hs

/-- A followed gather election is the sixth event position. -/
theorem election_position (ht : Frame.Tracked (Machine.code P L) X) (hg : g < L.threads) {i : Nat}
    {d : Wg1Tma.D} (hi : i ≤ (X.tr g).length)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hElect : d.site = .elect) : i = 5 := by
  obtain ⟨k, rfl, hHead⟩ := election_after_dispatch ht hg hi hState hElect
  rw [(PrologueRoleTrace.head_position hpre hX hs (Nat.le_of_succ_le hi) hHead).1]

/-- Before the sixth position, a warp-five lane is still in the prologue or at dispatch. -/
theorem early_state (hw : warpOf L g = 5) {i : Nat} (hi : i ≤ (X.tr g).length) (hEarly : i < 5) :
    (∃ s, Frame.stateAt (Machine.code P L) X g i = some (some (.prologue s))) ∨
      Frame.stateAt (Machine.code P L) X g i = some (some .head) := by
  have he (k : Nat) (hk : k < i) : ∃ e, X.get (g, k) = some e :=
    ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hk hi)⟩
  have hGroup : wgOf L g = 1 := by
    unfold wgOf warpOf at *
    omega
  interval_cases i
  · exact .inl ⟨_, Frame.stateAt_zero⟩
  · obtain ⟨_, h⟩ := he 0 (by decide)
    exact .inl ⟨_, PrologueShuffleTrace.state_one hpre hX hs h⟩
  · obtain ⟨_, h⟩ := he 1 (by decide)
    have hp := PrologueShuffleTrace.state_two hpre hX hs h
    rw [hw] at hp
    exact .inl ⟨_, hp⟩
  · obtain ⟨_, h⟩ := he 2 (by decide)
    exact .inl ⟨_, PrologueShuffleTrace.state_three hpre hX hs h hGroup⟩
  · obtain ⟨_, h⟩ := he 3 (by decide)
    exact .inr (PrologueShuffleTrace.state_four hpre hX hs h hGroup)

/-- A warp-five lane reaching the sixth position is ready to issue its election. -/
theorem election_at_five (hw : warpOf L g = 5) (hi : 5 ≤ (X.tr g).length) :
    Frame.stateAt (Machine.code P L) X g 5 = some (some (.tma (Wg1Tma.init P L g))) := by
  have hGroup : wgOf L g = 1 := by unfold wgOf warpOf at *; omega
  have he : X.get (g, 4) = some (X.tr g)[4] := List.getElem?_eq_getElem hi
  rw [PrologueShuffleTrace.state_five hpre hX hs he hGroup, Machine.headStart_eq5 (by omega) hw]
  rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaElectionTrace

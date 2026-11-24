-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressStartupShuffle
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueShuffleTrace
import Lemmas.Step.WarpShfl

public section

/-! # Progress at the two common launch broadcasts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem early_warp_peers {g n : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hn : n ≤ 1) (hLen : (X.tr g).length = n) {h : Nat} (hw : SameWarp L g h) :
    SameWarp L g h ∧ (X.tr h).length ≤ n := by
  refine ⟨hw, ?_⟩
  by_contra! hMore
  obtain ⟨e, he⟩ : ∃ e, X.get (h, n) = some e := by
    exact ⟨(X.tr h)[n], List.getElem?_eq_getElem hMore⟩
  have hK := PrologueShuffleTrace.early_shuffle_ordinal hpre hX
    (fun z hz => (hs z hz).machine) hn he
  obtain ⟨⟨_, _, _, _, _, _, _, he'⟩, _⟩ := id hK
  rcases PTX.Step.shfl_lane_of_ready hX he' hK ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩ with
    ⟨j, hj⟩ | ⟨j, tag, hj, _⟩
  · have hCount : n < (X.tr g).countP Execution.isShfl := PTX.Step.ShflK.lt_count hj
    have hSize := List.countP_le_length (p := Execution.isShfl) (l := X.tr g)
    omega
  · obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
    exact hRun.no_exit hj

private theorem early_peer_tail {h : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hh : h < L.threads) (hLen : (X.tr h).length ≤ 1) :
    Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length =
        some (some ((if (X.tr h).length = 0 then StartupShuffle.group
          else StartupShuffle.warp).state)) := by
  have hlast (e : Event) (he : X.get (h, (X.tr h).length - 1) = some e) :
      ∃ tag a recv ok, e = ⟨tag, .shfl .idx a 0 31 recv ok⟩ := by
    have hPos := PTX.len_of_get he
    have hZero : (X.tr h).length - 1 = 0 := by omega
    rw [hZero] at he
    exact ⟨_, _, _, _, PrologueShuffleTrace.first_event hpre hX
      (fun z hz => (hs z hz).machine) he⟩
  refine ⟨⟨hh, ?_, ?_⟩, .of_get ?_, ?_⟩
  · rintro ⟨_, _, hCanceled⟩
    obtain ⟨i, sp, targets, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
    exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hi
  · intro tag he
    rw [List.getLast?_eq_getElem?] at he
    obtain ⟨_, _, _, _, h⟩ := hlast _ he
    exact Kind.noConfusion (congrArg Event.kind h)
  · intro e he
    obtain ⟨_, _, _, _, rfl⟩ := hlast e he
    simp [Kind.resume]
  · by_cases hz : (X.tr h).length = 0
    · rw [hz, ite_eq_left rfl, Frame.stateAt_zero]
      rfl
    · have hOne : (X.tr h).length = 1 := by omega
      obtain ⟨e, he⟩ : ∃ e, X.get (h, 0) = some e := by
        have hPos : 0 < (X.tr h).length := by omega
        exact ⟨(X.tr h)[0], List.getElem?_eq_getElem hPos⟩
      rw [hOne, ite_eq_right (by decide)]
      exact PrologueShuffleTrace.state_one hpre hX (fun z hz => (hs z hz).machine) he

/-- Pending lanes at the first broadcast can issue the full warp's first events. -/
theorem first_broadcast_not_pending {g : Nat} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.prologue .shfl0)) : False := by
  have hn := PrologueRoleTrace.first_shuffle_position le_rfl hp.2
  apply hmax.not_grows (startup_shuffle_extension hpre hs hmax.1 hp.1.1 hub .group ?_)
  intro h hw
  have hSize := (early_warp_peers hpre hmax.1 hs hub hp.1 (by decide) hn hw).2
  have hz : (X.tr h).length = 0 := by omega
  simpa only [hz, ↓reduceIte] using
    (early_peer_tail hpre hmax.1 hs hw.1.2.1 (by omega : (X.tr h).length ≤ 1))

/-- A pending second broadcast either has a peer at the first or can issue the full warp. -/
theorem pending_second_broadcast_earlier {g : Nat} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.prologue .shfl1)) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.prologue .shfl1) := by
  have hn := PrologueRoleTrace.second_shuffle_position le_rfl hp.2
  by_contra hEarlier
  apply hmax.not_grows (startup_shuffle_extension hpre hs hmax.1 hp.1.1 hub .warp ?_)
  intro h hw
  have hSize := (early_warp_peers hpre hmax.1 hs hub hp.1 (by decide) hn hw).2
  obtain ⟨hPending, hRel, hState⟩ := early_peer_tail hpre hmax.1 hs hw.1.2.1 hSize
  by_cases hz : (X.tr h).length = 0
  · rw [ite_eq_left hz] at hState
    exact (hEarlier ⟨h, .prologue .shfl0, ⟨hPending, hState⟩,
      by simp [priority, prologueRank]⟩).elim
  · rw [ite_eq_right hz] at hState
    exact ⟨hPending, hRel, hState⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

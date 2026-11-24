-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaElectionTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressTmaElection
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueShuffleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
import Lemmas.Clc.ClcExecution
import Lemmas.Order.ElectOrdinal

public section

/-! # The gather election either progresses or has a lane before dispatch -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

private theorem no_elect_before_dispatch {g i inst leader : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hw : warpOf L g = 5) (hi : i < 5)
    (he : X.Elect (g, i) Wg1Tma.Site.elect.pc (2 ^ 32 - 1) inst leader) : False := by
  let sound := fun h hh => (hs h hh).machine
  rcases TmaElectionTrace.early_state hpre hX sound hw (len_of_get he).le hi with
    ⟨s, hState⟩ | hState
  · have hPc := Frame.event_pc hs hX he hState
    change Wg1Tma.Site.elect.pc = s.pc at hPc
    have hDifferent : ∀ s : Site, Wg1Tma.Site.elect.pc ≠ s.pc := by
      intro s
      cases s
      all_goals first | decide +kernel | (rename_i j; revert j; decide +kernel)
    exact hDifferent s hPc
  · have hPc := Frame.event_pc hs hX he hState
    change Wg1Tma.Site.elect.pc = (Machine.code P L g).pc .head at hPc
    cases hPc

/-- The warp-five election progresses once all lanes have dispatched. If a lane has yet to
dispatch, its actual prologue state has smaller dependency priority. -/
theorem pending_tma_election_earlier {g : Nat} {d : Wg1Tma.D}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.tma d)) (hd : d.site = .elect) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.tma d) := by
  classical
  have hX := hmax.1
  let sound := fun h hh => (hs h hh).machine
  have hwg : warpOf L g = 5 := RingRoleGeometry.of_trace hX hp.1.1 (sound g hp.1.1) hp.2
  have hLength := TmaElectionTrace.election_position hpre hX sound ht hp.1.1 le_rfl hp.2 hd
  have hCore (h : Nat) : warpOf L h = h % L.block / 32 := by
    simp [warpOf, tidOf_eq hpre, hpre.block]
  have hw {h : Nat} (hWarp : SameWarp L g h) : warpOf L h = 5 := by
    rw [hCore, ← hWarp.2, ← hCore, hwg]
  have hLe {h : Nat} (hWarp : SameWarp L g h) : (X.tr h).length ≤ 5 := by
    by_contra! hLong
    have hh := TmaElectionTrace.election_at_five hpre hX sound (hw hWarp) hLong.le
    have he : X.get (h, 5) = some (X.tr h)[5] := List.getElem?_eq_getElem hLong
    obtain ⟨inst, leader, heq⟩ := tma_election_event hs hX hh rfl he
    rw [heq] at he
    have hPeer : X.Elect (h, 5) Wg1Tma.Site.elect.pc (2 ^ 32 - 1) inst leader := he
    obtain ⟨_, _, j, tag, l, _, hGet⟩ := elect_ready hX hPeer _
      (elect_need_mem (L := L) hPeer (full_member L g))
    rw [PTX.Step.warpLane_of_sameWarp (sameWarp_symm hWarp)] at hGet
    have hg : X.Elect (g, j) tag (2 ^ 32 - 1) inst l := hGet
    have hSame := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ hPeer hg (sameWarp_symm hWarp)).1
    have hJ : j < 5 := by simpa only [hLength] using len_of_get hg
    exact no_elect_before_dispatch hpre hX hs hwg hJ (hSame ▸ hg)
  have hPending {h : Nat} (hWarp : SameWarp L g h) : Frame.Pending L X h := by
    refine ⟨hWarp.1.2.1, ?_, ?_⟩
    · rintro ⟨_, _, hCancel⟩
      obtain ⟨i, sp, targets, _, hIssue, _⟩ := hX.clc.canceled_has_issue hCancel
      exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hIssue
    · intro tag hLast
      rw [List.getLast?_eq_getElem?] at hLast
      obtain ⟨j, _, _, hj⟩ := ClosingOrder.arrival_before_exit hpre hX hs ht hLast
      obtain ⟨p, hP, hSite, _, _⟩ := ScoreClosingGate.closing_at hpre hX hs ht hj
      have hJ := len_of_get hj
      have hLimit := hLe hWarp
      rcases TmaElectionTrace.early_state hpre hX sound (hw hWarp) hJ.le
          (show j < 5 by omega) with ⟨s, hState⟩ | hState
      · rw [hState] at hP
        cases hP
        exact hSite
      · rw [hState] at hP
        cases hP
        exact hSite
  by_cases hShort : ∃ h, SameWarp L g h ∧ (X.tr h).length < 5
  · obtain ⟨h, hWarp, hh⟩ := hShort
    rcases TmaElectionTrace.early_state hpre hX sound (hw hWarp) le_rfl hh with
      ⟨s, hState⟩ | hState
    · refine ⟨h, .prologue s, hWarp.1, ⟨hPending hWarp, hState⟩, ?_⟩
      simp only [priority, gatherTime, hd, tmaOrdinal]
      omega
    · exact ⟨h, .head, hWarp.1, ⟨hPending hWarp, hState⟩, by simp [priority, gatherTime, hd,
        tmaOrdinal]⟩
  · exfalso
    apply hmax.not_grows
    refine tma_election_batch hpre hs hX hp.1.1 hub fun h hWarp => ?_
    have hN : (X.tr h).length = 5 := by
      have hLim := hLe hWarp
      have hGe := Nat.le_of_not_gt fun he => hShort ⟨h, hWarp, he⟩
      omega
    have hState := TmaElectionTrace.election_at_five hpre hX sound (hw hWarp) hN.ge
    refine ⟨Wg1Tma.init P L h, hPending hWarp, ?_, hN.symm ▸ hState, rfl⟩
    apply PTX.Step.Released.of_get
    intro e he
    rw [hN] at he
    have hGroup : wgOf L h = 1 := by
      have hw := hw hWarp
      unfold wgOf warpOf at *
      omega
    rw [PrologueShuffleTrace.head_event hpre hX sound he hGroup]
    simp [Kind.resume]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

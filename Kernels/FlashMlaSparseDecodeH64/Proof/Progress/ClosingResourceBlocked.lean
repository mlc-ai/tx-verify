-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ResourceRecord
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.CtaClosingTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceExitTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceWaitTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Launch
import Lemmas.Clc.ClcExecution
import Lemmas.Tmem.TmemResourceReady

public section

/-! # A closing deallocation releases or descends to a missing lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A lane waiting for its deallocation leads to an earlier pending state in a maximal trace. -/
theorem pending_deallocation_earlier {g tag : Nat} {dst : Option Loc} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g d)
    (he : X.get (g, (X.tr g).length - 1) =
      some ⟨tag, .tc (.resource .one dst (.dealloc 0 512))⟩) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
  have hX := hmax.1
  have hub := Safety.no_ub hpre hX hs ht
  let i := (X.tr g).length - 1
  have hi : i < (X.tr g).length := PTX.len_of_get he
  have hLen : i + 1 = (X.tr g).length := by dsimp [i]; omega
  obtain ⟨z, _, hz, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hp.1.1).machine ht he
    (by simp)
  have hEmit := ResourceEvents.emits hpre hf rfl
  have hSource : ∃ w, z = .wg0 w ∧ w.site = .exit ∧ warpOf L g = 0 ∧ dst = none := by
    cases hEmit
    case dealloc w hw hWarp _ hDst _ => exact ⟨w, rfl, hw, hWarp, hDst⟩
    all_goals contradiction
  obtain ⟨w, rfl, hSite, hWarp, rfl⟩ := hSource
  have hDone := (CtaClosingTrace.dealloc_at hpre hX hs he hz hSite).2
  rw [hLen] at hDone
  obtain rfl : d = .done := Option.some.inj (Option.some.inj (hp.2.symm.trans hDone))
  by_cases hAll : ∀ h, SameWarp L g h → ∃ j t, X.get (h, j) =
      some ⟨t, .tc (.resource .one none (.dealloc 0 512))⟩
  · let k := ((X.tr g).take i).countP isTcColl
    have hKey : X.TcK (g, i) k := ⟨⟨_, he, rfl⟩, rfl⟩
    have hIssued (h : Nat) (hw : SameWarp L g h) :
        ∃ j, X.get (h, j) = some ⟨tag, .tc (.resource .one none (opAct 0 2).request)⟩ ∧
          X.TcK (h, j) k ∧ opsAt X h j = 2 := by
      obtain ⟨j, t, hj⟩ := hAll h hw
      obtain ⟨hTag, hOrdinal⟩ := TcCollectiveTrace.dealloc_aligned hpre hX hs ht hw he hj
      subst t
      exact ⟨j, hj, (hOrdinal k).mp hKey, ResourceEvents.request_index hpre hX hs ht (by decide) hj⟩
    have hc := resource_covered_of_issued hpre hmax hs ht hp.1.1 hWarp (by decide) hIssued hKey
    have hReady := Tmem.Pair.ReturnReady.ready hX.tmemPair he
      ⟨hc.performed hX.tmemPair, fun _ => hc⟩ nofun
    exact pending_released_earlier hpre hmax hs ht hp ⟨fun _ _ _ _ => hReady⟩
  · push Not at hAll
    obtain ⟨h, hw, hMissing⟩ := hAll
    have hh := hw.1.2.1
    have hSyn := (hs h hh).machine
    have hW : warpOf L h = 0 := (show warpOf L h = warpOf L g from
      by simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2.symm).trans hWarp
    have hGroup : wgOf L h = 0 := by unfold warpOf at hW; unfold wgOf; omega
    have hPend : Frame.Pending L X h := by
      refine ⟨hh, ?_, ?_⟩
      · rintro ⟨_, _, hCan⟩
        obtain ⟨j, sp, tg, _, hIssue, _⟩ := hX.clc.canceled_has_issue hCan
        exact GlobalWrites.no_clc (i := j) (s := sp) (tg := tg) hX hIssue
      · intro t hLast
        rw [List.getLast?_eq_getElem?] at hLast
        obtain ⟨j, _, t', he'⟩ :=
          ResourceEvents.dealloc_before_exit hpre hX hSyn ht hW hLast rfl
        exact hMissing j t' he'
    obtain ⟨q, hQ⟩ := pending_followed hpre hX hs ht hPend
    have hCta : completionTime P L h = completionTime P L g := by
      simp only [completionTime, ctaidY, ctaOf, hw.1.2.2]
    refine ⟨h, q, ⟨hPend, hQ⟩, ?_⟩
    rcases Wg0.state_of_wg hGroup (hSyn.produces (hX.thr h hh)) hQ with
      ⟨s, rfl⟩ | ⟨a, rfl⟩ | rfl
    · simp only [priority, completionTime, blockTime]
      omega
    · by_cases hExit : a.site = .exit
      · simp [priority, softmaxTime, hExit, hCta]
      · obtain ⟨_, hRun⟩ := Frame.run_some hX hub hPend
        obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.end_at hs hh hRun hQ
        have hLe := before_closing_priority hInv hExit
        refine lt_of_le_of_lt hLe ?_
        simp [priority, hCta]
    · obtain ⟨j, _, t, hD⟩ :=
        ResourceEvents.dealloc_before_done hpre hX hSyn hh hW le_rfl hQ
      exact (hMissing j t hD).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

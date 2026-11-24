-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ResourceRecord
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressAllocation
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceWaitTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGateRelease
import Lemmas.Clc.ClcExecution
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.CtaBarNamed
import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
import Lemmas.Tmem.TmemResourceReady

public section

/-! # Pending resource requests of the allocation prologue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Tmem.Pair
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem before_prologue_request {g h : Nat} {s q : Site} {n : Nat} (hn : n < 2)
    (hSite : if n = 0 then s = .allocStore ∨ s = .allocRead else s = .barrier)
    (hw : warpOf L h = 0) (hRank : TcPrologueRank.rank L h q ≤ n) :
    priority P L h (.prologue q) < priority P L g (.prologue s) := by
  rcases n with _ | n
  · rcases hSite with rfl | rfl <;> cases q <;>
      simp [TcPrologueRank.rank, TcPrologueRank.setup, hw, priority, prologueRank] at *
    all_goals rename_i j; have := j.isLt; omega
  · obtain rfl : n = 0 := by omega
    have hs : s = .barrier := hSite
    subst s
    cases q <;> simp [TcPrologueRank.rank, TcPrologueRank.setup, hw, priority, prologueRank] at *
    all_goals rename_i j; have := j.isLt; omega

private theorem absent_before_prologue_request {g h n : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hw : SameWarp L g h) (hWarp : warpOf L g = 0)
    (hn : n < 2) (hCount : (X.tr h).countP isTcColl ≤ n) :
    ∃ q, PendingState P L X h (.prologue q) ∧
      warpOf L h = 0 ∧ TcPrologueRank.rank L h q ≤ n := by
  have hh : warpOf L h = 0 := (show warpOf L h = warpOf L g from
    by simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2.symm).trans hWarp
  have sound := (hs h hw.1.2.1).machine
  have hMissing (i tag : Nat) (he : X.IsBarrier (h, i) 0 none tag) : False := by
    have hLen : i < (X.tr h).length := PTX.len_of_get he
    obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_from_trace hX sound ht he (by simp)
    obtain ⟨rfl, _, _⟩ := RingGateEvents.gate_source hf rfl
    have hK := (Wg0TcTrace.prologue_rank_at hpre hX sound hw.1.2.1 hLen.le hd).2
    have hMono := (List.take_sublist i (X.tr h)).countP_le (p := isTcColl)
    rw [hK] at hMono
    simp [TcPrologueRank.rank, TcPrologueRank.setup, hh] at hMono
    omega
  have hp : Frame.Pending L X h := by
    refine ⟨hw.1.2.1, ?_, ?_⟩
    · rintro ⟨_, _, hCanceled⟩
      obtain ⟨i, sp, tg, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
      exact GlobalWrites.no_clc (i := i) (s := sp) (tg := tg) hX hi
    · intro tag hLast
      rw [List.getLast?_eq_getElem?] at hLast
      obtain ⟨j, _, hj, _⟩ := MachineTracking.exit_follows_gate hpre hX
        (fun z hz => (hs z hz).machine) hLast
      exact hMissing j _ hj
  obtain ⟨d, hd⟩ := pending_followed hpre hX hs ht hp
  obtain ⟨q, rfl, _⟩ := MachineTracking.state_before_gate_of_missing hX hp.1 sound hd hMissing
  have hQ := (Wg0TcTrace.prologue_rank_at hpre hX sound hp.1 le_rfl hd).2
  rw [List.take_length] at hQ
  exact ⟨q, ⟨hp, hd⟩, hh, hQ ▸ hCount⟩

/-- A pending allocation or permit relinquishment either releases or has an earlier lane. -/
theorem pending_allocator_earlier {g tag n : Nat} {dst : Option Loc} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g d) (hn : n < 2)
    (he : X.get (g, (X.tr g).length - 1) =
      some ⟨tag, .tc (.resource .one dst (opAct 0 n).request)⟩) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
  have hX := hmax.1
  have hWarp := (ResourceEvents.request_origin hpre hX hs ht he).1
  obtain ⟨hKey, s, hS, hSite⟩ := ResourceEvents.prologue_wait_state hpre hX hs ht hn he
  have hD := Option.some.inj (Option.some.inj (hp.2.symm.trans hS))
  subst d
  by_cases hAll : ∀ h, SameWarp L g h → n < (X.tr h).countP isTcColl
  · have hIssued (h : Nat) (hw : SameWarp L g h) :
        ∃ i, X.get (h, i) = some ⟨tag, .tc (.resource .one dst (opAct 0 n).request)⟩ ∧
          X.TcK (h, i) n ∧ opsAt X h i = n := by
      obtain ⟨i, e, hGet, hColl, hN⟩ := PTX.NamedBar.exists_ordinal isTcColl (X.tr h) (hAll h hw)
      obtain ⟨k, hKind⟩ := PTX.TcCollective.kind_of_coll hColl
      obtain ⟨tag', kd⟩ := e
      change kd = .tc k at hKind
      subst kd
      have hK : X.TcK (h, i) n := ⟨⟨_, hGet, hColl⟩, hN⟩
      obtain ⟨hTag, hSame⟩ := TcCollectiveTrace.agree (f := (h, i)) hpre hX hs ht hw he hGet hKey hK
      subst tag'
      have hEq : k = .resource .one dst (opAct 0 n).request := by
        cases k <;> first | exact hSame.symm | cases hSame
      subst k
      exact ⟨i, hGet, hK, ResourceEvents.request_index hpre hX hs ht (by omega) hGet⟩
    have hCovered := resource_covered_of_issued hpre hmax hs ht hp.1.1 hWarp
      (by omega) hIssued hKey
    have hPubl : ∀ c, (opAct 0 n).request = .alloc c → PTX.laneOf L g ≠ 0 →
        ∃ store obj, AllocResult L X store (g, (X.tr g).length - 1) obj := by
      intro c hc _
      have hZero : n = 0 := by interval_cases n <;> first | rfl | contradiction
      subst n
      have hSafe := Safety.no_resourceUnsafe hpre hX hs ht
      rcases PrologueAllocation.result_or_representative hpre hX hs ht hSafe he hCovered with
        hResult | ⟨leader, hPend, hRel, hAt⟩
      · exact hResult
      · exact (hmax.not_grows (PrologueAllocation.alloc_store_extension hpre hX hs
          (Safety.no_ub hpre hX hs ht) hSafe hPend hRel hAt
          (PrologueAllocation.alloc_store_predecessor hpre hX hs hAt))).elim
    have hReady := Tmem.Pair.ReturnReady.ready hX.tmemPair he
        ⟨hCovered.performed hX.tmemPair, fun _ => hCovered⟩ hPubl
    exact pending_released_earlier hpre hmax hs ht hp ⟨fun _ _ _ _ => hReady⟩
  · push Not at hAll
    obtain ⟨h, hw, hCount⟩ := hAll
    obtain ⟨q, hPending, hh, hRank⟩ :=
      absent_before_prologue_request hpre hX hs ht hw hWarp hn hCount
    exact ⟨h, .prologue q, hPending, before_prologue_request hn hSite hh hRank⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

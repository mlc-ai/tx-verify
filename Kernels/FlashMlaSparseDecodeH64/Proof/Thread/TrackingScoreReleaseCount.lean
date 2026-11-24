-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGemmPublishers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace

@[expose] public section

/-! # The probability release follows the QK wait of its own slot use -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof Protocol.GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Even after numerical dismissal, the concrete probability publication has acquired its
own and all earlier QK uses of the slot. -/
theorem qk_successes_before_actual_score {g i cta : Nat} {slot : Fin 2} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (Object.soReady.loc L cta slot) 0 1 true .cta) :
    arrivals (Object.soReady.loc L cta slot) ((X.tr g).take i) + 1 ≤
      Flow.okPolls (Object.qkDone.loc L cta slot) ((X.tr g).take i) := by
  obtain ⟨hc, _, _, _, _, hPublisher⟩ := actual_gemm_arrival hpre hX hs he hk
  rcases hPublisher with ⟨h, _⟩ | ⟨_, hWg, hTag, start, hLe, initial, hSite, hFirst, hAnchor⟩
  · cases h
  let events := (X.tr g).drop start
  let k := i - start
  let score := Object.soReady.loc L cta slot
  let qk := Object.qkDone.loc L cta slot
  have hGet : events[k]? = some e := by
    change ((X.tr g).drop start)[i - start]? = _
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact he
  have hMem := List.mem_of_getElem? hGet
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hAnchor
    (List.ne_nil_of_mem hMem)
  have hAt := softmax_mask_entry_facts hSite (show (Wg0.code P L g).AtD initial t from hGood.1)
  have hBlock : initial.block < Wg0.blocksOf P L g :=
    (show Wg0.Inv P L g initial from hGood.2).blockLt
  have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
    have h := (Wg0.blocksOf_word_bounds hpre (Wg1Mma.batchOf_lt hpre hg)).2
    omega
  have hShort : k < events.length := (List.getElem?_eq_some_iff.mp hGet).1
  have hSplit : events = events.take k ++ e :: events.drop (k + 1) := by
    have hDrop := List.drop_eq_getElem_cons hShort
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
    rw [← hDrop]
    exact (List.take_append_drop ..).symm
  change Run kernel Assumptions.all L g t events o at hRun
  rw [hSplit] at hRun
  obtain ⟨hQk, hScore, hEvent⟩ :=
    softmax_probability_history_in_trace slot hpre hBlock hTotal hAt hTag hRun
  rw [hFirst, hc] at hQk hScore hEvent
  have hSlot : slot.val = ((events.take k).countP isProbabilityPublication) % 2 := by
    have hLoc := (Kind.arrive.inj (hk.symm.trans hEvent)).1
    have hAddr := congrArg Loc.addr hLoc
    change L.sharedBase + (222920 + 8 * slot.val) =
      L.sharedBase + (222920 + 8 * ((0 + (events.take k).countP isProbabilityPublication) % 2))
      at hAddr
    omega
  have hSelected :
      (events.take k).countP (successfulQkPoll qk) =
        (events.take k).countP (scorePublishedTo score) + 1 := by
    change (events.take k).countP (successfulQkPoll qk) = _ at hQk
    change (events.take k).countP (scorePublishedTo score) = _ at hScore
    have := slot.isLt
    omega
  have hArrivals :
      (events.take k).countP (arrivesOn score) =
        (events.take k).countP (scorePublishedTo score) := by
    apply List.countP_congr
    intro f hf
    constructor
    · intro hArrives
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hf)
      have hF : X.get (g, start + j) = some f := by
        change (X.tr g)[start + j]? = _
        simpa only [events, List.getElem?_drop] using hj
      have getArrival : ∃ tx count rel scope, f.kind = .arrive score tx count rel scope := by
        unfold arrivesOn sourceArrive at hArrives
        split at hArrives
        · rename_i loc tx count rel scope hKind
          exact ⟨tx, count, rel, scope, of_decide_eq_true hArrives ▸ hKind⟩
        · cases hArrives
      obtain ⟨tx, count, rel, scope, hKind⟩ := getArrival
      obtain ⟨_, _, _, _, _, hActual⟩ := actual_gemm_arrival hpre hX hs hF hKind
      rcases hActual with ⟨h, _⟩ | ⟨_, _, hTag, _⟩
      · cases h
      · simp [scorePublishedTo, isProbabilityPublication, hTag, hArrives]
    · intro h
      exact (Bool.and_eq_true_iff.mp h).2
  have hEmpty := Wg0GemmTrace.score_arrivals_of_state hpre slot
    ((hs g hg).machine.produces (hX.thr g hg)) hAnchor
  rw [hc] at hEmpty
  simp [Wg0GemmTrace.publishedBlocks, hSite, hFirst, Wg0.Site.inEpilogue] at hEmpty
  have hZero : arrivals score ((X.tr g).take start) = 0 := by
    change arrivals score ((X.tr g).take start) = _ at hEmpty
    have := slot.isLt
    omega
  have hTake : (X.tr g).take i = (X.tr g).take start ++ events.take k := by
    dsimp only [events, k]
    rw [← List.take_add, Nat.add_sub_of_le hLe]
  have hQkIncl :
      (events.take k).countP (successfulQkPoll qk) ≤ (events.take k).countP (okPoll qk) :=
    List.countP_mono_left (fun f _ h => (Bool.and_eq_true_iff.mp h).2)
  change arrivals score ((X.tr g).take i) + 1 ≤ Flow.okPolls qk ((X.tr g).take i)
  rw [hTake, arrivals, Flow.okPolls, List.countP_append, List.countP_append]
  change ((X.tr g).take start).countP (arrivesOn score) = 0 at hZero
  rw [hZero, Nat.zero_add, hArrivals, ← hSelected]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

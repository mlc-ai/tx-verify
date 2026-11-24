-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing
import Lemmas.Protocol.GatedFaults

@[expose] public section

/-! # GEMM handoff records are gated by the preceding successful polls -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow MBarrier Protocol.GemmRing PTX.MbarRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable {cta : Nat} {slot : Fin 2} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
include hpre hX hs

/-- All records of the score-ready object are fault-free, including its arrivals. -/
theorem score_ready_fault_free (ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (Object.soReady.loc L cta slot), r.fault = none := by
  obtain ⟨issuer, hU⟩ := exists_issuer (cta := cta) hpre hX hs
  let R := scoreRing (slot := slot) hpre hX hs ht hU
  apply (score_obj hpre hX hs ht (cta := cta) (slot := slot)).fault_free hX
  refine Unit.gated_of_paths (A := Assumptions.all) fun {lane i tag sc} he hpos => ?_
  let u := PTX.Flow.arrivals (Object.soReady.loc L cta slot) ((X.tr (softmax L cta lane)).take i)
  have hg (j : Nat) (hj : j ≤ u) := guard_score_arrival hpre hX hs ht he hj
  obtain ⟨_, hPath⟩ := R.reach_consumer_op hX.depAcyclic 0 (b := lane) (t := u) hg hpos le_rfl
  change Relation.TransGen (DepStep L kernel X)
    (.thread (issuer, Poll.nth X (Object.soReady.loc L cta slot) issuer (u - 1)), true)
    (.thread (softmax L cta lane, i), false) at hPath
  exact ⟨issuer, by simpa only [Nat.add_zero] using hPath⟩

/-- All records of the QK-done object are fault-free, including its notifications. -/
theorem qk_done_fault_free (ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (qk L cta slot), r.fault = none := by
  obtain ⟨issuer, hU⟩ := exists_issuer (cta := cta) hpre hX hs
  let R := scoreRing (slot := slot) hpre hX hs ht hU
  apply (qk_obj (slot := slot) hpre hX hs ht hU).fault_free hX
  refine Notify.gated_of_paths (A := Assumptions.all) fun {i tag sp rank} he _ htgt hrec hpos => ?_
  have hg (n : Nat) (h1 : 1 ≤ n)
      (hn : n ≤ ((X.tr issuer).take i).countP (commitsTo (qk L cta slot))) :=
    guard_qk_issue hpre hX hs ht he htgt h1 hn
  let u := ((X.tr issuer).take i).countP (commitsTo (qk L cta slot))
  have hj : u - 1 < u := Nat.sub_lt hpos (by decide)
  obtain ⟨_, hPath⟩ := R.reach_op hX.depAcyclic (a := 0) (s := u) hg 0 hj
  change Relation.TransGen (DepStep L kernel X)
    (.thread (softmax L cta 0, Poll.nth X (qk L cta slot) (softmax L cta 0) (u - 1)), true)
    (.thread (issuer, i), false) at hPath
  obtain ⟨r, hr, hid⟩ := hrec
  have hp := object_record_present hX.tma hr
  rw [hid] at hp
  exact ⟨softmax L cta 0, by
    simpa only [Nat.add_zero] using
      hPath.tail (show DepStep L kernel X (.thread (issuer, i), false)
          (.async (issuer, i) (.tcNotify rank), false) from
        .inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hp, trivial⟩))⟩

/-- All records of the dequant-ready object are fault-free, including its arrivals. -/
theorem dequant_ready_fault_free (_ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (Object.dequantReady.loc L cta slot), r.fault = none := by
  obtain ⟨issuer, hU⟩ := exists_issuer (cta := cta) hpre hX hs
  let R := dequantRing (slot := slot) hpre hX hs hU
  apply (dequant_obj hpre hX hs (cta := cta) (slot := slot)).fault_free hX
  refine Unit.gated_of_paths (A := Assumptions.all) fun {lane i tag sc} he hpos => ?_
  let u := PTX.Flow.arrivals (full L cta slot) ((X.tr (producer L cta lane)).take i)
  have hg (j : Nat) (_ : 1 ≤ j) (hj : j ≤ u) := guard_ready_arrival hpre hX hs he hj
  have hj : u - 1 < u := Nat.sub_lt hpos (by decide)
  obtain ⟨_, hPath⟩ := R.reach_op hX.depAcyclic (a := lane) (s := u) hg 0 hj
  change Relation.TransGen (DepStep L kernel X)
    (.thread (issuer, Poll.nth X (full L cta slot) issuer (u - 1)), true)
    (.thread (producer L cta lane, i), false) at hPath
  exact ⟨issuer, by simpa only [Nat.add_zero] using hPath⟩

/-- All records of the PV-done object are fault-free. Only WG2's reuse waits gate arrivals. -/
theorem sv_done_fault_free (_ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (Object.svDone.loc L cta slot), r.fault = none := by
  obtain ⟨issuer, hU⟩ := exists_issuer (cta := cta) hpre hX hs
  let R := dequantRing (slot := slot) hpre hX hs hU
  apply (reuse_obj (slot := slot) hpre hX hs hU).fault_free_selected hX
  refine Notify.selected_gated_of_paths (A := Assumptions.all)
    fun {i tag sp rank} he _ htgt hrec hpos => ?_
  let u := ((X.tr issuer).take i).countP (commitsTo (Object.svDone.loc L cta slot))
  have hg (j : Nat) (hj : j ≤ u) := guard_pv_issue hpre hX hs he htgt hj
  obtain ⟨_, hPath⟩ := R.reach_consumer_op hX.depAcyclic 0 (b := 0) (t := u) hg hpos le_rfl
  change Relation.TransGen (DepStep L kernel X)
    (.thread (producer L cta 0,
      Poll.nth X (Object.svDone.loc L cta slot) (producer L cta 0) u), true)
    (.thread (issuer, i), false) at hPath
  obtain ⟨r, hr, hid⟩ := hrec
  have hp := object_record_present hX.tma hr
  rw [hid] at hp
  have hcount : u - 1 + 1 = u := by omega
  refine ⟨producer L cta 0, producer_wg2 hpre cta 0, ?_⟩
  change Relation.TransGen (DepStep L kernel X)
    (.thread (producer L cta 0, Poll.nth X (Object.svDone.loc L cta slot) (producer L cta 0)
      (u - 1 + 1)), true) (.async (issuer, i) (.tcNotify rank), false)
  rw [hcount]
  exact hPath.tail (.inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, ⟨_, he⟩, hp, trivial⟩))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

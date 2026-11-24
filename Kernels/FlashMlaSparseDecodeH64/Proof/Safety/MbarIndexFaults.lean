-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.CtaRings
import Lemmas.Protocol.GatedFaults

@[expose] public section

/-! # Index publications and releases cannot overrun their barrier generations -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow PTX.MbarRing Protocol IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem ready_gated {cta : Nat} {slot : Fin 4} {lane : Fin 32}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : Unit.Ring L kernel Assumptions.all X (IndexRing.ready L cta slot)
      (IndexRing.free L cta slot) 32 129 (producerThread L cta) (consumerThread L cta lane)) :
    Unit.Gated L kernel Assumptions.all X (IndexRing.ready L cta slot) 32
      (producerThread L cta) 0 := by
  refine Unit.gated_of_paths (A := Assumptions.all) fun {a i tag sc} he hPos => ?_
  let n := arrivals (IndexRing.ready L cta slot) ((X.tr (producerThread L cta a)).take i)
  have hGate := R.gateP he
  have hg (k : Nat) (_ : 1 ≤ k) (hk : k ≤ n) :
      Resumes kernel X ((R.items hX).wE a k) (producerThread L cta a, i) := by
    exact Poll.guard R.spins (PTX.len_of_get he) (by omega)
  obtain ⟨_, hPath⟩ := (R.items hX).reach_op hX.depAcyclic hg 0
    (j := n - 1) (by omega)
  exact ⟨consumerThread L cta lane 0, by
    change Relation.TransGen (DepStep L kernel X)
      (.thread (consumerThread L cta lane 0,
        Poll.nth X (IndexRing.ready L cta slot) (consumerThread L cta lane 0) (n - 1 + 0)), true)
      _
    exact hPath⟩

private theorem free_gated {cta : Nat} {slot : Fin 4} {lane : Fin 32}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (R : Unit.Ring L kernel Assumptions.all X (IndexRing.ready L cta slot)
      (IndexRing.free L cta slot) 32 129 (producerThread L cta) (consumerThread L cta lane)) :
    Unit.Gated L kernel Assumptions.all X (IndexRing.free L cta slot) 129
      (consumerThread L cta lane) 1 := by
  refine Unit.gated_of_paths (A := Assumptions.all) fun {b i tag sc} he hPos => ?_
  let n := arrivals (IndexRing.free L cta slot) ((X.tr (consumerThread L cta lane b)).take i)
  have hGate := R.gateC he
  have hg (k : Nat) (hk : k ≤ n) :
      Resumes kernel X ((R.items hX).wF b k) (consumerThread L cta lane b, i) := by
    exact Poll.guard R.spins (PTX.len_of_get he) (by omega)
  obtain ⟨_, hPath⟩ := (R.items hX).reach_consumer_op hX.depAcyclic 0 hg
    (n := n) hPos le_rfl
  have hIndex : n - 1 + 1 = n := by omega
  exact ⟨producerThread L cta 0, by
    change Relation.TransGen (DepStep L kernel X)
      (.thread (producerThread L cta 0,
        Poll.nth X (IndexRing.free L cta slot) (producerThread L cta 0) (n - 1 + 1)), true)
      _
    rwa [hIndex]⟩

/-- Every index-ready record is clean. The arrival's gate is derived from the actual
issuing lane, including when its record is still potentially faulting. -/
theorem index_ready_fault_free {cta : Nat} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcta : cta < L.grid) (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (IndexRing.ready L cta slot), r.fault = none := by
  let R := (ctaRings hpre hX hcta hs ht).index slot
  exact R.F.fault_free hX (ready_gated hX R)

/-- Every index-free record is clean. Its earlier ready poll forces the matching index
producer's free poll before the new release, ruling out a generation overrun. -/
theorem index_free_fault_free {cta : Nat} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcta : cta < L.grid) (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (IndexRing.free L cta slot), r.fault = none := by
  let R := (ctaRings hpre hX hcta hs ht).index slot
  exact R.E.fault_free hX (free_gated hX R)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

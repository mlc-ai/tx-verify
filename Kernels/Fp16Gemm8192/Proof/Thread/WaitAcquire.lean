-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Flow.WaitAcquire
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # The kernel's polls acquire and its arrivals release

Every `mbarrier.try_wait` of the kernel is a CTA-scope acquire poll and every
`mbarrier.arrive` a CTA-scope release arrival (decided on the code); under the cluster-scope
assumption their events are cluster-scope acquire waits and release arrivals. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The kernel's polls are CTA-scope acquire polls and its arrivals CTA-scope release arrivals
(decided on the code). -/
theorem kernel_sync_flags :
    kernel.code.all (fun ins => match ins.op with
      | .mbarWait _ _ _ _ a sc => a && sc == .cta
      | .mbarArrive _ _ _ _ _ r sc _ => r && sc == .cta
      | _ => true) = true := by
  decide +kernel

/-- A poll of a thread followed by its machine is a cluster-scope acquire poll, and an arrival
a cluster-scope release arrival. -/
theorem sync_flags {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) = some (some d)) :
    (∀ m p ok acq sc, e.kind = .wait m p ok acq sc → acq = true ∧ sc = .cluster) ∧
    (∀ m tx c rel sc, e.kind = .arrive m tx c rel sc → rel = true ∧ sc = .cluster) := by
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, ht, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hfo
  have h := List.all_eq_true.mp kernel_sync_flags ins (List.mem_of_getElem? hc)
  rw [← ht.1] at hc
  refine ⟨fun m p ok acq sc hk => ?_, fun m tx c rel sc hk => ?_⟩
  · obtain ⟨p', b, off, par, sc0, hop, hw⟩ := fires_wait_flags hfire hk
    rw [hop] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, hw (prod_scope_at hc (by rw [hop]; rfl)) h.1 h.2⟩
  · obtain ⟨b, off, tx', c', cl, sc0, st, hop, hw⟩ := fires_arrive_flags hfire hk
    rw [hop] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, hw (prod_scope_at hc (by rw [hop]; rfl)) h.1 h.2⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof

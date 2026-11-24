-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.CtaRings
import Lemmas.Protocol.GatedFaults

@[expose] public section

/-! # Fault-free releases of the raw gather slots -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow PTX.MbarRing Protocol RawRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every raw-free record is clean. Each release is guarded by the actual preceding ready
polls, even if the release's own record has yet to be shown successful. -/
theorem raw_free_fault_free {cta : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (free L cta slot), r.fault = none := by
  obtain ⟨lane, _, hIssuer⟩ := selected_tma (cta := cta) hpre hX hs
  let g := cta * L.block + 160 + lane.val
  let R := items (slot := slot) g hpre hX hs ht hIssuer
  apply (free_obj hpre hX hs ht (cta := cta) (slot := slot)).fault_free hX
  refine Unit.gated_of_paths (A := Assumptions.all) fun {b i tag sc} he hPos => ?_
  let n := arrivals (free L cta slot) ((X.tr (consumer L cta b)).take i)
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hc, d, hb, hd, hState⟩ :=
    release_source hpre hX (hs _ hg) ht he rfl
  obtain ⟨ha, hp⟩ := Wg2RawTrace.composed_raw_free_counts hpre
    ((hs _ hg).produces (hX.thr _ hg)) hState hd
  rw [hc, hb] at ha hp
  change n = d.block / 2 at ha
  change okPolls (ready L cta slot) ((X.tr (consumer L cta b)).take i) = d.block / 2 + 1 at hp
  have hguard (j : Nat) (hj : j ≤ n) :
      Resumes kernel X (R.wF b j) (consumer L cta b, i) :=
    Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw) (PTX.len_of_get he)
      (by omega)
  obtain ⟨_, hPath⟩ := R.reach_consumer_op hX.depAcyclic 0 hguard (n := n) hPos le_rfl
  exact ⟨g, by
    change Relation.TransGen (DepStep L kernel X)
      (.thread (g, Poll.nth X (free L cta slot) g (n - 1 + 1)), true) _
    rw [show n - 1 + 1 = n by omega]
    exact hPath⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterCount
public import Kernels.Fp16Gemm8192.Proof.Thread.AccTiles

@[expose] public section

/-! # The cluster barrier count at a thread's state, and the claimless read of a consumer in its
exit stage

A thread's cluster arrivals at its trace's end are its state's phase (`cl_phase_of`). A consumer
in its exit stage has read a response that claims no CTA, after a successful poll of its CTA's
response barrier (`cons_exit_read`): the exit stage is doomed (`Consumer.D.doomed`), and the
consumer's invariant gives the read. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- A thread's cluster arrivals at the end of its trace are its state's cluster phase. -/
theorem cl_phase_of {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} {d : ThreadD}
    (hg : g < L.threads) (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) :
    clArrives (X.tr g) = d.clPhase := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have h := clusterInv hpre hg htr (X.tr g).length d hσ
  rw [List.take_length] at h
  exact h.1

/-- Every exit-stage site of a consumer is doomed. -/
theorem doomed_of_exitOff {c : Consumer.D} (hx : Consumer.exitOff c ≠ none) : c.doomed := by
  unfold Consumer.exitOff at hx
  unfold Consumer.D.doomed
  cases hs : c.site <;> simp_all

/-- **A consumer in its exit stage has read a response that claims no CTA**, after a successful
poll of its CTA's response barrier (the footprint is the one `AllResponsesAgree` names). -/
theorem cons_exit_read {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} {c : Consumer.D}
    (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))))
    (hx : Consumer.exitOff c ≠ none) :
    ∃ j pc p acq sc pcr, ∃ src : Acc, ∃ bs rr,
      (X.tr g)[j]? = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ ∧
      (X.tr g)[j + 1]? = some ⟨pcr, .rd src bs⟩ ∧
      src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
          false⟩ ∧
      Flow.responseOf bs = some rr ∧ ¬ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have h := consInv hpre hg htr (X.tr g).length (.inr (.cons c)) hσ
  rw [List.take_length] at h
  obtain ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hw, hr, h1, h2, h3, h4⟩ :=
    h.2.2.1 (doomed_of_exitOff hx)
  exact ⟨j, pc, p, acq, sc, pcr, src, bs, rr, hw, hr, ⟨h1, h2⟩, h3, h4⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof

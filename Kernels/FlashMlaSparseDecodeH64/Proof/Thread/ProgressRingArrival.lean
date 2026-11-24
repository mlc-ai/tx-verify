-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

public section

/-! # Publications on the raw, index and dequantization rings -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- The gather and dequantization roles' buffer notification sites. -/
inductive RingArrival : Machine.ThreadD → Prop where
  | rawReady {d : Wg1Tma.D} : d.site = .rawReady → RingArrival (.tma d)
  | coordFree {d : Wg1Tma.D} : d.site = .coordFree → RingArrival (.tma d)
  | dequantReady {d : Wg2.D} : d.site = .ready → RingArrival (.wg2 d)
  | rawFree {d : Wg2.D} : d.site = .free → RingArrival (.wg2 d)

/-- A released lane can append its buffer notification and its checked object action. -/
theorem ring_arrival_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Machine.ThreadD} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hsg : SyncGuarded L kernel X)
    (hnr : ∀ e tag a bs, X.get e = some ⟨tag, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ → a.release = false)
    (hnf : ∀ e sem scope, ¬ X.ThreadFence e sem scope)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : RingArrival d) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hd <;> cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  have hTemplate : ∃ obj bytes, eventTmpl Assumptions.all L g u ins.op =
      .arrive obj bytes (PTX.next u) 1 true .cta := by
    cases hd with
    | rawReady h => exact ⟨_, _, RingEvents.rawReady_template hpre h ha hi hc⟩
    | coordFree h => exact ⟨_, _, RingEvents.validFree_template hpre h ha hi hc⟩
    | dequantReady h => exact ⟨_, _, RingEvents.dequantReady_template hpre h ha hi hc⟩
    | rawFree h => exact ⟨_, _, RingEvents.rawFree_template hpre h ha hi hc⟩
  obtain ⟨_, _, hTmpl⟩ := hTemplate
  rw [hTmpl] at hout
  exact role_arrival_extension hX hord hsg hnr hnrmw hnf hp.1 hn hrel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

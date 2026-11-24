-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Lemmas.Step.TcLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreBytes

public section

/-! # Score, rescale and output Tensor Memory load extensions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow TcMma

/-- Tensor Memory loads issued by the softmax role. -/
inductive SoftmaxLoad : Wg0.Site → Prop where
  | score (arm part : Fin 2) : SoftmaxLoad (.scoreLoad arm part)
  | rescale (tile : Fin 4) : SoftmaxLoad (.rescaleLoad tile)
  | output (tile : Fin 4) : SoftmaxLoad (.oLoad tile)

/-- At all three kinds of Tensor Memory load, a released lane reads the last known whole words. -/
theorem softmax_tmem_load_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hGuard : SyncGuarded L kernel X) (hLayout : LayoutInjective X)
    (hWord : ∀ w cell v, Wrote L Assumptions.all X w cell v → v.bytes = 4)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hRel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : SoftmaxLoad d.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  change kernel.code[d.site.pc]? = some ins at hc
  have hTemplate : ∃ address n k, eventTmpl Assumptions.all L g u ins.op =
      .tcLd address n .s32x32b k := by
    generalize hSite : d.site = s at hd
    cases hd with
    | score arm part =>
      obtain ⟨k, hTmpl⟩ := Wg0.scoreLoad_site_template hpre hSite ha hc
      exact ⟨_, _, k, hTmpl⟩
    | rescale j => exact ⟨_, _, _, Wg0.rescaleLoad_template hpre hSite ha hc⟩
    | output j =>
      rw [hSite] at hc
      obtain rfl := Option.some.inj (hc.symm.trans (Wg0.outputLoad_code j))
      exact ⟨_, _, _, Wg0.event_oLoad hpre ha hSite⟩
  obtain ⟨address, n, k, hTmpl⟩ := hTemplate
  rw [hTmpl] at hout
  let vals := PTX.Step.loadVals L Assumptions.all X g .s32x32b address n
  refine PTX.Step.tc_load_counted_extension hX hp.1 hn hRel hRun hTau
    (vals := vals) (o := some (k vals))
    ⟨_, hout, _, PTX.Step.loadVals_length, rfl, rfl⟩ ?_ ?_
  · intro i v hi hLast
    change (PTX.Step.loadVals L Assumptions.all X g .s32x32b address n).length > i at hi
    rw [PTX.Step.loadVals_length] at hi
    exact ⟨PTX.Step.loadVals_spec hX hGuard hLayout hi hLast, by
      obtain ⟨w, hw, _⟩ := hLast
      exact hWord w _ _ hw⟩
  · exact Interface.all_wf_snoc_of_not_nc hX (fun _ _ h => Kind.noConfusion h)
      (fun h => Kind.noConfusion h)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.TcWaits
public import Kernels.Fp16Gemm8192.Proof.Progress.NextFire
public import Lemmas.Tcgen05.TcLoadSource
public import Lemmas.Step.TcLoad

@[expose] public section

/-! # Progress at a Tensor Memory load and its wait

* A released pending thread whose next event is a Tensor Memory load issues it, each register slot
  returning the value the last write of its cell left (`Step.loadVals`): the kernel's MMA layouts
  are injective, so that value is unique, and it is a single-precision float, a whole word
  (`TmemWords`). A load's wait is issued as is (`tc_load_next_steps`).
* A pending thread whose last event is an unreleased load or wait has not stopped: in a safe
  execution every word a load returned is a single-precision float (`load_word_f32`), so
  the wait's conversions succeed and the thread is at a consumer's state (`ThreadFacts.
  cons_data_next`); a lane of its warp lags behind (`tc_wait_steps`, `tc_data_steps`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every word a Tensor Memory load returns is a single-precision float**, in a safe execution:
the word has a source write (`TcSupported`) and contains its value (`LoadReadOk`). -/
theorem load_word_f32 (hX : Consistent L kernel Prod mem0 X) (hw : TmemWords L X)
    (hsafe : ¬ Unsafe L kernel Prod mem0 X) {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    {v : Value} (hl : X.TLd e a vals sh) (hv : v ∈ vals) : ∃ r, v = .float .f32 r := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨cell, hcell⟩ : ∃ cell, TcMma.LoadCell L X e j cell :=
    ⟨_, a, vals, sh, hl, hj, rfl⟩
  obtain ⟨source, value, hrs, hwr⟩ := sourceSafe_of_safe hsafe .ld e cell ⟨j, hcell⟩
  obtain ⟨word, hword, hc⟩ := hX.tcRead.1 e a vals sh j source cell value hl hcell hrs hwr
  obtain ⟨r, rfl⟩ := hw.2 _ _ _ hwr
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hword
  rw [hword]
  rcases hc with ⟨-, rfl⟩ | ⟨hb, -⟩
  · exact ⟨r, rfl⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb

/-- **A released pending thread at a Tensor Memory load or a load's wait steps.** -/
theorem tc_load_next_steps (ht : ThreadFacts L X) (hw : TmemWords L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .tcLoad)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX (fun h => hsafe (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, n, sh, k, rfl⟩ | ⟨u, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · refine .inl (Step.tc_load_counted_extension hX hg hne hrel hrun hl
      (o := some (k (Step.loadVals L Prod X g sh a n)))
      ⟨_, hout, _, Step.loadVals_length, rfl, rfl⟩ ?_ (prod_wf _))
    intro j v hj hv
    rw [Step.loadVals_length] at hj
    refine ⟨Step.loadVals_spec hX hsg hw.1 hj hv, ?_⟩
    obtain ⟨s, hs, -⟩ := hv
    obtain ⟨r, rfl⟩ := hw.2 _ _ _ hs
    rfl
  · exact .inl (Step.tccoll_counted_extension hX hg (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
      (prod_wf _))

/-- **Progress at an unreleased Tensor Memory data event.** Its thread is at a consumer's state:
the words its loads returned are single-precision floats. A lane of its warp lags behind. -/
theorem tc_data_steps (ht : ThreadFacts L X) (hw : TmemWords L X)
    (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) (hagree : AllResponsesAgree L X)
    (hexit : ClusterExitAll L X) {g : Nat} (hp : Frame.Pending L X g) {e : Event}
    (hlast : X.get (g, (X.tr g).length - 1) = some e) (hd : isTcData e = true)
    (hnr : ¬ Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub : ¬ HasUb X := fun h => hsafe (.inl h)
  have hlen := len_of_get hlast
  simp only at hlen
  obtain ⟨d0, hd0⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub hlast
  obtain ⟨c, hσ⟩ := ht.cons_data_next hg hlast hd hd0
    (fun _ pc a vals sh _ hk v hv => load_word_f32 hX hw hsafe ⟨pc, hk⟩ hv)
  rw [show (X.tr g).length - 1 + 1 = (X.tr g).length by omega] at hσ
  exact tc_wait_steps ht hub hmax hagree hexit hp hσ hlast hd hnr

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress

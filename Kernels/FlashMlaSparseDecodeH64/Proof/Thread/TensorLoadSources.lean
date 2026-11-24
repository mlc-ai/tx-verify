-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawGatherTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Flow.NotTensorPrefetch
import Lemmas.Flow.Final
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast

public section

/-! # The descriptors of actual tensor-load issues -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TensorLoadSources

open PTX PTX.Flow MmaDataTrace

/-- A load uses the fixed query tile or one of the two actual KV gather descriptors. -/
inductive Load (P : Params) (L : Launch) (g : Nat) (s : TensorCopy.Spec) : Prop
  | query (tile : Fin 8) : s = queryTmaSpec P L g tile → Load P L g s
  | main :
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, (encodeKv P.kvBase P.numBlocks P.blockStride P.kvClass).fourRows⟩ → Load P L g s
  | extra : P.extra_topk ≠ 0 →
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, (encodeKv P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass).fourRows⟩ →
    Load P L g s

private theorem query_spec {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i address : Nat} {d : Wg1Mma.D} {tile : Fin 8} {s : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    {e : Event} (he : X.get (g, i) = some e) (hk : e.kind = .tensorIssue address s)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hSite : d.site = .qLoad tile) :
    address = P.param1Base + Wg1Mma.qMapOff ∧ s = queryTmaSpec P L g tile := by
  obtain ⟨t, ins, o, hat, _, hc, hf⟩ := Frame.fired_site hs hX he hd
  obtain ⟨site, block⟩ := d
  change site = _ at hSite
  subst site
  cases o with
  | none =>
    rcases fires_none_ends hf with ⟨_, h⟩ | h <;> rw [hk] at h <;> cases h
  | some u =>
    have h := (MmaDataTrace.fires_qLoad hpre (Frame.lt_of_get hX he) block tile hat hc hf).1
    exact Kind.tensorIssue.inj (hk.symm.trans h)

/-- A real issue has the fixed query map or the TMA role's actual gather state. -/
theorem issue_kind {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i address : Nat} {s : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorIssue (g, i) address s) :
    (∃ tile, address = P.param1Base + Wg1Mma.qMapOff ∧ s = queryTmaSpec P L g tile) ∨
      ∃ d k, Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) ∧ d.site = .issue k := by
  obtain ⟨tag, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  have hSite := RingTensorEvents.issue_site hf rfl
  cases d
  case mma d =>
    obtain ⟨k, h⟩ := hSite
    exact .inl ⟨k, query_spec hpre hX hs he rfl hd h⟩
  case tma d =>
    obtain ⟨k, h⟩ := hSite
    exact .inr ⟨d, k, hd, h⟩
  all_goals exact hSite.elim

/-- Classify the issued load even if its effects are still empty. -/
theorem load {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i address : Nat} {s : TensorCopy.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.TensorIssue (g, i) address s) : Load P L g s := by
  rcases issue_kind hpre hX hs ht hi with ⟨k, _, h⟩ | ⟨d, k, hd, h⟩
  · exact .query k h
  · obtain ⟨_, _, _, _, _, hDesc⟩ := RawGatherTrace.gather_operands
      hpre hs hX hd h hi.choose_spec rfl
    exact hDesc.elim Load.main (fun h => Load.extra h.1 h.2)

set_option maxRecDepth 100000 in
private theorem no_prefetch_instruction : OpPcsFast kernel.code tensorPrefetchOp [] = true := by
  decide +kernel

/-- The descriptor-preload instructions do not issue asynchronous tensor prefetches. -/
theorem no_tensor_prefetch {L : Launch} {mem0 : Mem0} {X : Execution}
    {i : EvId} {address : Nat} {s : TensorPrefetch.Spec}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : X.TensorPrefetchIssue i address s) : False := by
  obtain ⟨tag, he⟩ := hi
  rcases Flow.get_source hX he with ⟨_, h⟩ | ⟨_, _, _, _, hc, hf⟩
  · cases h
  · exact List.not_mem_nil (OpPcsFast.mem no_prefetch_instruction hc
      (fires_tensorPrefetch_op hf rfl))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TensorLoadSources

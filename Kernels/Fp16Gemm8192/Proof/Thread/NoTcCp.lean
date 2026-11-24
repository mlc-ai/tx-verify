-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.NotTcCp
public import Lemmas.Flow.NotTcSt
public import Lemmas.Flow.NotTensorPrefetch

@[expose] public section

/-! # The kernel issues no Tensor Core copy, Tensor Memory store or tensor prefetch

The kernel has no `tcgen05.cp`, no `tcgen05.st` and no `cp.async.bulk.prefetch.tensor`
instruction (decided on the code), so no event of a followed thread is a Tensor Core copy
(`no_tc_cp`), a Tensor Memory store (`no_tc_st`) or a tensor prefetch (`no_tensor_prefetch`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The kernel has no Tensor Core copy instruction. -/
theorem kernel_no_tcCp : OpPcs kernel.code tcCpOp [] = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- No event of a followed thread is a Tensor Core copy. -/
theorem no_tc_cp {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k =
      some (some d)) {s : TcCopy.Spec} :
    e.kind ≠ .tc (.cp s) := by
  intro hk
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hfo
  have := OpPcs.mem kernel_no_tcCp hc (fires_tcCp_op hfire hk)
  simp at this

/-- The kernel has no Tensor Memory store instruction (decided in one pass). -/
theorem kernel_no_tcSt : OpPcsFast kernel.code tcStOp [] = true := by
  decide +kernel

/-- No event of a followed thread is a Tensor Memory store. -/
theorem no_tc_st {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) {a : Nat} {vals : List Value}
    {sh : TcShape} :
    e.kind ≠ .tc (.st a vals sh) := by
  intro hk
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hfo
  have := OpPcsFast.mem kernel_no_tcSt hc (fires_tcSt_op hfire hk)
  simp at this

/-- The kernel has no tensor prefetch instruction (decided in one pass). -/
theorem kernel_no_tensorPrefetch : OpPcsFast kernel.code tensorPrefetchOp [] = true := by
  decide +kernel

/-- No event of a followed thread is a tensor prefetch. -/
theorem no_tensor_prefetch {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) {a : Nat} {s : TensorPrefetch.Spec} :
    e.kind ≠ .tensorPrefetch a s := by
  intro hk
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, hc, hfire⟩ := Code.fired_site (sound hpre hg) hfo
  have := OpPcsFast.mem kernel_no_tensorPrefetch hc (fires_tensorPrefetch_op hfire hk)
  simp at this

end

end PTX.Kernels.Fp16Gemm8192.Proof

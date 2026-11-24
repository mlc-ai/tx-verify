-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace

@[expose] public section

/-! # The query copy and the first dequantized write to its shared address -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GemmReuseEndpoints

open PTX PTX.Flow

/-- A query-copy site issues its matching operation on the shared query tile. -/
theorem query_copy {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : Wg1Mma.D} {e : Event} {u : TState} {k : Fin 16}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hd : d.site = .qCopy k)
    (hf : (Machine.machine P L g).Fired (some (.mma d)) e (some u)) :
    e.kind = .tc (.cp (MmaDataTrace.queryCopySpec L g k)) := by
  obtain ⟨t, ⟨ha, _⟩, hf⟩ := hf
  change (Wg1Mma.code P L g).AtD d t at ha
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e (some u) at hf
  have hp : t.pc = d.site.pc := ha.1
  rw [hp, hd] at hf
  have heq : d = ⟨.qCopy k, d.i⟩ := by cases d; simp_all
  rw [heq] at ha
  cases hc : kernel.code[(Wg1Mma.Site.qCopy k).pc]? with
  | none =>
    rw [hc] at hf
    cases hf.2
  | some ins =>
    rw [hc] at hf
    exact (MmaDataTrace.fires_qCopy hpre hg d.i k ha hc hf).1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GemmReuseEndpoints

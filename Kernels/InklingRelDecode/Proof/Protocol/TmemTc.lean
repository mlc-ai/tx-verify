-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.TmemAlloc

@[expose] public section

/-!
# The MMA instruction and read-source branches of `Unsafe`

`Safety.Protocol.tcInstr` (`TcMma.InstructionUnsafe`) and `tcSource` (`TcMma.SourceUnsafe`), from
the premises each branch is made of. The statements are the fields' exactly; the premises are the
named conjuncts, each a row of the development notes ("Protocol `Tmem`"):

* `tcInstr`: every MMA of the kernel has the issue shape its site's template checks
  (`TcMma.IssueShape`: the `kind::f16` descriptors of the QK and PV MMAs, the 128-byte swizzled
  shared descriptors, the Tensor Memory columns of `SOTmemCols`, zero lane masks;
  `Ring.Kv.qkDesc_valid` and `pvDesc_valid` are its decoded-descriptor part), the completed MMAs'
  unmasked results have
  derived values (`TcMma.CompletedValues`, the `idealArith` rule of `kind::f16`: the result layer's
  `MmaPremises`), the kernel issues no `tcgen05.cp`, and no MMA reuses a collector buffer (the
  kernel's MMAs name no `.collector` qualifier);
* `tcSource`: every load register, accumulator cell and Tensor Memory A byte of a completed MMA
  has a read source with a value (`TcMma.sourceSafe_iff`): the stores and MMA writes of the S, P and
  O cells, ordered by the handshakes of `SOHandoff`, `SOTmemOrder`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX PTX.Proof TcMma

noncomputable section

variable {L : Launch} {A : List Assumption} {X : Execution}

/-- **`Safety.Protocol.tcInstr`.** -/
theorem no_instruction_unsafe
    (hmma : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → IssueShape L i d s mask ∧ CompletedValues L A X i)
    (hcp : ∀ i c, ¬ X.CpIssue i c)
    (hcol : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → s.collector.a.reuses = false ∧ s.collector.b.reuses = false) :
    ¬ InstructionUnsafe L A X := fun hn =>
  hn ⟨fun _ _ _ _ _ hi => hmma hi, fun _ _ hc => absurd hc (hcp _ _),
    collectorSafe_of_noReuse fun _ _ _ _ _ hi => hcol hi⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Tmem1

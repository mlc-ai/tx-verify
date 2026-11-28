-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Run
public import Kernels.InklingRelDecode.Gen.SoftmaxExp
public import Kernels.InklingRelDecode.Gen.SoftmaxPk
import Kernels.InklingRelDecode.Proof.Softmax.GenRulesE

@[expose] public section

/-! # The runs of the exponent window and of the probability pack as steps of a register file

The generated runs of pcs 1847 to 1912 (the maximum used and the 64 shifted scores), 2089 to 2233
(the exponentials, the packs of pairs and the row sum), 949 to 998 and 1000 to 1007 (the pack to
`bf16` pairs), as `RunData` (`Data/W1Run.lean`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section

def runE1 : RunData := ⟨1847, 66, Gen.ex1_facts0, Gen.ex1_facts3, Gen.ex1_cond, Gen.ex1_run⟩
def runE2 : RunData := ⟨2089, 145, Gen.ex2_facts0, Gen.ex2_facts5, Gen.ex2_cond, Gen.ex2_run⟩
def runK1 : RunData := ⟨951, 48, Gen.pk1_facts0, Gen.pk1_facts2, Gen.pk1_cond, Gen.pk1_run⟩
def runK2 : RunData := ⟨1000, 8, Gen.pk2_facts0, Gen.pk2_facts1, Gen.pk2_cond, Gen.pk2_run⟩

private theorem free_ex (s n : Nat) (h : ∀ i < n, exPc (s + i) = true) :
    ∀ i < n, Assumption.SegFreePc Assumptions.all (s + i) := fun i hi => exSegFree (h i hi)

theorem runE1_ok : runE1.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_ex 1847 66 (fun i hi => by simp only [exPc, decide_eq_true_eq]; omega)⟩
theorem runE2_ok : runE2.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_ex 2089 145 (fun i hi => by simp only [exPc, decide_eq_true_eq]; omega)⟩
theorem runK1_ok : runK1.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_ex 951 48 (fun i hi => by simp only [exPc, decide_eq_true_eq]; omega)⟩
theorem runK2_ok : runK2.Ok := ⟨fun _ => rfl, fun _ => rfl, by decide +kernel, by decide +kernel,
  free_ex 1000 8 (fun i hi => by simp only [exPc, decide_eq_true_eq]; omega)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

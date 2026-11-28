-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.NotTensor
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.TensorIssueCopy
public import Lemmas.Flow.TensorRoute
public import Lemmas.Tensor.TensorMulticast
public import Lemmas.Tensor.TensorDescriptor
public import Lemmas.Tensor.TensorTile
public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # The tensor loads of the code: unicast, routed, with a valid nonempty descriptor

Every tensor load of the kernel is unicast (a static scan of the decoded code), so it is routed
from its issuing CTA and goes through a map of a valid descriptor whose transfer box is valid and
nonempty (`tensorLoadForm`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow TensorDescriptor

noncomputable section

/-- The four-row form of a valid descriptor is valid. -/
theorem valid_fourRows {o : Nat} {d : Descriptor o} (h : Valid d) : Valid d.fourRows := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, h8, h9, ?_⟩
  · intro i
    simp only [Descriptor.fourRows]
    split_ifs
    · omega
    · exact h5 i
  · intro i
    simp only [Descriptor.fourRows]
    split_ifs
    · omega
    · exact h6 i
  · simpa [Descriptor.fourRows] using h7
  · simpa [Descriptor.fourRows] using h10

/-- A valid descriptor has a nonempty box. -/
theorem bytes_pos {o : Nat} {d : Descriptor o} (h : Valid d) : 0 < TensorTransfer.bytes d := by
  have hstep := effective_step_pos h
  obtain ⟨-, -, -, -, hbox, -⟩ := h
  have count_pos (axis : Fin (o + 1)) : 0 < TensorTile.count d.box axis := by
    apply (TensorTile.index_lt_count_iff d.box axis (hstep axis) 0).mpr
    simpa only [Nat.zero_mul] using (hbox axis).1
  have h0 := count_pos 0
  have h1 := TensorTile.rows_pos count_pos
  have hb := format_bytes_pos d.format
  exact Nat.mul_pos (Nat.mul_pos h0 h1) hb

/-- The transfer descriptor of a mode of a valid descriptor is valid. -/
theorem valid_transfer {o : Nat} {d : Descriptor o} (lm : TensorMode) (h : Valid d) :
    Valid (lm.transfer d) := by
  cases lm
  · exact h
  · exact valid_fourRows h

private def multicastLoad : Op → Bool
  | .cpTensor _ _ _ _ _ _ _ _ (some _) _ _ => true
  | _ => false

private theorem noMulticastCode :
    kernel.code.all (fun i => !multicastLoad i.op) = true := by
  decide +kernel

private theorem unicastRoute {A : List Assumption} {l : Launch}
    {g pc dst mb addr : Nat} {t : TState} {ca group : Bool} {off mbarOff : Int}
    {map : Opnd} {coord : List Opnd} {mode : TensorMode} {policy : Option Opnd}
    {sp : TensorCopy.Spec} {o : Option TState}
    (hf : Fires pc (eventTmpl A l g t
        (.cpTensor ca group dst off map coord mb mbarOff none mode policy))
      ⟨pc, .tensorIssue addr sp⟩ o) :
    TensorCopy.RoutingOk l (g / l.block) sp ∧ Valid sp.descriptor := by
  have hcopy := fires_cpTensor_copy hf rfl
  obtain ⟨-, -, d, -, hv, hdesc, -⟩ := tensorLoadCopy_ok hcopy
  refine ⟨?_, hdesc ▸ valid_transfer mode hv⟩
  change Fires pc (tensorTmpl l g t
    (.cpTensor ca group dst off map coord mb mbarOff none mode policy)) _ _ at hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure] at hf
  rcases hp : cachePolicyRead l g t policy with fault | success
  · simp [hp, Fires] at hf
  rcases hc : tensorLoadCopy l g t ca group dst off map coord mb mbarOff mode with fault | ⟨a, s⟩
  · simp [hp, hc, Fires] at hf
  by_cases hr : TensorRoute l (g / l.block) s.clusterAddress s.group s.sharedBase s.mbar
  · simp [hp, hc, hr, Fires] at hf
    obtain ⟨⟨_, hSpec⟩, _⟩ := hf
    rw [hSpec]
    exact hr
  · simp [hp, hc, hr, Fires, throw, throwThe, MonadExceptOf.throw] at hf

/-- **Every tensor load is routed, with a valid nonempty descriptor.** -/
theorem tensorLoadForm {A : List Assumption} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {addr : Nat} {s : TensorCopy.Spec}
    (hTensor : X.TensorIssue i addr s) :
    TensorCopy.RoutingOk l (i.1 / l.block) s ∧ Valid s.descriptor ∧
      0 < TensorTransfer.bytes s.descriptor := by
  obtain ⟨pc, he⟩ := hTensor
  rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hu
  have hClass : tensorOp ins.op = true := by
    cases h : tensorOp ins.op
    · exact (fires_notTensor (eventTmpl_notTensor h) hf addr s rfl).elim
    · rfl
  have hn := List.all_eq_true.mp noMulticastCode ins (List.mem_of_getElem? hCode)
  cases hOp : ins.op <;> simp only [hOp, tensorOp, Bool.false_eq_true] at hClass
  rename_i ca group dst off map coord mb moff mask mode policy
  cases mask with
  | none =>
    rw [hOp] at hf
    obtain ⟨hr, hv⟩ := unicastRoute hf
    exact ⟨hr, hv, bytes_pos hv⟩
  | some mask => simp [hOp, multicastLoad] at hn

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

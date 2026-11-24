-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Lemmas.Flow.NotProxyFence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof

noncomputable section

private def plainSharedProxyFence : Op → Bool
  | .fence (.proxy (.async (some (.shared .cta))) none none) => true
  | op => !proxyFenceOp op

private theorem plainSharedProxyFenceCode :
    Decoded.kernel.code.all (fun i => plainSharedProxyFence i.op) = true := by
  decide +kernel

/-- The kernel's proxy fences order only shared memory of the issuer's CTA. -/
theorem actualProxyFence {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l Decoded.kernel A m X)
    {i : EvId} {kind : ProxyFence} {scope : Option MbarScope}
    (he : X.IsProxyFence i kind scope) : kind = .async (some (.shared .cta)) ∧ scope = none := by
  obtain ⟨pc, he⟩ := he
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hf
  have hOp := fires_proxyFence_op hf rfl
  have ha := List.all_eq_true.mp plainSharedProxyFenceCode ins (List.mem_of_getElem? hCode)
  have hCodeShape : ins.op = .fence (.proxy (.async (some (.shared .cta))) none none) := by
    generalize ho : ins.op = op at ha hOp ⊢
    unfold plainSharedProxyFence at ha
    split at ha
    · rfl
    · rw [hOp] at ha
      cases ha
  rw [hCodeShape] at hf
  have hShape := hf.1
  simp only [Event.mk.injEq, Kind.fenceProxy.injEq] at hShape
  exact ⟨hShape.2.1, hShape.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd

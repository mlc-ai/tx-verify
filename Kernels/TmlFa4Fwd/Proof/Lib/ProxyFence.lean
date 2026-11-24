-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotProxyFence

@[expose] public section

/-! # Every proxy fence is of the CTA's shared bytes (`proxy_fence`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {m : Mem0} {X : Execution}

private def ctaFence : Op → Bool
  | .fence (.proxy k o addr) => k == .async (some (.shared .cta)) && o.isNone && addr.isNone
  | _ => true

private theorem ctaFence_code : kernel.code.all (fun i => ctaFence i.op) = true := by
  decide +kernel

/-- Every proxy fence is `fence.proxy.async.shared::cta`. -/
theorem proxy_fence (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {pc : Nat}
    {f : ProxyFence} {sc : Option MbarScope} (he : X.get i = some ⟨pc, .fenceProxy f sc⟩) :
    f = .async (some (.shared .cta)) ∧ sc = none := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hf
  have hop := fires_proxyFence_op hf rfl
  have hu := List.all_eq_true.mp ctaFence_code ins (List.mem_of_getElem? hCode)
  cases hOp : ins.op <;> simp only [hOp, proxyFenceOp, Bool.false_eq_true] at hop
  rename_i fi
  cases fi with
  | thread _ _ => simp at hop
  | proxy kk o addr =>
    simp only [hOp, ctaFence, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hu
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hu
    rw [hOp] at hf
    have hE : ∀ A L g t, eventTmpl A L g t
        (.fence (.proxy (.async (some (.shared .cta))) none none)) =
        .fenceProxy (.async (some (.shared .cta))) none (next t) := fun _ _ _ _ => rfl
    rw [hE] at hf
    simp only [Fires] at hf
    have := congrArg Event.kind hf.1
    simp only [Kind.fenceProxy.injEq] at this
    exact this

end
end PTX.Kernels.TmlFa4Fwd.Proof

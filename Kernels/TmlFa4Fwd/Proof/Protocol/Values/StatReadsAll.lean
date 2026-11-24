-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Elements
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.SoftStores
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatPayload

@[expose] public section

/-! # The statistics reads return what the correction lanes' data machines follow -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (Sc)

/-- **The statistics reads of a consistent execution.** -/
theorem statReads {p : Params} {L : Launch} {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X) : StatReads L X := by
  intro y j s e _ h8 h12 he hpc hst hL
  obtain ⟨pc, kind⟩ := e
  simp only at hpc
  subst hpc
  cases kind with
  | rd a bs =>
    cases s with
    | rscale st =>
      obtain ⟨w, x, rfl | ⟨rfl, -⟩, hr⟩ := scale_payload hp hX hFw h8 h12 hL he
      · exact ⟨Sc.num x, hr⟩
      · exact ⟨Sc.one, hr⟩
    | fsum st =>
      obtain ⟨x, hx, hr⟩ := sum_payload hp hX hFw h8 h12 hL he
      exact ⟨x, hr, hx⟩
    | fmax st => exact max_payload hp hX hFw h8 h12 hL he
    | _ => cases hst
  | _ => cases s <;> trivial

/-- **The softmax lanes' part of the operand values** of a consistent execution. -/
theorem softFacts {p : Params} {L : Launch} {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X) : SoftFacts L X :=
  ⟨softStores hp hX hFw, statReads hp hX hFw⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Values

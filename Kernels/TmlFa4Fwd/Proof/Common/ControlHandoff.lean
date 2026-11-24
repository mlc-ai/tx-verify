-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Handoff
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Handoff

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow PTX.Proof

theorem handoffU {p L m g} (hp : Pre p L m) (hg : g < L.threads) :
    Code.Handoff (Startup.code p L g) (frag p L g) (exit L g) := by
  intro d i t hx hat hi
  obtain ⟨h,href⟩ := handoffD hp hg d i t hx hat hi
  cases i with
  | correction =>
    obtain ⟨pc, sub, acc, fault, regs⟩ := h
    exact ⟨⟨pc, sub, acc, fault, Correction.Control.facts_init p L g ▸ regs⟩,
      .inl rfl⟩
  | softmax =>
    obtain ⟨pc, sub, acc, fault, regs⟩ := h
    exact ⟨⟨pc, sub, acc, fault, Softmax.Control.facts_init p L g ▸ regs⟩,
      .inl ⟨rfl,rfl,rfl⟩,href.2.1⟩
  | _ => exact ⟨h,href⟩

end PTX.Kernels.TmlFa4Fwd.Proof

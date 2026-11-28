-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Softmax.BiasAt

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Proof

/-- **A bias load of the Softmax region reads the two bytes of an element of `Rel`.** -/
public theorem bias_read {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩)
    (site : (∃ j : Fin 64, pc = 680 + 2 * j.val) ∨ ∃ j : Fin 64, pc = 1124 + 2 * j.val) :
    ∃ r < Q.b, ∃ tok < Q.qLen r, ∃ head < heads, ∃ c < relPad,
      a.loc = ⟨.global, 0, Q.relBase + 2 * ((Q.qStart r + tok) * Q.strideRel + head * relPad + c)⟩ ∧
      a.size = 2 := by
  obtain ⟨z, x, y, j, B, -, -, -, hz, -, -, -, ht, hh, hc, -, loc, size⟩ := bias_at hp hX hf he site
  exact ⟨z, hz, _, ht, _, hh, _, hc, loc, size⟩

/-- A bias load of the Softmax region reads input bytes. -/
public theorem bias_address {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩)
    (site : (∃ j : Fin 64, pc = 680 + 2 * j.val) ∨ ∃ j : Fin 64, pc = 1124 + 2 * j.val) :
    Iface.InputAcc Q a := by
  obtain ⟨r, hr, tok, ht, head, hh, c, hc, loc, size⟩ := bias_read hp hX hf he site
  refine ⟨by rw [loc], by rw [loc], fun jj hjj => ?_⟩
  rw [loc]
  exact .inr (.inl ⟨r, hr, tok, ht, head, hh, c, hc, jj, by omega, rfl⟩)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

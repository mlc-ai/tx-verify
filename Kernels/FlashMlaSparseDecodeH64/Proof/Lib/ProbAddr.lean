-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot

@[expose] public section

/-! # The address of a PV MMA's A byte

A byte of a PV MMA's A operand (the P tile, `probDesc B k`: K-major, no swizzle, leading offset
1024, stride 128, start `B + 2048 (k / 2)`) at element `(r, kk)`, `r < 128` the A row of the read
(`.ws` with M = 64: shared row `r % 64`), `kk < 16`, byte `z < 2`, is at
`B + 2048 (k / 2) + 16 (r % 64) + 1024 (kk / 8) + 2 (kk % 8) + z` (`prob_addr`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
open PTX

/-- **The address of an A byte of a PV MMA.** -/
theorem prob_addr {s : TcMma.OperandSpec} (hD : s.descriptor = pvD) {B k : Nat}
    (hs : s.a = probDesc B k) (haT : s.aTmem = none) {r kk z : Nat} {l : Loc}
    (hkk : kk < 16) (hz : z < 2) (h : s.byteLoc .a (2 * (r * 16 + kk) + z) = some l) :
    l.addr = B + 2048 * (k / 2) + 16 * (r % 64) + 1024 * (kk / 8) + 2 * (kk % 8) + z := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, pvD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs, haT,
    TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := pvD_valid
  simp only [pvD] at hv
  simp [hv] at h
  obtain ⟨hrow, h⟩ := h
  obtain ⟨a, hba, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := (Option.some.inj h).symm
  have h1 := TcShared.byteAddress_none_eq rfl hba
  simp only [TcShared.linear, TcShared.Swizzle.sectors, probDesc, ↓reduceIte] at h1
  show a = _
  rw [h1]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
public import Core.Tc.TcMmaSafety

@[expose] public section

/-! # The MMAs' issue checks

Pure geometry: a QK MMA (descriptor `qkD`, D at column 400, A in Tensor Memory at
`256 + 8 k`, B and A words `keyDesc B k`) and a PV MMA (descriptor `pvD`, D at column 0 or 128,
A `probDesc B' k`, B `valueDesc B k`) pass `TcMma.IssueShape`: both shared descriptors are
encoded and every operand byte has an address. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot
open PTX

private theorem enc_key {B k : Nat} (hk : k < 16) (h16 : B % 16 = 0) (hB : B + 131072 ≤ 2 ^ 18) :
    TcMma.SharedEncoded (keyDesc B k) := by
  simp only [TcMma.SharedEncoded, keyDesc, qkDelta, and_true]
  omega

private theorem enc_value {B k : Nat} (hk : k < 8) (h16 : B % 16 = 0)
    (hB : B + 131072 ≤ 2 ^ 18) : TcMma.SharedEncoded (valueDesc B k) := by
  simp only [TcMma.SharedEncoded, valueDesc, pvDelta, and_true]
  omega

private theorem enc_prob {B k : Nat} (hk : k < 8) (h16 : B % 16 = 0) (hB : B + 8192 ≤ 2 ^ 18) :
    TcMma.SharedEncoded (probDesc B k) := by
  simp only [TcMma.SharedEncoded, probDesc, and_true]
  omega

/-- Every B byte of a QK MMA has a shared address. -/
private theorem qk_bLoc {s : TcMma.OperandSpec} {B k : Nat} (hD : s.descriptor = qkD)
    (hs : s.b = keyDesc B k) {idx : Nat} (hi : idx < TcMma.Operand.bytes .b qkD) :
    ∃ loc, s.byteLoc .b idx = some loc := by
  have hv := qkD_valid
  simp only [qkD] at hv
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes, TcMma.Operand.rows] at hi ⊢
  simp [hv]
  simp at hi
  refine ⟨by omega, ?_⟩
  unfold TcShared.byteAddress
  simp [keyDesc, show idx % 2 ≤ 1 by omega]


/-- Every B byte of a PV MMA has a shared address. -/
private theorem pv_bLoc {s : TcMma.OperandSpec} {B k : Nat} (hD : s.descriptor = pvD)
    (hs : s.b = valueDesc B k) {idx : Nat} (hi : idx < TcMma.Operand.bytes .b pvD) :
    ∃ loc, s.byteLoc .b idx = some loc := by
  have hv := pvD_valid
  simp only [pvD] at hv
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, pvD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes, TcMma.Operand.rows] at hi ⊢
  simp [hv]
  simp at hi
  refine ⟨by omega, ?_⟩
  unfold TcShared.byteAddress
  simp [valueDesc, show idx % 2 ≤ 1 by omega]

/-- Every A byte of a PV MMA has a shared address. -/
private theorem pv_aLoc {s : TcMma.OperandSpec} {B k : Nat} (hD : s.descriptor = pvD)
    (hs : s.a = probDesc B k) (haT : s.aTmem = none) {idx : Nat}
    (hi : idx < TcMma.Operand.bytes .a pvD) : ∃ loc, s.byteLoc .a idx = some loc := by
  have hv := pvD_valid
  simp only [pvD] at hv
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, pvD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs, haT,
    TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes, TcMma.Operand.rows] at hi ⊢
  simp [hv]
  simp at hi
  refine ⟨by omega, ?_⟩
  unfold TcShared.byteAddress
  simp [probDesc, show idx % 2 ≤ 1 by omega]

/-- Every A byte of a QK MMA has a Tensor Memory cell. -/
private theorem qk_aCell {s : TcMma.OperandSpec} {k : Nat} (hk : k < 16) (hD : s.descriptor = qkD)
    (haT : s.aTmem = some (256 + 8 * k)) {idx : Nat} (hi : idx < TcMma.Operand.bytes .a qkD) :
    ∃ c, TcMma.aCell s idx = some c := by
  have hv := qkD_valid
  simp only [qkD] at hv
  unfold TcMma.aCell
  simp only [hD, qkD, haT, TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes,
    TcMma.Operand.rows, Option.bind_some] at hi ⊢
  simp [hv, TcMma.halfDatapath]
  simp at hi
  exact ⟨by omega, by omega, .inr (by omega)⟩


/-- **A QK MMA passes the issue checks**: D at column 400, A in Tensor Memory at `256 + 8 k`, A
and B words `keyDesc B k`. -/
theorem qk_issueShape {L : Launch} {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {mask : List Nat}
    {B k : Nat} (hi : i.1 < L.threads) (hk : k < 16) (h16 : B % 16 = 0)
    (hB : B + 131072 ≤ 2 ^ 18) (hd : d = 400) (hm : mask = [0, 0, 0, 0])
    (hD : s.descriptor = qkD) (haT : s.aTmem = some (256 + 8 * k))
    (hL : s.MatchesLaunch L (i.1 / L.block)) (ha : s.a = keyDesc B k) (hb : s.b = keyDesc B k) :
    TcMma.IssueShape L i d s mask := by
  subst hd hm
  refine ⟨hi, hD ▸ qkD_valid, hD ▸ (by decide), hL, ha ▸ enc_key hk h16 hB,
    hb ▸ enc_key hk h16 hB, hD ▸ .inl (by decide), fun a _ hh => ?_, hD ▸ (by decide), ?_⟩
  · rw [hD] at hh
    exact absurd hh (by decide)
  · intro op idx hidx
    cases op
    · exact .inr ⟨rfl, qk_aCell hk hD haT (hD ▸ hidx)⟩
    · exact .inl (qk_bLoc hD hb (hD ▸ hidx))

/-- **A PV MMA passes the issue checks**: D at column `c` (0 or 128), A in shared memory, A word
`probDesc B' k`, B word `valueDesc B k`. -/
theorem pv_issueShape {L : Launch} {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {mask : List Nat}
    {B B' k : Nat} (hi : i.1 < L.threads) (hk : k < 8) (h16 : B % 16 = 0) (h16' : B' % 16 = 0)
    (hB : B + 131072 ≤ 2 ^ 18) (hB' : B' + 8192 ≤ 2 ^ 18) (hd : d = 0 ∨ d = 128)
    (hm : mask = [0, 0, 0, 0]) (hD : s.descriptor = pvD) (haT : s.aTmem = none)
    (hL : s.MatchesLaunch L (i.1 / L.block)) (ha : s.a = probDesc B' k)
    (hb : s.b = valueDesc B k) : TcMma.IssueShape L i d s mask := by
  subst hm
  have hd' : d / 2 ^ 16 = 0 ∧ d % 2 ^ 16 = d := by rcases hd with rfl | rfl <;> decide
  refine ⟨hi, hD ▸ pvD_valid, hD ▸ (by decide), hL, ha ▸ enc_prob hk h16' hB',
    hb ▸ enc_value hk h16 hB, hD ▸ (hd'.1 ▸ .inl rfl), fun a h => by simp [haT] at h, ?_, ?_⟩
  · rw [hD, hd'.2]
    rcases hd with rfl | rfl <;> decide
  · intro op idx hidx
    cases op
    · exact .inl (pv_aLoc hD ha haT (hD ▸ hidx))
    · exact .inl (pv_bLoc hD hb (hD ▸ hidx))


/-- **A query copy passes `CopySafe`**: shape `128x256b`, source `keyDesc B k`. -/
theorem cp_safe {c : TcCopy.Spec} {B k : Nat} (hk : k < 16) (h16 : B % 16 = 0)
    (hB : B + 131072 ≤ 2 ^ 18) (hsh : c.shape = .s128x256b) (hs : c.src = keyDesc B k) :
    TcMma.CopySafe c := by
  refine ⟨hs ▸ enc_key hk h16 hB, fun cta _ idx hidx => ?_⟩
  rw [hsh, hs] at *
  unfold TcCopy.byteLoc
  simp only [hidx, ↓reduceIte]
  unfold TcShared.byteAddress
  simp [keyDesc]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MmaFoot

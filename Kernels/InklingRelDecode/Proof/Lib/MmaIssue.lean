-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.MmaFoot
public import Core.Tc.TcMmaSafety

@[expose] public section

/-! # The MMAs' issue checks

Pure geometry: a QK MMA (descriptor `qkDesc`, both operands K-major in shared memory, D at column
`128 (i % 2)`) and a PV MMA (descriptor `pvDesc`, A in Tensor Memory at `128 b + 8 j`, B MN-major,
D at column 256) pass `TcMma.IssueShape`: the shared descriptors are encoded and every operand byte
has an address. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

private theorem addr_k {st row k byte : Nat} (h : byte < 2) :
    ∃ a, TcShared.byteAddress 2 .k ⟨st, 0, 1024, 0, false, false, .b128⟩ row k byte = some a := by
  unfold TcShared.byteAddress
  simp [h]

private theorem addr_mn {st row k byte : Nat} (h : byte < 2) :
    ∃ a, TcShared.byteAddress 2 .mn ⟨st, 16384, 1024, 0, false, false, .b128⟩ row k byte =
      some a := by
  unfold TcShared.byteAddress
  simp [h]

/-- Every byte of a QK MMA's shared operand has an address. -/
theorem qk_byteLoc {s : TcMma.OperandSpec} {op : TcMma.Operand} {st : Nat}
    (hD : s.descriptor = qkDesc) (haT : op = .a → s.aTmem = none)
    (hs : (match op with | .a => s.a | .b => s.b) = ⟨st, 0, 1024, 0, false, false, .b128⟩)
    {idx : Nat} (hi : idx < TcMma.Operand.bytes op s.descriptor) :
    ∃ loc, s.byteLoc op idx = some loc := by
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  unfold TcMma.OperandSpec.byteLoc
  cases op
  · simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size,
      TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes, TcMma.Operand.rows] at hi hs haT ⊢
    simp [hv, haT, hs] at hi ⊢
    obtain ⟨a, ha⟩ := addr_k (st := st) (row := idx / 32 % 64) (k := idx / 2 % 16)
      (byte := idx % 2) (by omega)
    rw [ha]
    exact ⟨by omega, _, rfl⟩
  · simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size,
      TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes, TcMma.Operand.rows] at hi hs ⊢
    simp [hv, hs] at hi ⊢
    obtain ⟨a, ha⟩ := addr_k (st := st) (row := idx / 32 % 128) (k := idx / 2 % 16)
      (byte := idx % 2) (by omega)
    rw [ha]
    exact ⟨by omega, _, rfl⟩

/-- Every B byte of a PV MMA has an address. -/
theorem pv_bLoc {s : TcMma.OperandSpec} {st : Nat} (hD : s.descriptor = pvDesc)
    (hs : s.b = ⟨st, 16384, 1024, 0, false, false, .b128⟩) {idx : Nat}
    (hi : idx < TcMma.Operand.bytes .b s.descriptor) : ∃ loc, s.byteLoc .b idx = some loc := by
  have hv := pvDesc_valid
  simp only [pvDesc] at hv
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, pvDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size,
    TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes, TcMma.Operand.rows] at hi hs ⊢
  simp [hv, hs] at hi ⊢
  obtain ⟨a, ha⟩ := addr_mn (st := st) (row := idx / 32 % 128) (k := idx / 2 % 16)
    (byte := idx % 2) (by omega)
  rw [ha]
  exact ⟨by omega, _, rfl⟩

/-- Every A byte of a PV MMA (A in Tensor Memory at `a < 256`) has a cell. -/
theorem pv_aCell {s : TcMma.OperandSpec} {a : Nat} (hD : s.descriptor = pvDesc)
    (haT : s.aTmem = some a) (ha : a < 256) {idx : Nat}
    (hi : idx < TcMma.Operand.bytes .a s.descriptor) : ∃ c, TcMma.aCell s idx = some c := by
  have hv := pvDesc_valid
  simp only [pvDesc] at hv
  unfold TcMma.aCell
  simp only [hD, pvDesc, haT, TcMma.Kind.k, TcMma.Kind.width, TcMma.Operand.bytes,
    TcMma.Operand.rows, Option.bind_some] at hi ⊢
  simp [hv, TcMma.halfDatapath]
  simp at hi
  exact ⟨by omega, by omega, .inr (by omega)⟩

private theorem enc_k {st : Nat} (h : st < 2 ^ 18) (h16 : st % 16 = 0) :
    TcMma.SharedEncoded ⟨st, 0, 1024, 0, false, false, .b128⟩ := by
  refine ⟨h, ?_, ?_, h16, ?_, ?_⟩ <;> dsimp only <;> omega

private theorem enc_mn {st : Nat} (h : st < 2 ^ 18) (h16 : st % 16 = 0) :
    TcMma.SharedEncoded ⟨st, 16384, 1024, 0, false, false, .b128⟩ := by
  refine ⟨h, ?_, ?_, h16, ?_, ?_⟩ <;> dsimp only <;> omega

/-- **A QK MMA passes the issue checks**: D at column `128 b` (`b < 2`), both operands K-major in
shared memory, words `(sa, sb)`. -/
theorem qk_issueShape {L : Launch} {i : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {mask : List Nat}
    {sa sb : Nat} (hi : i.1 < L.threads) (hsa : sa < 2 ^ 18) (hsb : sb < 2 ^ 18)
    (h16a : sa % 16 = 0) (h16b : sb % 16 = 0) (hd : d = 0 ∨ d = 128)
    (hm : mask = [0, 0, 0, 0]) (hD : s.descriptor = qkDesc) (haT : s.aTmem = none)
    (hL : s.MatchesLaunch L (i.1 / L.block))
    (ha : s.a = ⟨sa, 0, 1024, 0, false, false, .b128⟩)
    (hb : s.b = ⟨sb, 0, 1024, 0, false, false, .b128⟩) : TcMma.IssueShape L i d s mask := by
  subst hm
  have hd' : d / 2 ^ 16 = 0 ∧ d % 2 ^ 16 = d := by rcases hd with rfl | rfl <;> decide
  refine ⟨hi, hD ▸ qkDesc_valid, hD ▸ (by decide), hL, ha ▸ enc_k hsa h16a, hb ▸ enc_k hsb h16b,
    hD ▸ .inl hd'.1, fun a h => by simp [haT] at h, ?_, ?_⟩
  · rw [hD, hd'.2]
    rcases hd with rfl | rfl <;> decide
  · intro op idx hidx
    cases op
    · exact .inl (qk_byteLoc (op := .a) hD (fun _ => haT) ha hidx)
    · exact .inl (qk_byteLoc (op := .b) hD (fun h => by cases h) hb hidx)

/-- **A PV MMA passes the issue checks**: D at column 256, A in Tensor Memory at `a < 256` in
the lane field of D, B MN-major with word `sb`. -/
theorem pv_issueShape {L : Launch} {i : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {mask : List Nat}
    {sb a : Nat} (hi : i.1 < L.threads) (hsb : sb < 2 ^ 18) (h16b : sb % 16 = 0)
    (hd : d = 256) (hm : mask = [0, 0, 0, 0]) (hD : s.descriptor = pvDesc)
    (haT : s.aTmem = some a) (ha : a < 256) (same : s.a = s.b)
    (hL : s.MatchesLaunch L (i.1 / L.block))
    (hb : s.b = ⟨sb, 16384, 1024, 0, false, false, .b128⟩) : TcMma.IssueShape L i d s mask := by
  subst hm hd
  refine ⟨hi, hD ▸ pvDesc_valid, hD ▸ (by decide), hL, same ▸ hb ▸ enc_mn hsb h16b,
    hb ▸ enc_mn hsb h16b,
    hD ▸ .inl (by decide), fun a' h _ => by simp only [haT, Option.some.injEq] at h; omega,
    hD ▸ (by decide), ?_⟩
  · intro op idx hidx
    cases op
    · exact .inr ⟨rfl, pv_aCell hD haT ha hidx⟩
    · exact .inl (pv_bLoc hD hb hidx)

end PTX.Kernels.InklingRelDecode.Proof.Lib

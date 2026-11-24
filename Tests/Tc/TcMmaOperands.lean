-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaOperands

namespace PTX.Tests.TcMmaOperands
open TcMma

private def launch : Launch := { grid := 8, block := 384, params := fun _ => none, clusterSize :=
                                 ⟨4, by decide⟩ }
private def desc : Descriptor := ⟨.two, .f16 .f16 .f32, 256, 128, false, false, false, false, false⟩
private def smem : TcShared.Descriptor := ⟨1024, 0, 1024, 0, false, false, .b128⟩

private def at2 (issuer : Nat) (d : Descriptor) (op : Operand) (row k byte : Nat) : Option Loc := do
  let s ← makeOperands launch issuer d smem smem
  s.byteLoc op (row * 32 + k * 2 + byte)

-- An odd issuing CTA in the second pair of a nonzero cluster.
example : at2 7 desc .a 0 0 0 = some ⟨.shared, 6, 1024⟩ := rfl
example : at2 7 desc .a 128 0 0 = some ⟨.shared, 7, 1024⟩ := rfl
example : at2 6 desc .a 129 0 1 = some ⟨.shared, 7, 1169⟩ := rfl
-- B splits at N/2, not M/2; local row numbering restarts in the peer.
example : at2 7 desc .b 64 0 0 = some ⟨.shared, 7, 1024⟩ := rfl
example : at2 6 desc .b 65 0 0 = some ⟨.shared, 7, 1168⟩ := rfl
example : at2 7 desc .b 128 0 0 = none := rfl
example : at2 8 desc .a 0 0 0 = none := rfl
-- A valid cluster can nevertheless have no peer for its last even rank.
private def launch3 : Launch :=
  { grid := 6, block := 384, params := fun _ => none, clusterSize := ⟨3, by decide⟩ }
example : makeOperands launch3 2 desc smem smem = none := by decide
-- Transposition changes the address within the same selected CTA.
example : at2 7 { desc with transposeB := true } .b 65 0 0 = some ⟨.shared, 7, 1026⟩ := rfl

-- cta_group::1: every row of both operands is in the issuer's own CTA, at any rank.
private def i8 : Descriptor := ⟨.one, .i8 true true false, 128, 8, false, false, false, false,
    false⟩
private def k8 : TcShared.Descriptor := ⟨4096, 128, 256, 0, false, false, .none⟩

example : (makeOperands launch 7 i8 k8 k8).map (fun s => (s.lowCta, s.highCta)) = some (7, 7) :=
  rfl
example : (makeOperands launch 5 i8 k8 k8).map (fun s => (s.lowCta, s.highCta)) = some (5, 5) :=
  rfl

private def at1 (op : Operand) (index : Nat) : Option Loc := do
  let s ← makeOperands launch 5 i8 k8 k8
  s.byteLoc op index

-- One-byte elements: flat index `row * 32 + k` is the canonical K-major position
-- `start + 16 (row % 8) + SBO (row / 8) + k % 16 + LBO (k / 16)`.
example : at1 .a 0 = some ⟨.shared, 5, 4096⟩ := rfl
example : at1 .a 1 = some ⟨.shared, 5, 4097⟩ := rfl
example : at1 .a 16 = some ⟨.shared, 5, 4096 + 128⟩ := rfl
example : at1 .a (1 * 32) = some ⟨.shared, 5, 4096 + 16⟩ := rfl
example : at1 .a (8 * 32) = some ⟨.shared, 5, 4096 + 256⟩ := rfl
example : at1 .a (127 * 32 + 31) =
    some ⟨.shared, 5, 4096 + 16 * 7 + 256 * 15 + 15 + 128⟩ := rfl
-- B rows are N; there are only N = 8 of them.
example : at1 .b (7 * 32 + 31) = some ⟨.shared, 5, 4096 + 16 * 7 + 15 + 128⟩ := rfl
example : at1 .b (8 * 32) = none := rfl
example : at1 .a (128 * 32) = none := rfl

-- Group identities always come from the launch.
example {L : Launch} {issuer : Nat} {d : Descriptor} {a b : TcShared.Descriptor} {s : OperandSpec}
    (h : makeOperands L issuer d a b = some s) : s.MatchesLaunch L issuer :=
  makeOperands_matches h

end PTX.Tests.TcMmaOperands

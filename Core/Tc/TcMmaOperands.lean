-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaDescriptor
public import Core.Tc.TcSharedAddress
public import Core.Tmem.CtaPair

@[expose] public section

namespace PTX.TcMma

/-! ## THREAD-TC-MMA-OPERANDS — shared operand locations of a CTA group
Statement: Each byte of the A and B operands of an MMA is read from the shared memory of a CTA of
  the issuing group, at the address that the operand's shared matrix descriptor gives for its row,
  contraction element and byte. With `.cta_group::2` the first half of the rows of A (along M) and
  of B (along N) is read from the pair's even-rank CTA and the second half from its odd-rank CTA,
  and a transposed operand is addressed MN-major.

Defs: TcMma.Operand, TcMma.Operand.extent, TcMma.Operand.major, TcMma.Operand.rows,
  TcMma.Operand.bytes, TcMma.Collectors, TcMma.OperandSpec, TcMma.OperandSpec.byteLoc,
  TcMma.OperandSpec.MatchesLaunch, TcMma.OperandSpec.matchesLaunch_iff, TcMma.makeOperands

Source:
- §9.7.18.5.1 (CTA pairs)
- §9.7.18.10.6 (transpose); NVIDIA CUTLASS include/cute/atom/mma_traits_sm100.hpp SM100_MMA_*_SS and
    SM100_MMA_*_2x1SM_SS ALayout/BLayout
- EXT-TCFIG

Direction: reading

Applies: Dense shared A and B operands in the represented canonical descriptor modes, for either CTA
  group

Premises: Valid instruction shape, the issuer's CTA group in the launch, in-range matrix coordinate
  and element byte, and supported shared descriptor addressing.

Effect: Computes a shared location only. Either CTA of a `cta_group::2` pair may issue.
  Transposition selects the local major order and leaves the CTA partition unchanged. A transposed
  operand of kind::tf32 requires the 128-byte swizzle with 32-byte atomicity, and a transposed
  operand of the other kinds excludes it (Table 65, THREAD-TC-SHARED-ADDRESS). The element width is
  that of the kind. With `.ws` and M below 128 the A read has one row per D lane, and lane `L` reads
  A row `L % M` (EXT-TCFIG). The same descriptor byte offset is interpreted in each
  participating CTA's shared memory. Group numbering is cluster-relative, including clusters larger
  than two; the partition and which CTA of the pair holds which half are EXT-TCFIG.
-/
/-- The A or B operand of an MMA. -/
inductive Operand where
  | a | b
  deriving DecidableEq, Repr

/-- The rows of the operand: M for A and N for B. -/
def Operand.extent (op : Operand) (d : Descriptor) : Nat :=
  match op with
  | .a => d.m
  | .b => d.n

/-- The major order of the operand in shared memory: MN-major when its transpose bit is set,
otherwise K-major. -/
def Operand.major (op : Operand) (d : Descriptor) : TcShared.Major :=
  let transpose := match op with
    | .a => d.transposeA
    | .b => d.transposeB
  if transpose then .mn else .k

/-- Rows one issue reads for the operand. With `.ws` and M < 128 (Layouts E, G) every D lane
reads its own A row (EXT-TCFIG): 128 rows, lane `L` reading A row `L % m`. -/
def Operand.rows (op : Operand) (d : Descriptor) : Nat :=
  if op = .a ∧ d.ws ∧ d.m < 128 then 128 else op.extent d

/-- Bytes one issue reads for the operand. -/
def Operand.bytes (op : Operand) (d : Descriptor) : Nat :=
  op.rows d * d.kind.k * d.kind.width

/-- The collector usage of one issue: of A, and of B with its buffer (PROG-ISA-TC-MMA). The
collector rule is ERR-TC-COLLECTOR-REUSE; the operand locations do not depend on it. -/
structure Collectors where
  a : MmaCollector := .discard
  b : MmaCollector := .discard
  bBuffer : Nat := 0
  deriving DecidableEq, Repr

/-- Frozen addressing data of one issue; no operand values are captured here. `lowCta`
holds the first `extent / group.size` rows of each operand and `highCta` the rest; with
`cta_group::1` both are the issuer's CTA. -/
structure OperandSpec where
  /-- The decoded instruction descriptor. -/
  descriptor : Descriptor
  /-- The shared matrix descriptor of A. -/
  a : TcShared.Descriptor
  /-- The shared matrix descriptor of B. -/
  b : TcShared.Descriptor
  /-- The CTA holding the first half of the rows: the pair's even-rank CTA, or the issuer with
  `cta_group::1`. -/
  lowCta : Nat
  /-- The CTA holding the second half of the rows: the pair's odd-rank CTA, or the issuer with
  `cta_group::1`. -/
  highCta : Nat
  /-- `some address`: A is read from Tensor Memory at `address` (`[a-tmem]`); `s.a` is then
  unused. `none`: A is in shared memory. -/
  aTmem : Option Nat
  /-- The collector usage of the issue. -/
  collector : Collectors := {}
  deriving DecidableEq, Repr

/-- Flat byte number is row-major (row `< op.rows d`, contraction, byte), not physical
smem order; with `.ws` and M < 128, A row `L` is shared row `L % m`. -/
def OperandSpec.byteLoc (s : OperandSpec) (op : Operand) (index : Nat) : Option Loc := do
  let d := s.descriptor
  let w := d.kind.width
  let row := index / (d.kind.k * w)
  if ¬(Valid d ∧ row < if op = .a ∧ d.ws ∧ d.m < 128 then 128 else op.extent d) then none else do
    let half := op.extent d / d.group.size
    let cta := if row < half then s.lowCta else s.highCta
    if op = .a ∧ s.aTmem.isSome then none else do
    let shared := match op with | .a => s.a | .b => s.b
    let addr ← TcShared.byteAddress w (op.major d) shared (row % half)
      (index / w % d.kind.k) (index % w)
    pure ⟨.shared, cta, addr⟩

/-- The issue adapter must establish the identities from the actual issuer's launch. -/
def OperandSpec.MatchesLaunch (s : OperandSpec) (L : Launch) (issuer : Nat) : Prop :=
  ∃ ctas, L.ctaGroup issuer s.descriptor.group = some ctas ∧
    ctas.head? = some s.lowCta ∧ ctas.getLast? = some s.highCta

/-- Resolve the group's CTA identities from the issuer, without choosing any read values: the
first and last CTA of the issuer's CTA group. -/
def makeOperands (L : Launch) (issuer : Nat) (d : Descriptor)
    (a b : TcShared.Descriptor) : Option OperandSpec := do
  let ctas ← L.ctaGroup issuer d.group
  let lowCta ← ctas.head?
  let highCta ← ctas.getLast?
  pure ⟨d, a, b, lowCta, highCta, none, {}⟩

set_option linter.unusedSimpArgs false in
/-- Per-form lemma: `MatchesLaunch` as the two `peerCta` equations of the group's first and last
rank (the former definition). -/
theorem OperandSpec.matchesLaunch_iff (s : OperandSpec) (L : Launch) (issuer : Nat) :
    s.MatchesLaunch L issuer ↔
      L.peerCta issuer (L.rankOfCta issuer / s.descriptor.group.size * s.descriptor.group.size) =
          some s.lowCta ∧
        L.peerCta issuer (L.rankOfCta issuer / s.descriptor.group.size *
            s.descriptor.group.size + s.descriptor.group.size - 1) = some s.highCta := by
  unfold OperandSpec.MatchesLaunch
  cases hg : s.descriptor.group with
  | one =>
    rw [Launch.ctaGroup_one]
    simp only [CtaGroup.size, Nat.div_one, Nat.mul_one]
    cases h1 : L.peerCta issuer (L.rankOfCta issuer) <;> simp [h1, eq_comm]
  | two =>
    rw [Launch.ctaGroup_two]
    simp only [CtaGroup.size]
    cases h1 : L.peerCta issuer (L.rankOfCta issuer / 2 * 2) <;>
      cases h2 : L.peerCta issuer (L.rankOfCta issuer / 2 * 2 + 1) <;> simp [h1, h2, eq_comm]

end PTX.TcMma

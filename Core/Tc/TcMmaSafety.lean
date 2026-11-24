-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaRead
public import Core.Tc.TcMmaCollector
public import Core.Assembly.SharedLifetime

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## ERR-TC-MMA — issue coverage and completed result coverage
Statement: An execution is unsafe when an MMA has an invalid shape or mask, CTAs that do not match
  the launch, a shared descriptor that is not encoded or not supported, a D address with a wrong
  lane alignment or columns past the 512th, or an operand byte without an address. It is also unsafe
  when a completed MMA has an unmasked result without a derived value, when a `tcgen05.cp` reads an
  unsupported source, or when an MMA reuses a collector buffer against ERR-TC-COLLECTOR-REUSE.

Defs: TcMma.SharedEncoded, TcMma.IssueShape, TcMma.CompletedValues, TcMma.CopySafe,
  TcMma.InstructionSafe, TcMma.InstructionUnsafe

Source:
- §9.7.18.4.1 (descriptor encoding/alignment)
- §9.7.18.5 (issue granularity and active peer)
- §9.7.18.10.5 (D layout)
- §9.7.18.10.9.5 (alignment)
- §9.7.18.10.10.1 (MMA)
- DEP-TC-MMA-VALUE

Direction: stricter

Applies: Every represented dense MMA, including instructions with no subsequent load, and every
  represented tcgen05.cp

Premises: Launched issuer, valid decoded shape and masks, launch-derived CTA group, encoded shared
  fields, the same Layout F lane alignment for D and Tensor Memory A (§9.7.18.10.5), complete
  supported operand address mapping and in-range D. Every completed unmasked output has a finite
  numerical derivation; every collector reuse satisfies `CollectorSafe`. The sources of the
  accumulator and A reads of a completed MMA are required by ERR-TMEM-READ-SOURCE.

Effect: InstructionUnsafe enters Unsafe and does not filter executions. Base-offset, absolute and
  LUT modes are limited by the support scope of THREAD-TC-SHARED-ADDRESS. The checks apply to every
  result of a completed MMA, whether or not a later load reads it. The lifetimes of the operand CTAs
  are checked by ERR-SHARED-LIFETIME, whose completing stage is the completion of the MMA or copy.
-/

/-- Canonical 16-byte-unit encoding represents 18-bit byte addresses/strides. -/
def SharedEncoded (d : TcShared.Descriptor) : Prop :=
  d.start < 2^18 ∧ d.leading < 2^18 ∧ d.stride < 2^18 ∧
    d.start % 16 = 0 ∧ d.leading % 16 = 0 ∧ d.stride % 16 = 0

/-- The checks on one MMA issue: a launched issuer, a valid shape and mask, CTAs that match the
launch, encoded shared descriptors, a permitted D lane alignment (shared by a Tensor Memory A in
Layout F), D columns within the 512, and an address for every operand byte. -/
def IssueShape (L : Launch) (i : EvId) (d : Nat) (s : OperandSpec) (mask : List Nat) : Prop :=
  i.1 < L.threads ∧ Valid s.descriptor ∧ OutputMaskValid s.descriptor.group mask ∧
    s.MatchesLaunch L (i.1 / L.block) ∧ SharedEncoded s.a ∧ SharedEncoded s.b ∧
    LaneAligned s.descriptor (d / 2 ^ 16) ∧
    (∀ address, s.aTmem = some address → halfDatapath s.descriptor →
      address / 2 ^ 16 = d / 2 ^ 16) ∧
    d % 2 ^ 16 + resultColumns s.descriptor ≤ 512 ∧
    ∀ op index, index < op.bytes s.descriptor →
      (∃ loc, s.byteLoc op index = some loc) ∨ (op = .a ∧ ∃ c, aCell s index = some c)

/-- Each unmasked result cell of a completed MMA has a derived value. -/
def CompletedValues (L : Launch) (A : List Assumption) (X : Execution) (i : EvId) : Prop :=
  X.async.mmaDone i = true → ∀ cell, X.MmaCell i cell → ∃ value, Result L A X i cell value

/-- A copy reads only represented, encoded shared locations, in every CTA of its group. -/
def CopySafe (c : TcCopy.Spec) : Prop :=
  SharedEncoded c.src ∧ ∀ cta ∈ c.ctas, ∀ index < c.shape.sourceBytes,
    ∃ loc, TcCopy.byteLoc c.shape c.src cta index = some loc

/-- Every MMA passes its issue checks and its completed results are derived, every copy reads a
supported source, and every collector reuse is justified (ERR-TC-COLLECTOR-REUSE). -/
def InstructionSafe (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  (∀ i d s accum mask, X.MmaIssue i d s accum mask →
    IssueShape L i d s mask ∧ CompletedValues L A X i) ∧
  (∀ i c, X.CpIssue i c → CopySafe c) ∧ CollectorSafe X

/-- Some MMA or copy fails the checks of `InstructionSafe`. -/
def InstructionUnsafe (L : Launch) (A : List Assumption) (X : Execution) : Prop :=
  ¬ InstructionSafe L A X

end
end PTX.TcMma

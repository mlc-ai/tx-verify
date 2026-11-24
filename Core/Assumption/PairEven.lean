-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.ClusterScopeMbar
public import Core.Thread.Local

@[expose] public section

/-!
# Assumption constructor `pairEvenAt`

A kernel declares the peer-bit assumption with `Assumption.pairEvenAt`, naming exactly the
`and.b32 d, a, -16777217` sites whose result its proof reads as the `.shared::cluster` address of
the same byte in the even CTA of the CTA pair. This file is not itself an assumption.
-/

namespace PTX.Assumption

/-! ## ASM-PEER-BIT — clearing bit 24 of a shared window address names the even CTA of the pair
Statement: At the `and.b32 d, a, -16777217` sites a kernel names, the model reads the result as the
  `.shared::cluster` address of the same byte in the even CTA of the executing CTA's pair, which
  relies on the hardware encoding of cluster shared addresses. A kernel that computes this address
  with `mapa` does not need this assumption.

Defs: Assumption.peerBitMask, Assumption.execPairEven, Assumption.pairEvenAt

Source:
- §9.7.10.28.5.3: "When .cta_group::2 is specified, the mbarrier object mbar can be in shared
    memory of either the same CTA as the shared memory destination dstMem or in its peer-CTA"
- §5.1.7: "The addresses in the .shared::cta window also fall within the .shared::cluster window."
- §9.7.10.26 (mapa)
- CUTLASS `Sm100MmaPeerBitMask` (0xFEFFFFFF, `include/cute/arch/copy_sm100_tma.hpp`)

Direction: trust

Effect: `pairEvenAt K name sites why` reads one instruction as one local step, through the field
  `segmentRule` (THREAD-LOCAL). Core's `and.b32` would give the integer `a & 0xFEFFFFFF`. It
  selects exactly the sites (`pc`) in `sites` where kernel `K` has the unguarded instruction
  `and.b32 d, a, -16777217`. The register `a` must hold an integer `x` below `2 ^ 24` (a
  `.shared::cta` window address of the executing CTA) in a launch with an even cluster size, and
  `d` receives the `.shared::cluster` address of byte `x` of the even CTA of the executing CTA's
  pair (its peer of rank `rank / 2 * 2`, and for the even CTA itself its own byte). Otherwise the
  step faults (`badValue`). A site whose instruction has another form is not affected. The
  constructor sets no `wf` and no `ub`. The statement is generated from the sites and lists every
  site it covers.

Review: The ISA defines no encoding of `.shared::cluster` addresses. It gives `mapa` as the way to
  name a peer CTA's byte, and the model represents such addresses symbolically
  (THREAD-SHARED-POINTER). A 2-SM tensor load in CUTLASS and CuTeDSL instead clears bit 24 of the
  mbarrier's `.shared::cta` address (`and.b32 d, a, -16777217`, mask `0xFEFFFFFF`) so that the
  copies issued by both CTAs of a pair signal the even CTA's mbarrier, which alone expects the
  transaction bytes. This relies on the hardware encoding of `.shared::cluster` addresses: the
  CTA's rank in the cluster from bit 24 up, the byte offset below.
-/

/-- The mask `-16777217` (`0xFEFFFFFF`): every bit but bit 24. -/
def peerBitMask : Int := -16777217

/-- The step of `and.b32 d, a, -16777217` at a selected site: the `.shared::cluster` address of
byte `a` in the even CTA of the pair. -/
noncomputable def execPairEven (L : Launch) (g : Nat) (t : TState) (d a : Nat) : Exec TState := do
  let .bits _ x ← readReg t a | throw .badValue
  let off := (truncBits 32 x).toNat
  let cta := g / L.block
  unless off < 2 ^ 24 ∧ L.clusterSizeOf cta % 2 = 0 do throw .badValue
  let some even := L.peerCta cta (L.rankOfCta cta / 2 * 2) | throw .badValue
  pure (next (setReg t d (.ptr 32 false (.shared cta even) (BitVec.ofNat 64 off))))

/-- `and.b32 d, a, -16777217` at exactly `sites` of kernel `K` names the even CTA's byte; `why`
says why the kernel needs it. -/
noncomputable def pairEvenAt (K : Kernel) (name : String) (sites : List Nat) (why : String) :
    Assumption where
  name := name
  statement := s!"and.b32 d, a, -16777217 with a a .shared::cta address of the executing CTA \
    below 2^24 gives the .shared::cluster address of the same byte in the even CTA of its CTA \
    pair (cluster size even), at exactly these sites: {siteText sites}. {why}"
  segmentRule L g t :=
    if sites.contains t.pc ∧ t.sub = 0 then
      match K.code[t.pc]? with
      | some ⟨none, .int ⟨.and, .int .b 32, false, [some d], [.reg a, .imm m]⟩⟩ =>
        if m = peerBitMask then some (execPairEven L g t d a) else none
      | _ => none
    else none

end PTX.Assumption

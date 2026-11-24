-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaOperands
public import Core.Tc.TcCommitSafety
public import Core.Tc.TcCopy

/-! One computation of the CTA group (§9.7.18.5.1): `Launch.ctaGroup` lists the CTAs of the group
of a CTA by the CTA's rank in its own cluster, and tensor routing (`SameCtaGroup`), `tcgen05.mma`
operands (`makeOperands`, `MatchesLaunch`), `tcgen05.cp` / `tcgen05.shift` and the commit's group
check (`TcCommitIssueSafe`) take the CTAs from it. -/
namespace PTX.Tests.CtaGroup
noncomputable section

private def L : Launch :=
  { grid := 16, block := 128, params := fun _ => none, clusterSize := ⟨8, by decide⟩ }
-- A cluster of three CTAs has no complete pair at its last rank.
private def L3 : Launch :=
  { grid := 6, block := 128, params := fun _ => none, clusterSize := ⟨3, by decide⟩ }

-- cta_group::1 is the CTA itself, cta_group::2 the aligned pair of cluster ranks, the even first.
example : L.ctaGroup 5 .one = some [5] := by decide
example : L.ctaGroup 5 .two = some [4, 5] := by decide
example : L.ctaGroup 4 .two = some [4, 5] := by decide
-- The ranks are relative to the CTA's own cluster.
example : L.ctaGroup 13 .two = some [12, 13] := by decide
example : L.ctaGroup 8 .two = some [8, 9] := by decide
example : L.ctaGroup 10 .one = some [10] := by decide
-- A CTA outside the grid and a pair that is incomplete in its cluster have no group.
example : L.ctaGroup 16 .two = none := by decide
example : L.ctaGroup 16 .one = none := by decide
example : L3.ctaGroup 1 .two = some [0, 1] := by decide
example : L3.ctaGroup 2 .two = none := by decide
example : L3.ctaGroup 2 .one = some [2] := by decide
example : L3.ctaGroup 5 .two = none := by decide

-- `SameCtaGroup` names the same aligned blocks of ranks.
example : SameCtaGroup L .two 4 5 := by unfold SameCtaGroup CtaInCluster; decide
example : SameCtaGroup L .two 13 12 := by unfold SameCtaGroup CtaInCluster; decide
example : ¬ SameCtaGroup L .two 5 6 := by unfold SameCtaGroup CtaInCluster; decide
example : ¬ SameCtaGroup L .two 7 8 := by unfold SameCtaGroup CtaInCluster; decide
example : SameCtaGroup L .one 5 5 := by unfold SameCtaGroup CtaInCluster; decide
example : ¬ SameCtaGroup L .one 4 5 := by unfold SameCtaGroup CtaInCluster; decide
example (a b : Nat) (h : SameCtaGroup L .two a b) :
    L.rankOfCta a / 2 = L.rankOfCta b / 2 := ((sameCtaGroup_iff L .two a b).1 h).2

-- The MMA operand CTAs are the first and the last CTA of the group.
example (issuer : Nat) (d : TcMma.Descriptor) (a b : TcShared.Descriptor)
    (s : TcMma.OperandSpec) (h : TcMma.makeOperands L issuer d a b = some s) :
    s.MatchesLaunch L issuer := by
  unfold TcMma.makeOperands at h
  obtain ⟨ctas, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨lo, hl, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hi, hh, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact ⟨ctas, hc, hl, hh⟩

-- The commit's group check is the existence of the group: the last rank must lie in the cluster.
private theorem hp :
    ∀ r < L3.clusterSizeOf 2, L3.clusterStart (L3.clusterOfCta 2) + r < L3.grid := by
  decide
example : ¬ (L3.rankOfCta 2 / CtaGroup.two.size + 1) * CtaGroup.two.size ≤ L3.clusterSizeOf 2 :=
  fun h => (Launch.ctaGroup_ne_none_iff L3 2 .two (by decide) hp).2 h
    (by decide)
example : (L3.rankOfCta 1 / CtaGroup.two.size + 1) * CtaGroup.two.size ≤ L3.clusterSizeOf 1 := by
  decide

end
end PTX.Tests.CtaGroup

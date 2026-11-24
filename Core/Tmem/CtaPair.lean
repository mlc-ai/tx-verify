-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Cluster

@[expose] public section

namespace PTX

/-! ## PROG-CTA-GROUP — CTA-group identities and tensor completion routing
Statement: A tensor copy from global to shared memory faults unless its shared destination and its
  mbarrier lie in CTAs of the issuer's cluster, both lie in the issuing CTA when the copy uses
  CTA-local addresses, and the mbarrier's CTA is in the same CTA group as the destination's CTA. A
  CTA group is an aligned block of `group.size` cluster ranks: one rank for cta_group::1, an even
  rank and the next odd rank for cta_group::2. `Launch.ctaGroup` lists the CTAs of the group of a
  CTA, and every rule that needs the CTAs of a CTA group (tensor routing, `tcgen05.mma` operands,
  `tcgen05.cp`, `tcgen05.shift` and `tcgen05.commit`) takes them from it. SameCtaGroup includes
  equality. The checks use cluster-relative ranks, including in clusters larger than two.

Defs: CtaInCluster, Launch.ctaGroupRanks, Launch.ctaGroup, SameCtaGroup, sameCtaGroup_iff,
  Launch.ctaGroup_one, Launch.ctaGroup_two, Launch.ctaGroup_ne_none_iff,
  TensorRoute, tensorRouteDecidable

Source:
- §9.7.18.5.1–§9.7.18.5.2 (CTA pair)
- §9.7.10.28.5.3 (shared destination and cta_group completion)

Direction: reading

Applies: Non-multicast global-to-shared tensor copies in the represented 1D cluster topology

Premises: Both locations are shared addresses in the issuer's cluster. CTA-only addressing requires
  both to belong to the issuer. The mbarrier belongs to the destination's CTA group: the destination
  itself for group one, its pair for group two.

Effect: Address ownership checks only. No arrival, completion, visibility or scheduling consequence
  follows from cluster/pair membership.
-/
/-- CTAs `issuer` and `cta` are CTAs of the grid in the same cluster. -/
def CtaInCluster (L : Launch) (issuer cta : Nat) : Prop :=
  issuer < L.grid ∧ cta < L.grid ∧ L.clusterOfCta issuer = L.clusterOfCta cta

/-- The cluster ranks of the CTA group of CTA `cta`: the aligned block of `group.size` ranks that
contains the rank of `cta` in its own cluster. A block has one rank for cta_group::1, and for
cta_group::2 an even rank followed by the next odd rank (a CTA pair, §9.7.18.5.1). The ranks are
relative to the cluster of `cta`, which is a CTA of the 3-D cluster model of the launch. -/
def Launch.ctaGroupRanks (L : Launch) (cta : Nat) (group : CtaGroup) : List Nat :=
  (List.range group.size).map fun k => L.rankOfCta cta / group.size * group.size + k

/-- The CTAs of the CTA group of CTA `cta`, in rank order (the even-rank CTA of a pair first), or
none when a rank of the group has no CTA in the cluster of `cta`. -/
def Launch.ctaGroup (L : Launch) (cta : Nat) (group : CtaGroup) : Option (List Nat) :=
  (L.ctaGroupRanks cta group).mapM (L.peerCta cta)

/-- CTAs `a` and `b` are in the same cluster and in the same CTA group of size `group.size`:
the cluster rank of `b` is one of the ranks of the group of `a`. -/
def SameCtaGroup (L : Launch) (group : CtaGroup) (a b : Nat) : Prop :=
  CtaInCluster L a b ∧ L.rankOfCta b ∈ L.ctaGroupRanks a group

/-- Per-form lemma: `SameCtaGroup` as the equality of the aligned rank blocks of the two CTAs. -/
theorem sameCtaGroup_iff (L : Launch) (group : CtaGroup) (a b : Nat) :
    SameCtaGroup L group a b ↔
      CtaInCluster L a b ∧ L.rankOfCta a / group.size = L.rankOfCta b / group.size := by
  unfold SameCtaGroup Launch.ctaGroupRanks
  cases group <;> simp only [CtaGroup.size, List.mem_map, List.mem_range] <;> constructor
  · rintro ⟨h, k, hk, hr⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, L.rankOfCta b % 1, by omega, by omega⟩
  · rintro ⟨h, k, hk, hr⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, L.rankOfCta b % 2, by omega, by omega⟩

/-- Per-form lemma: the group of a CTA with `cta_group::1` is its own rank. -/
theorem Launch.ctaGroup_one (L : Launch) (cta : Nat) :
    L.ctaGroup cta .one = (L.peerCta cta (L.rankOfCta cta)).map fun p => [p] := by
  have h : L.ctaGroupRanks cta .one = [L.rankOfCta cta] := by
    simp [Launch.ctaGroupRanks, CtaGroup.size]
  unfold Launch.ctaGroup
  rw [h]
  simp only [List.mapM_cons, List.mapM_nil]
  cases L.peerCta cta (L.rankOfCta cta) <;> rfl

/-- Per-form lemma: the group of a CTA with `cta_group::2` is the even rank of its pair and the
next rank. -/
theorem Launch.ctaGroup_two (L : Launch) (cta : Nat) :
    L.ctaGroup cta .two =
      (L.peerCta cta (L.rankOfCta cta / 2 * 2)).bind fun low =>
        (L.peerCta cta (L.rankOfCta cta / 2 * 2 + 1)).bind fun high => some [low, high] := by
  have h : L.ctaGroupRanks cta .two =
      [L.rankOfCta cta / 2 * 2, L.rankOfCta cta / 2 * 2 + 1] := rfl
  unfold Launch.ctaGroup
  rw [h]
  simp only [List.mapM_cons, List.mapM_nil]
  cases L.peerCta cta (L.rankOfCta cta / 2 * 2) <;>
    cases L.peerCta cta (L.rankOfCta cta / 2 * 2 + 1) <;> rfl

/-- Per-form lemma: in a launch whose cluster ranks all name CTAs of the grid, the CTA group of a
CTA of the grid exists exactly when its last rank lies in the cluster (the former
`(rank / size + 1) * size ≤ clusterSize` form of the commit's group check). -/
theorem Launch.ctaGroup_ne_none_iff (L : Launch) (cta : Nat) (group : CtaGroup)
    (hc : cta < L.grid)
    (hp : ∀ r < L.clusterSizeOf cta, L.clusterStart (L.clusterOfCta cta) + r < L.grid) :
    L.ctaGroup cta group ≠ none ↔
      (L.rankOfCta cta / group.size + 1) * group.size ≤ L.clusterSizeOf cta := by
  cases group
  · rw [Launch.ctaGroup_one]
    unfold Launch.peerCta
    have := hp (L.rankOfCta cta)
    simp only [CtaGroup.size, Nat.div_one, Nat.mul_one]
    split_ifs with h
    · simp; omega
    · simp only [Option.map_none, ne_eq, not_true_eq_false, false_iff, not_le]
      by_contra hn
      exact h ⟨hc, by omega, this (by omega)⟩
  · rw [Launch.ctaGroup_two]
    unfold Launch.peerCta
    have h1 := hp (L.rankOfCta cta / 2 * 2)
    have h2 := hp (L.rankOfCta cta / 2 * 2 + 1)
    simp only [CtaGroup.size]
    split_ifs <;> simp <;> omega

/-- The address check of a global-to-shared tensor copy issued by CTA `issuer`: the launch has
valid clusters, the destination and the mbarrier are shared locations in the issuer's cluster, in
the issuer itself when the copy uses CTA-local addresses, and the mbarrier is in the destination's
CTA group. -/
def TensorRoute (L : Launch) (issuer : Nat) (clusterAddress : Bool) (group : CtaGroup)
    (dst mbar : Loc) : Prop :=
  L.clusterGridValid ∧ dst.space = .shared ∧ mbar.space = .shared ∧
  CtaInCluster L issuer dst.cta ∧ CtaInCluster L issuer mbar.cta ∧
  (clusterAddress = false → dst.cta = issuer ∧ mbar.cta = issuer) ∧
  SameCtaGroup L group dst.cta mbar.cta

instance tensorRouteDecidable (L : Launch) (issuer : Nat) (clusterAddress : Bool)
    (group : CtaGroup) (dst mbar : Loc) :
    Decidable (TensorRoute L issuer clusterAddress group dst mbar) := by
  unfold TensorRoute SameCtaGroup CtaInCluster
  infer_instance

end PTX

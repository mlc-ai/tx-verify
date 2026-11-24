-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.CtaPair

@[expose] public section

namespace PTX.TcCommit

/-! ## THREAD-TC-COMMIT-TARGETS — 16-bit multicast target selection
Statement: Bit r of the 16-bit multicast mask of a `tcgen05.commit` selects the mbarrier at the
  addressed shared-memory offset in the CTA of cluster rank r, for every rank of the cluster,
  including ranks outside the issuer's CTA pair. A mask bit at or above the cluster size, or an
  mbarrier address outside the issuer's cluster, makes the issue fault.

Defs: TcCommit.Spec, TcCommit.resolve, TcCommit.target

Source:
- §9.7.18.12.1 (tcgen05.commit multicast masks and same-offset targeting)

Direction: reading

Applies: Full-completion tcgen05.commit; an unmasked commit selects only the addressed rank

Premises: A launched issuer, a shared mbarrier address in its cluster, whole-cluster launch
  topology, and selected mask ranks within the cluster.

Effect: Target addresses; each target has its own notification identity (OBJ-MBAR-ORIGIN) and
  receives its arrival at completion.
-/
/-- The targets of one `tcgen05.commit`: the addressed mbarrier, the multicast mask and the
issuer's cluster. -/
structure Spec where
  /-- The `.cta_group` of the commit. -/
  group : CtaGroup
  /-- The addressed mbarrier, in shared memory of a CTA of the issuer's cluster. -/
  mbar : Loc
  /-- The 16-bit multicast mask; bit `r` selects cluster rank `r`. -/
  mask : BitVec 16
  /-- The CTA number of rank 0 of the issuer's cluster. -/
  clusterBase : Nat
  /-- The number of CTAs in the cluster. -/
  clusterSize : Nat
  deriving DecidableEq, Repr

/-- The target specification of a commit issued by CTA `issuer`; `none` when the mbarrier is not
in shared memory of a CTA of the issuer's cluster or the mask selects a rank outside the
cluster. -/
def resolve (L : Launch) (group : CtaGroup) (issuer : Nat) (mbar : Loc) (mask : BitVec 16) :
    Option Spec :=
  if L.clusterGridValid ∧ issuer < L.grid ∧ mbar.space = .shared ∧ mbar.cta < L.grid ∧
      L.clusterOfCta mbar.cta = L.clusterOfCta issuer ∧ mask.toNat < 2 ^ L.clusterSizeOf issuer then
    some ⟨group, mbar, mask, L.clusterStart (L.clusterOfCta issuer), L.clusterSizeOf issuer⟩
  else none

/-- The mbarrier that cluster rank `rank` receives an arrive-on at: the offset of the addressed
mbarrier in that rank's CTA, when the rank's mask bit is set. -/
def target (s : Spec) (rank : Fin 16) : Option Loc :=
  if rank.val < s.clusterSize ∧ s.mask.toNat / 2 ^ rank.val % 2 = 1 then
    some ⟨.shared, s.clusterBase + rank.val, s.mbar.addr⟩
  else none

end PTX.TcCommit

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairHistory
public import Core.Memory.Order

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

/-! ## OBJ-TMEM-PUBLICATION — a paired allocation published through the peer warp
Statement: An allocation whose request is paired with a cta_group::2 allocation of the peer CTA is
  published to an event when an event of the peer CTA's paired request happens before that event.
  This publication adds no edge to base causality order (`baseCausality`).

Defs: Tmem.Pair.PairAllocBefore

Source:
- §9.7.18.7.1 (collective `cta_group::2` allocation)
- EXT-PAIR-ALLOC-ORDER

Direction: trust

Applies: Allocations of a CTA whose request is paired (`Execution.tmemPairing`) with a
  `tcgen05.alloc.cta_group::2` request of the peer CTA

Premises: An event of the paired peer request happens before the access.

Effect: `PairAllocBefore` is the peer route of the one coverage relation `Covers`
  (OBJ-TMEM-LIFETIME), which every Tensor Memory rule uses.

### EXT-PAIR-ALLOC-ORDER — a paired allocation is complete when the peer warp's returns

Statement: When one warp of each CTA of a pair performs a paired `tcgen05.alloc.cta_group::2`, the
  model takes the allocation of each CTA to be complete, and usable by the Tensor Memory accesses of
  either CTA, before the instruction returns in the peer warp. The allocation of a CTA therefore
  covers an access when an event of the peer warp's paired allocation happens before the access.

Source:
- §9.7.18.7.1: "When .cta_group::2 is specified, one warp from each of the peer CTAs must
    collectively perform the allocation and de-allocation."
- §9.7.18.7.1: "The mandatory .sync qualifier indicates that the instruction causes the executing
    thread to wait until all threads in the warp execute the same instruction before resuming
    execution."

Why it is not spec text: The text makes the two warps perform the allocation collectively. It does
  not state that the peer CTA's half has completed when the instruction returns in a warp, nor that
  the peer's allocation is then ordered before the warp's later Tensor Memory accesses of the peer's
  cells. Without the reading, coverage requires publication from the cell's own CTA's allocation
  event. The peer needs of the pair (DEP-TMEM-ALLOC-WAIT) enter the dependency order
  (DEP-ORDER) and add nothing to `baseCausality`.

Direction: trust

Effect: In the model, a CTA's allocation record whose request is paired (`Execution.tmemPairing`)
  with a request of the peer CTA covers an access when an event of the peer warp's allocation
  happens before the access (`PairAllocBefore`, a disjunct of `Covers`). Every use of coverage
  takes this route: the allocated-before-access conjunct and the release conjunct of `AccessSafe`
  (ERR-TMEM-ACCESS-LIFETIME), the fresh-lifetime check (`FreshAfter`) and the source-liveness check
  (`TcMma.SourceLive`). A record covering an access only through its peer is still subject to the
  release check. Disclosed by every kernel whose statement names
  `Op.tcAlloc (group := CtaGroup.two)`: FlashAttn4Fwd, Fp16Gemm8192.
-/

/-- EXT-PAIR-ALLOC-ORDER: the request of record `r` is paired with a request of the peer CTA, and
an event of that request happens before `e`. -/
def PairAllocBefore (L : Launch) (X : Execution) (r : Requests) (e : EvId) : Prop :=
  ∃ q ∈ X.tmemPairing, ∃ p, ((q.1 = r.own ∧ q.2 = p) ∨ (q.2 = r.own ∧ q.1 = p)) ∧
    ∃ lane, baseCausality L X (p.event L lane) e

/-! ## OBJ-TMEM-LIFETIME — allocation coverage and first release attempts
Statement: An allocation covers a column of its own CTA within its range for every event that the
  allocation event happens before, or, for an allocation paired with a cta_group::2 allocation of
  the peer CTA, that an event of the peer's paired request happens before. A later allocation of the
  same cell starts a fresh lifetime for an access when a release attempt happens before it and it
  covers the access. A release attempt of an allocation is the first matching deallocation after it
  in a lane of the allocating warp, any matching deallocation by another warp of its CTA, or, for a
  paired cta_group::2 allocation, a release attempt of the peer CTA's allocation of the same
  operation.

Defs: Tmem.Pair.Covers, Tmem.Pair.Covers.own, Tmem.Pair.Covers.paired, Tmem.Pair.FreshAfter,
  Tmem.Pair.OwnRelease, Tmem.Pair.ReleaseOf

Source:
- §9.7.18.1.2 (allocation before access)
- §9.7.18.7.1 (collective release and repeated allocations)
- §9.7.18.5 Table 55: "Issue from a single warp in the current CTA would initiate the allocation
    management instruction."
- OBJ-TMEM-PUBLICATION
- EXT-PAIR-ALLOC-ORDER

Direction: trust

Applies: Allocations of either cta_group performed by their CTA's allocator, and whole-allocation
  release attempts

Premises: Each CTA has its own column range. Coverage is at the accessed cell's physical CTA, which
  need not be the accessor's for a group-2 operation, and requires publication to the access from
  the allocation event or, for a paired allocation, from the peer's paired request
  (EXT-PAIR-ALLOC-ORDER). This is the one coverage relation of the model. A release attempt of an
  allocation is the first matching attempt after it in a lane of its warp, a matching deallocation
  by a thread of another warp of its CTA (any warp may issue the release), or, for a paired
  cta_group::2 allocation, a release attempt of the peer CTA's allocation of the same operation.

Effect: These relations connect allocator histories to access safety and source-lifetime checks.
  Memory contents are published by MEM-MODEL-CAUSALITY and asynchronous completion by
  DEP-TC-COMPLETION-CLOSURE.
-/
/-- Record `r` is an allocation of CTA `owner` whose column range contains `col`, published to
`e`: lane 0's allocation event happens before `e`, or the record is paired and an event of the
peer's paired request happens before `e` (EXT-PAIR-ALLOC-ORDER). -/
def Covers (L : Launch) (X : Execution) (r : Requests) (owner : Nat) (e : EvId) (col : Nat) :
    Prop :=
  ∃ n base, r.action = .alloc n base ∧ owner = r.own.cta ∧ base ≤ col ∧ col < base + n ∧
    (baseCausality L X (r.own.event L 0) e ∨ PairAllocBefore L X r e)

/-- Coverage through the allocation's own event (the former own-only `Covers`). -/
theorem Covers.own {L : Launch} {X : Execution} {r : Requests} {owner : Nat} {e : EvId}
    {col : Nat} (h : ∃ n base, r.action = .alloc n base ∧ owner = r.own.cta ∧
      base ≤ col ∧ col < base + n ∧ baseCausality L X (r.own.event L 0) e) :
    Covers L X r owner e col :=
  let ⟨n, base, ha, ho, hl, hu, hh⟩ := h
  ⟨n, base, ha, ho, hl, hu, .inl hh⟩

/-- Coverage through the paired peer allocation (the former `CoversPaired`). -/
theorem Covers.paired {L : Launch} {X : Execution} {r : Requests} {owner : Nat} {e : EvId}
    {col : Nat} (h : ∃ n base, r.action = .alloc n base ∧ owner = r.own.cta ∧
      base ≤ col ∧ col < base + n ∧ PairAllocBefore L X r e) :
    Covers L X r owner e col :=
  let ⟨n, base, ha, ho, hl, hu, hp⟩ := h
  ⟨n, base, ha, ho, hl, hu, .inr hp⟩

/-- Release attempt `d` is followed by a fresh lifetime of the cell for access `e`: some
allocation covers the cell for `e`, and `d` happens before that allocation's event. -/
def FreshAfter (L : Launch) (X : Execution) (d e : EvId) (owner col : Nat) : Prop :=
  ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r owner e col ∧ baseCausality L X d (r.own.event L 0)

/-- A release attempt of the allocation of record `r` by its own CTA: the first matching
deallocation in a lane of its warp after it, or a matching deallocation by another warp of its
CTA. It need not yet have been performed. -/
def OwnRelease (L : Launch) (X : Execution) (r : Requests) (d : EvId) : Prop :=
  ∃ n base pc,
    r.action = .alloc n base ∧
    (∃ group, X.get d = some ⟨pc, .tc (.resource group none (.dealloc base n))⟩) ∧
    ((∃ lane, d.1 = (r.own.event L lane).1 ∧ r.own.indices lane < d.2 ∧
      ∀ f pc' group, X.get f = some ⟨pc', .tc (.resource group none (.dealloc base n))⟩ →
        f.1 = d.1 → r.own.indices lane < f.2 → d.2 ≤ f.2) ∨
     (d.1 / L.block = r.own.cta ∧ d.1 % L.block / 32 ≠ r.own.warp))

/-- A release attempt of the allocation of `r`: its own, or that of the peer CTA's record of a
paired operation. -/
def ReleaseOf (L : Launch) (X : Execution) (r : Requests) (d : EvId) : Prop :=
  OwnRelease L X r d ∨ ∃ q ∈ X.tmemPairing, ∃ s, s ∈ X.tmemHistory s.own.cta ∧
    ((q.1 = r.own ∧ q.2 = s.own) ∨ (q.2 = r.own ∧ q.1 = s.own)) ∧ OwnRelease L X s d

end
end PTX.Tmem.Pair

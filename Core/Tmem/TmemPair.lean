-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemObject

@[expose] public section

namespace PTX.Tmem.Pair

/-! ## OBJ-TMEM-PAIR — collective resource operations of a CTA group
Statement: The two warp requests of a cta_group::2 allocation-management operation, one in each CTA
  of the pair, are of the same kind, and for an allocation or a deallocation they name the same
  column count. The Tensor Memory addresses of the two deallocations may differ. Each CTA's
  allocator performs its own warp's request, at its own address and lifetime, in the execution order
  within that CTA (OBJ-TMEM-ORDER), and the operation completes when the allocators of both
  CTAs have performed it.

Defs: Tmem.Pair.compatible

Source:
- §9.7.18.5 (collective issue, potentially blocking deallocation)
- §9.7.18.7.1: "When .cta_group::1 is specified, one warp from the CTA must perform the allocation
    and de-allocation. When .cta_group::2 is specified, one warp from each of the peer CTAs must
    collectively perform the allocation and de-allocation."
- §9.7.18.7.1: "The number of columns allocated must not increase between any two allocations in the
    execution order within the CTA."

Direction: reading

Applies: Non-exclusive allocations, whole-allocation releases and permit relinquishment of a CTA
  group: one CTA for cta_group::1, an even/odd CTA pair for cta_group::2

Premises: An execution adapter supplies actual warp requests of every CTA of the group and proves
  their agreement. Local resource validity is checked by Tmem.perform.

Effect: Request agreement; OBJ-TMEM-HISTORY and OBJ-TMEM-ORIGIN connect allocator
  records and pairings to executions.

Review: The model keeps the two CTAs' addresses independent and assumes nothing about the two
  allocation results. Access completion before release is a separate safety obligation.
-/

/-- The two requests of a cta_group::2 operation agree: both allocate the same column count,
both deallocate the same column count, or both relinquish the permit. The deallocation addresses
are not compared, since each CTA has its own allocation result. -/
def compatible : Tmem.Request → Tmem.Request → Bool
  | .alloc n, .alloc m | .dealloc _ n, .dealloc _ m => n == m
  | .relinquish, .relinquish => true
  | _, _ => false

end PTX.Tmem.Pair

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Value
public import Core.Tmem.TmemPair

@[expose] public section

namespace PTX.Tmem.Pair

/-! ## OBJ-TMEM-REQUEST — warp instruction instances and allocator records
Statement: A Tensor Memory allocation-management instruction is recorded as one warp request, which
  names the CTA, warp, the trace position of each lane and the request. The allocator of each CTA
  records the requests it served with the action it took, and the two warp requests of a
  `cta_group::2` operation are paired separately.

Defs: Tmem.Pair.WarpRequest, Tmem.Pair.WarpRequest.event, Tmem.Pair.Requests

Source:
- none (representation)

Direction: representation

Applies: Allocator records of one CTA and the pairing of the two warp requests of a cta_group::2
  operation

Premises: None; actual participants and operation agreement are checked by OBJ-TMEM-REQUESTS
  and OBJ-TMEM-ORIGIN.

Effect: Data only.
-/
/-- One warp-collective allocation-management instruction instance (`tcgen05.alloc`,
`dealloc` or `relinquish_alloc_permit`): its CTA, warp, the trace position of each lane, the
source position, the destination of an allocation's address, and the request. -/
structure WarpRequest where
  cta : Nat
  warp : Nat
  indices : Fin 32 → Nat
  pc : Nat
  dst : Option Loc
  request : Tmem.Request

def WarpRequest.event (L : Launch) (w : WarpRequest) (lane : Fin 32) : Nat × Nat :=
  (w.cta * L.block + w.warp * 32 + lane.val, w.indices lane)

/-- One operation performed by a CTA's allocator: the CTA's warp request, its group, and the
action performed for it. -/
structure Requests where
  own : WarpRequest
  group : CtaGroup
  action : Tmem.Action

end PTX.Tmem.Pair

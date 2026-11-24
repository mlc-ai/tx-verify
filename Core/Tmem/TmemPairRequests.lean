-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

/-! ## OBJ-TMEM-REQUESTS — actual warp participants of a resource operation
Statement: Each allocation-management operation that an allocator records is issued by one full warp
  of the CTA, whose 32 lanes execute one warp-collective instance of the same instruction with the
  same operands, and the record performs that request. The two warps of a cta_group::2 operation are
  in the two distinct CTAs of one CTA pair of a valid cluster launch, the even-ranked CTA first, and
  their requests agree. Each side of a pair keeps its own source position, warp index, local address
  and trace indices.

Defs: Tmem.Pair.WarpRequest.Valid, Tmem.Pair.Requests.Valid, Tmem.Pair.PairValid

Source:
- §9.7.18.5 (one warp per peer CTA)
- §9.7.18.7.1 (.sync/.aligned and operands)

Direction: stricter

Applies: Actual allocation-management events of one complete warp per CTA of the group

Premises: Each warp's 32 lane instances exist, are the same warp-collective instance
  (DEP-TC-COLLECTIVE), agree on source instruction and request, and belong to that CTA. An
  allocator record's action performs its warp's request. A pairing's two warp requests are of
  distinct peer CTAs of one CTA pair in a valid cluster launch, the first of the even CTA, with
  compatible requests.

Effect: An execution-adapter component.

Review: Local address agreement across a warp is the represented sufficient scope. Cross-CTA warp
  indices and local addresses need not agree. The allocator orders (OBJ-TMEM-ORDER) enforce
  per-warp order and the absence of a repeated record.
-/
/-- Warp request `w` is an actual instruction instance of group `group`: the CTA and warp exist
in the launch, every lane's event at its trace index is that instruction with the request's
operands, and the 32 lane events form one warp-collective instance. -/
def WarpRequest.Valid (L : Launch) (X : Execution) (group : CtaGroup) (w : WarpRequest) : Prop :=
  w.cta < L.grid ∧ (w.warp + 1) * 32 ≤ L.block ∧
    (∀ lane, X.get (w.event L lane) = some ⟨w.pc, .tc (.resource group w.dst w.request)⟩) ∧
    ∃ k, ∀ lane, X.TcK (w.event L lane) k

/-- Allocator record `r` is valid: the launch has valid clusters, its action performs its warp's
request, and that warp request is an actual instance of the record's group. -/
def Requests.Valid (L : Launch) (X : Execution) (r : Requests) : Prop :=
  L.clusterGridValid ∧ r.action.request = r.own.request ∧ r.own.Valid L X r.group

/-- The two warp requests of a cta_group::2 operation are valid: both are actual cta_group::2
instances, of the two distinct CTAs of one CTA pair with the even-ranked CTA's first, and their
requests agree (`compatible`). -/
def PairValid (L : Launch) (X : Execution) (q : WarpRequest × WarpRequest) : Prop :=
  L.clusterGridValid ∧ q.1.Valid L X .two ∧ q.2.Valid L X .two ∧
    SameCtaGroup L .two q.1.cta q.2.cta ∧ q.1.cta ≠ q.2.cta ∧ L.rankOfCta q.1.cta % 2 = 0 ∧
    compatible q.1.request q.2.request = true

end
end PTX.Tmem.Pair

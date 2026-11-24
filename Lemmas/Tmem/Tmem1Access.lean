-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.Tmem1Protocol

@[expose] public section

/-!
# The Tensor Memory access branch of `Unsafe` for a `cta_group::1` allocation

A proof tool, generic over the kernel (ERR-TMEM-ACCESS-LIFETIME; the generic part of Inkling's
`Proof/Protocol/TmemAccess.lean`). With the allocation of `Tmem1Facts` (warp `w` of each CTA
allocates all 512 columns, relinquishes, and deallocates), `Tmem.Pair.AccessSafe` reduces to three
facts about the kernel's accesses:

* `hacc`: an access is a launched thread's, of a cell of its own CTA below column 512;
* `halloc`: lane 0 of warp `w` of the access's CTA allocated before it (in base causality) and went
  on after the allocation (so the allocation is complete and recorded);
* `hdone`: an access completes before every deallocation of its CTA (`TcMma.CompletedBefore`: a
  load or store by its thread's wait, an MMA, copy or shift by an observed commit).

From them (`no_access_unsafe`):

* **allocated** (`access_allocated`): the recorded allocation covers the cell (it is at column 0
  with 512 columns, `alloc_zero`);
* **released** (`release_info`): a release attempt of a recorded allocation is a deallocation of
  the allocation's CTA, since the operations are `cta_group::1` and no pairing releases them. -/

namespace PTX.Tmem.One
open PTX PTX.Proof Tmem.Pair TcMma

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {w : Nat}

/-- **An access with a completed allocation of its CTA before it is allocated**: the allocation of
lane 0 of warp `w` of the cell's CTA, complete since the thread went on, is a record of the CTA's
history at column 0 with 512 columns, and covers every column below 512. -/
theorem access_allocated (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {e : EvId}
    {cell : Cell} {j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat}
    (hal : X.get (cell.cta * L.block + w * 32, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hlen : j + 1 < (X.tr (cell.cta * L.block + w * 32)).length)
    (hhb : baseCausality L X (cell.cta * L.block + w * 32, j) e) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  have hcov := hX.tmemPairBlocking.covered ⟨pc, _, _, _, hal, trivial⟩ hlen
  obtain ⟨r, hr, hri⟩ := covered_record hX ht hcov
  obtain ⟨hcta, hw0, -⟩ := record_info hX ht hr
  have hwi : r.own.event L 0 = (cell.cta * L.block + w * 32, j) := by
    simp [WarpRequest.event, hw0, hcta, hri]
  obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc n base := by
    obtain ⟨-, -, -, hreq, -⟩ := record_info hX ht hr
    have hev := ((hX.tmemPair.1 _).1 r hr).2.2.2.2.1 0
    rw [hwi, hal] at hev
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hev
    exact Tmem.Action.request_eq_alloc (hreq.trans hev.2.2.2.symm)
  obtain ⟨rfl, rfl⟩ := alloc_zero hX ht hr _ _ hwa
  refine ⟨cell.cta, r, hr, Covers.own ⟨512, 0, hwa, hcta.symm, Nat.zero_le _, by omega, ?_⟩⟩
  rw [hwi]
  exact hhb

/-- The owner of a covering allocation is its record's CTA. -/
theorem covers_owner {r : Requests} {owner : Nat} {e : EvId} {col : Nat}
    (h : Covers L X r owner e col) : owner = r.own.cta :=
  let ⟨_, _, _, ho, _⟩ := h
  ho

/-- **A release attempt of a recorded allocation is a deallocation of its CTA**: the operations
are `cta_group::1`, so no pairing releases them. -/
theorem release_info (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {cta : Nat}
    {r : Requests} (hr : r ∈ X.tmemHistory cta) {d : EvId} (hrel : ReleaseOf L X r d) :
    (∃ pc grp a n, X.get d = some ⟨pc, .tc (.resource grp none (.dealloc a n))⟩) ∧
      d.1 / L.block = cta := by
  obtain ⟨hlc, hlw, hlg, -⟩ := record_info hX ht hr
  rcases hrel with ⟨n, base, pc, -, ⟨grp, hget⟩, hlane⟩ | ⟨q, hq, s, hs, hpair, -⟩
  · refine ⟨⟨pc, grp, base, n, hget⟩, ?_⟩
    rcases hlane with ⟨lane, hd1, -⟩ | ⟨h, -⟩
    · have hl := WarpRequest.event_props ((hX.tmemPair.1 cta).1 r hr).2.2 lane
      rw [hd1]
      exact hl.1.trans hlc
    · rw [h, hlc]
  · exfalso
    obtain ⟨-, ⟨a, ha, ha1, ha2⟩, b, hb, hb1, hb2⟩ := hX.tmemPair.2.1 q hq
    obtain ⟨-, -, hg, -⟩ := record_info hX ht ha
    rw [hg] at ha2
    cases ha2

/-- **No Tensor Memory access is unallocated or outlives its allocation**
(ERR-TMEM-ACCESS-LIFETIME, `cta_group::1`). -/
theorem no_access_unsafe (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w)
    (hacc : ∀ {e : EvId} {cell : Cell}, Access L X e cell →
      e.1 < L.threads ∧ cell.cta = e.1 / L.block ∧ cell.column < 512)
    (halloc : ∀ {e : EvId} {cell : Cell}, Access L X e cell → ∃ j pc grp dst n,
      X.get (cell.cta * L.block + w * 32, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr (cell.cta * L.block + w * 32)).length ∧
      baseCausality L X (cell.cta * L.block + w * 32, j) e)
    (hdone : ∀ {e : EvId} {cell : Cell} {d : EvId} {pc a n : Nat} {grp : CtaGroup},
      Access L X e cell → X.get d = some ⟨pc, .tc (.resource grp none (.dealloc a n))⟩ →
      d.1 / L.block = e.1 / L.block → TcMma.CompletedBefore L X e d) :
    ¬ AccessUnsafe L X := by
  refine fun hn => hn fun e cell ha => ?_
  obtain ⟨-, hc, hcol⟩ := hacc ha
  obtain ⟨j, pc, grp, dst, n, hal, hlen, hhb⟩ := halloc ha
  refine ⟨access_allocated hX ht hal hlen hhb hcol, fun cta r hr hcov d hrel => ?_⟩
  obtain ⟨⟨pc, grp, a, n, hd⟩, hdc⟩ := release_info hX ht hr hrel
  have hown := covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX ht hr
  exact .inl (hdone ha hd (by rw [hdc, ← hlc, ← hown, hc]))

end
end PTX.Tmem.One

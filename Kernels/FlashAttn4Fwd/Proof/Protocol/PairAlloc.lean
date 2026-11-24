-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAlloc

@[expose] public section

/-! # The paired allocation covers the peer CTA's cells

The leader CTA's MMAs write and read cells of the odd CTA, whose allocation event nothing orders
before them. The reading EXT-PAIR-ALLOC-ORDER covers such an access by the odd CTA's allocation
through the paired allocation of the accessing thread's CTA (`Tmem.Pair.Covers.paired`):

* lane 0 of warp 12 of the accessing thread's CTA allocates before the access and goes on past
  the allocation (`TmemLife.allocAt`), so its allocation is covered (DEP-TMEM-ALLOC-WAIT): it
  is a request of a pairing, whose other request is recorded in the history of the other CTA of
  the pair (`HistoriesOk`), the cell's CTA;
* both requests are allocations (their requests are compatible); the recorded allocation is of
  all 512 columns at column 0 (`alloc_zero`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof Tmem.Pair

noncomputable section

namespace PairAlloc

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The other request of a pairing covers its CTA's cells**: the record of request `s`, paired
with the allocation request `p` an event of which happens before `e`, covers every cell of the
first 512 columns of `s`'s CTA for `e` through the pairing. -/
theorem covers_of_pair (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) {q : WarpRequest × WarpRequest}
    (hq : q ∈ X.tmemPairing) {p s : WarpRequest} (hps : (q.1 = s ∧ q.2 = p) ∨ (q.2 = s ∧ q.1 = p))
    (hcomp : compatible p.request s.request = true) {n : Nat} (hpn : p.request = .alloc n)
    {r : Requests} (hr : r ∈ X.tmemHistory s.cta)
    (hrs : r.own = s) {e : EvId} {lane : Fin 32} (hhb : baseCausality L X (p.event L lane) e)
    {cell : TcMma.Cell} (hc : cell.cta = s.cta) (hcol : cell.column < 512) :
    Covers L X r cell.cta e cell.column := by
  have hto := TmemAlloc.warpOps hpre htm
  obtain ⟨m, hsn⟩ : ∃ m, s.request = .alloc m := by
    rw [hpn] at hcomp
    cases hs : s.request <;> simp_all [compatible]
  obtain ⟨-, -, -, hreq, -⟩ := record_info hX hto hr
  rw [hrs, hsn] at hreq
  obtain ⟨c, hac⟩ := Tmem.Action.request_eq_alloc hreq
  obtain ⟨rfl, rfl⟩ := alloc_zero hX hto hr _ _ hac
  refine Covers.paired ⟨512, 0, hac, by rw [hc, hrs], Nat.zero_le _, by omega, q, hq, p, ?_,
    lane, hhb⟩
  rw [hrs]
  exact hps

/-- **A peer cell is covered through the paired allocation**: if lane 0 of warp 12 of CTA `c`
allocates before `e` and goes on past the allocation, then every cell of the first 512 columns
of the other CTA of `c`'s pair is covered for `e` by that CTA's allocation, through the
pairing. -/
theorem coversPeer (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) {e : EvId} {c j pc n : Nat}
    {grp : CtaGroup} {dst : Option Loc}
    (hal : X.get (TmemAlloc.lane0 L c, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hlen : j + 1 < (X.tr (TmemAlloc.lane0 L c)).length)
    (hhb : baseCausality L X (TmemAlloc.lane0 L c, j) e) {cell : TcMma.Cell}
    (hpair : cell.cta / 2 = c / 2) (hne : cell.cta ≠ c) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  have hto := TmemAlloc.warpOps hpre htm
  have hblock := hpre.block
  obtain ⟨ws, hws, w, hw, lane, hl⟩ :=
    hX.tmemPairBlocking.covered ⟨pc, _, _, _, hal, trivial⟩ hlen
  rcases hws with ⟨k, x, hx, hg, rfl⟩ | ⟨q, hq, rfl⟩
  · rw [List.mem_singleton.mp hw] at hl
    obtain ⟨-, -, hg2, -⟩ := record_info hX hto hx
    rw [hg] at hg2
    cases hg2
  obtain ⟨hv, ⟨a, ha, ha1, -⟩, b, hbm, hb1, -⟩ := hX.tmemPair.2.1 q hq
  obtain ⟨-, hv1, hv2, ⟨⟨-, -, hcl⟩, -⟩, hne12, -, hcomp⟩ := hv
  have hq12 : q.1.cta / 2 = q.2.cta / 2 := by
    simpa only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster] using hcl
  -- the participating request is of CTA `c`, its event that of `hal`
  have hwc : ∀ {v : WarpRequest}, v.Valid L X .two → v.event L lane = (TmemAlloc.lane0 L c, j) →
      v.cta = c ∧ v.request = .alloc n := by
    intro v hvv hvl
    have h1 := (WarpRequest.event_props hvv lane).1
    rw [hvl] at h1
    have he := hvv.2.2.1 lane
    rw [hvl, hal] at he
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at he
    refine ⟨?_, he.2.2.2.symm⟩
    rw [← h1]
    simp only [TmemAlloc.lane0]
    rw [hblock]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · obtain ⟨hc1, hn1⟩ := hwc hv1 hl
    have hcs : cell.cta = q.2.cta := by omega
    have hcomp' : compatible q.1.request q.2.request = true := hcomp
    exact ⟨q.2.cta, b, hbm, covers_of_pair hpre hX htm hq (.inr ⟨rfl, rfl⟩) hcomp' hn1 hbm hb1
      (by rw [hl]; exact hhb) hcs hcol⟩
  · obtain ⟨hc2, hn2⟩ := hwc hv2 hl
    have hcs : cell.cta = q.1.cta := by omega
    have hcomp' : compatible q.2.request q.1.request = true := by
      rw [hn2] at hcomp ⊢
      cases h1 : q.1.request <;> simp_all [compatible]
    exact ⟨q.1.cta, a, ha, covers_of_pair hpre hX htm hq (.inl ⟨rfl, rfl⟩) hcomp' hn2 ha ha1
      (by rw [hl]; exact hhb) hcs hcol⟩

end PairAlloc

end
end PTX.Kernels.FlashAttn4Fwd.Proof

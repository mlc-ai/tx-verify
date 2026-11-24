-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.Tmem1Protocol

@[expose] public section

/-! # The Tensor Memory access class for one allocating warp (`cta_group::1`)

Generic over the kernel and the allocating warp `w` (Inkling's `Protocol/TmemAccess.lean` with the
warp as a parameter; a candidate for `Lemmas/Tmem/`): every Tensor Memory access is inside a
completed allocation of its CTA and completes before every release attempt of that allocation
(`Tmem.Pair.AccessSafe`), when

* `AccessInfo`: every access is a launched thread's MMA, `tcgen05.ld` or `tcgen05.st`, of a cell
  of its own CTA below column 512, and no `tcgen05.cp` or `tcgen05.shift` is issued;
* `Life w`: every access follows, in causality, an allocation by lane 0 of warp `w` of its CTA
  that has an event after it (`alloc_before`), and every load or store is finished by its
  thread's `wait` before every deallocation of its CTA (`ldst_before_dealloc`);
* `MmaDoneDealloc`: every MMA is done before every deallocation of its CTA;
* `Tmem.One.Tmem1Facts L X w`: warp `w`'s three operations on column 0.

* **Allocated** (`access_allocated`): the allocation is complete, so recorded in the CTA's
  history (`covered_record`), of 512 columns at column 0 (`alloc_zero`): it covers every column
  below 512.
* **Released** (`release_info`): a release attempt of a recorded allocation is a deallocation of
  the CTA's warp `w`.
* `no_access_unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tmem1
open PTX AsyncCopy Tmem.Pair TcMma Tmem.One

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {w : Nat}

/-- An MMA issue. -/
def IsMma (X : Execution) (i : EvId) : Prop := ∃ d s acc mask, X.MmaIssue i d s acc mask

/-- **AccessInfo**: every Tensor Memory access is a launched thread's MMA, load or store, of a cell
of its own CTA in the first 512 columns, and no `tcgen05.cp` or `tcgen05.shift` is issued. -/
def AccessInfo (L : Launch) (X : Execution) : Prop :=
  (∀ {e : EvId} {cell : Cell}, Access L X e cell →
    e.1 < L.threads ∧ cell.cta = e.1 / L.block ∧ cell.column < 512 ∧
      (IsMma X e ∨ (∃ a vals sh, X.TLd e a vals sh) ∨ ∃ a vals sh, X.TSt e a vals sh)) ∧
  (∀ i c, ¬ X.CpIssue i c) ∧ (∀ i s, ¬ X.ShiftIssue i s)

/-- **The lifetime orders of the allocation of warp `w`.** -/
structure Life (L : Launch) (X : Execution) (w : Nat) : Prop where
  /-- Every MMA, `tcgen05.ld` and `tcgen05.st` of a thread of CTA `c` follows an allocation by
  lane 0 of warp `w` of the CTA, in causality, and that lane has an event after it. -/
  alloc_before : ∀ {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape},
    (IsMma X e ∨ X.TLd e a vals sh ∨ X.TSt e a vals sh) →
      ∃ j pc grp dst n, X.get ((e.1 / L.block) * L.block + w * 32, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block + w * 32)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block + w * 32, j) e
  /-- Every `tcgen05.ld` (`tcgen05.st`) of a CTA is finished, by the thread's `wait::ld`
  (`wait::st`), before every deallocation of the CTA, in causality. -/
  ldst_before_dealloc : ∀ {e d : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {pc : Nat}
      {grp : CtaGroup} {dst : Option Loc} {da n : Nat},
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩ →
      (d.1 / L.block) = (e.1 / L.block) →
      (X.TLd e a vals sh → WaitBefore L X .waitLd e d) ∧
      (X.TSt e a vals sh → WaitBefore L X .waitSt e d)

/-- **MmaDoneDealloc**: every MMA is done before every deallocation of its CTA. -/
def MmaDoneDealloc (L : Launch) (X : Execution) : Prop :=
  ∀ {i d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}, IsMma X i →
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
    d.1 / L.block = i.1 / L.block → DoneBefore L X i d

/-- **An access of a cell of its thread's CTA, below column 512, is allocated.** -/
theorem access_allocated (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w)
    (hl : Life L X w) {e : EvId} {cell : Cell}
    (hk : IsMma X e ∨ (∃ a vals sh, X.TLd e a vals sh) ∨ ∃ a vals sh, X.TSt e a vals sh)
    (hc : cell.cta = e.1 / L.block) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  have hto := ht.toTmem1Ops
  obtain ⟨j, pc, grp, dst, n, hal, hlen, hhb⟩ : ∃ j pc grp dst n,
      X.get ((e.1 / L.block) * L.block + w * 32, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block + w * 32)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block + w * 32, j) e := by
    rcases hk with hm | ⟨a, vals, sh, hld⟩ | ⟨a, vals, sh, hst⟩
    · exact hl.alloc_before (a := 0) (vals := []) (sh := .s32x32b) (.inl hm)
    · exact hl.alloc_before (.inr (.inl hld))
    · exact hl.alloc_before (.inr (.inr hst))
  have hcov := hX.tmemPairBlocking.covered ⟨pc, _, _, _, hal, trivial⟩ hlen
  obtain ⟨r, hr, hri⟩ := covered_record hX hto hcov
  obtain ⟨hcta, hw0, -⟩ := record_info hX hto hr
  have hwi : r.own.event L 0 = ((e.1 / L.block) * L.block + w * 32, j) := by
    simp [WarpRequest.event, hw0, hcta, hri]
  obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc n base := by
    obtain ⟨-, -, -, hreq, -⟩ := record_info hX hto hr
    have hev := ((hX.tmemPair.1 _).1 r hr).2.2.2.2.1 0
    rw [hwi, hal] at hev
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hev
    exact Tmem.Action.request_eq_alloc (hreq.trans hev.2.2.2.symm)
  obtain ⟨rfl, rfl⟩ := alloc_zero hX hto hr _ _ hwa
  refine ⟨e.1 / L.block, r, hr, Covers.own ⟨512, 0, hwa, ?_, Nat.zero_le _, by omega, ?_⟩⟩
  · rw [hc, hcta]
  · rw [hwi]
    exact hhb

/-- The owner of a covering allocation is its record's CTA. -/
theorem covers_owner {r : Requests} {owner : Nat} {e : EvId} {col : Nat}
    (h : Covers L X r owner e col) : owner = r.own.cta :=
  let ⟨_, _, _, ho, _⟩ := h
  ho

/-- **A release attempt of a recorded allocation is a deallocation of its CTA's warp `w`**: the
operations are `cta_group::1`, so no pairing releases them. -/
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

/-- **No Tensor Memory access is unallocated or outlives its allocation.** -/
theorem no_access_unsafe (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w)
    (hinfo : AccessInfo L X) (hl : Life L X w) (hmd : MmaDoneDealloc L X) :
    ¬ AccessUnsafe L X := by
  obtain ⟨hacc, hno_cp, hno_shift⟩ := hinfo
  refine fun hn => hn fun e cell ha => ?_
  obtain ⟨he, hc, hcol, hk⟩ := hacc ha
  refine ⟨access_allocated hX ht hl hk hc hcol, fun cta r hr hcov d hrel => ?_⟩
  obtain ⟨⟨pc, grp, a, n, hd⟩, hdc⟩ := release_info hX ht.toTmem1Ops hr hrel
  have hown := covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX ht.toTmem1Ops hr
  have hcell : d.1 / L.block = e.1 / L.block := by rw [hdc, ← hlc, ← hown, hc]
  refine .inl ⟨fun ⟨a', vals, sh, hld⟩ => ?_, fun ⟨a', vals, sh, hst⟩ => ?_, fun hasync => ?_⟩
  · exact (hl.ldst_before_dealloc hd hcell).1 hld
  · exact (hl.ldst_before_dealloc hd hcell).2 hst
  · rcases hasync with hm | ⟨c, hcp⟩ | ⟨s, hsh⟩
    · exact hmd hm hd hcell
    · exact (hno_cp _ _ hcp).elim
    · exact (hno_shift _ _ hsh).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tmem1

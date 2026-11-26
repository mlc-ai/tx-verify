-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.AccessClass

@[expose] public section

/-! # The Tensor Memory access class for one allocating warp, with copies

The variant of `Lemmas/Tmem/AccessClass.lean` for a kernel that issues `tcgen05.cp`: a copy is an
access like an MMA (its cells in its CTA, allocated before it, done by an observed commit before
every deallocation of its CTA). Every Tensor Memory access is inside a completed allocation of its
CTA and completes before every release attempt of that allocation (`no_access_unsafe_cp`), when

* `AccessInfoCp`: every access is a launched thread's MMA, copy, `tcgen05.ld` or `tcgen05.st`,
  of a cell of its own CTA below column 512, and no `tcgen05.shift` is issued;
* `LifeCp w`: every access follows, in causality, an allocation by lane 0 of warp `w` of its CTA
  with an event after it, and every load or store is finished by its thread's `wait` before every
  deallocation of its CTA;
* `AsyncDoneDealloc`: every MMA and copy is done before every deallocation of its CTA;
* `Tmem.One.Tmem1Facts L X w`.

`allocated_of_before` is `Access.access_allocated` from the allocation order of the one access. -/

namespace PTX.Tmem.AccessCp
open PTX AsyncCopy Tmem.Pair TcMma Tmem.One Tmem.Access

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {w : Nat}

/-- An access of the class: an MMA, a copy, a `tcgen05.ld` or a `tcgen05.st`. -/
def Op (X : Execution) (e : EvId) : Prop :=
  IsMma X e ∨ (∃ c, X.CpIssue e c) ∨ (∃ a vals sh, X.TLd e a vals sh) ∨
    ∃ a vals sh, X.TSt e a vals sh

/-- **AccessInfoCp**: every Tensor Memory access is a launched thread's MMA, copy, load or store,
of a cell of its own CTA in the first 512 columns, and no `tcgen05.shift` is issued. -/
def AccessInfoCp (L : Launch) (X : Execution) : Prop :=
  (∀ {e : EvId} {cell : Cell}, Access L X e cell →
    e.1 < L.threads ∧ cell.cta = e.1 / L.block ∧ cell.column < 512 ∧ Op X e) ∧
  (∀ i s, ¬ X.ShiftIssue i s)

/-- **The lifetime orders of the allocation of warp `w`**, copies included. -/
structure LifeCp (L : Launch) (X : Execution) (w : Nat) : Prop where
  /-- Every access of a thread of CTA `c` follows an allocation by lane 0 of warp `w` of the CTA,
  in causality, and that lane has an event after it. -/
  alloc_before : ∀ {e : EvId}, Op X e →
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

/-- **AsyncDoneDealloc**: every MMA and copy is done before every deallocation of its CTA. -/
def AsyncDoneDealloc (L : Launch) (X : Execution) : Prop :=
  ∀ {i d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc},
    (IsMma X i ∨ ∃ c, X.CpIssue i c) →
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
    d.1 / L.block = i.1 / L.block → DoneBefore L X i d

/-- **An access after an allocation of its CTA's warp `w`, of a cell of its thread's CTA below
column 512, is allocated.** -/
theorem allocated_of_before (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w) {e : EvId}
    {cell : Cell} {j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat}
    (hal : X.get ((e.1 / L.block) * L.block + w * 32, j) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hlen : j + 1 < (X.tr ((e.1 / L.block) * L.block + w * 32)).length)
    (hhb : baseCausality L X ((e.1 / L.block) * L.block + w * 32, j) e)
    (hc : cell.cta = e.1 / L.block) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  have hto := ht.toTmem1Ops
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

/-- **No Tensor Memory access is unallocated or outlives its allocation**, copies included. -/
theorem no_access_unsafe_cp (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X w)
    (hinfo : AccessInfoCp L X) (hl : LifeCp L X w) (hmd : AsyncDoneDealloc L X) :
    ¬ AccessUnsafe L X := by
  obtain ⟨hacc, hno_shift⟩ := hinfo
  refine fun hn => hn fun e cell ha => ?_
  obtain ⟨-, hc, hcol, hk⟩ := hacc ha
  obtain ⟨j, pc, grp, dst, n, hal, hlen, hhb⟩ := hl.alloc_before hk
  refine ⟨allocated_of_before hX ht hal hlen hhb hc hcol, fun cta r hr hcov d hrel => ?_⟩
  obtain ⟨⟨pc, grp, a, n, hd⟩, hdc⟩ := release_info hX ht.toTmem1Ops hr hrel
  have hown := covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX ht.toTmem1Ops hr
  have hcell : d.1 / L.block = e.1 / L.block := by rw [hdc, ← hlc, ← hown, hc]
  refine .inl ⟨fun ⟨a', vals, sh, hld⟩ => ?_, fun ⟨a', vals, sh, hst⟩ => ?_, fun hasync => ?_⟩
  · exact (hl.ldst_before_dealloc hd hcell).1 hld
  · exact (hl.ldst_before_dealloc hd hcell).2 hst
  · rcases hasync with hm | hcp | ⟨s, hsh⟩
    · exact hmd (.inl hm) hd hcell
    · exact hmd (.inr hcp) hd hcell
    · exact (hno_shift _ _ hsh).elim

end
end PTX.Tmem.AccessCp

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.TmemAlloc
public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemLife

@[expose] public section

/-!
# The Tensor Memory access branch of `Unsafe` (`cta_group::1`)

`Safety.Protocol.tmemAccess`: every Tensor Memory access is inside a completed allocation of its
CTA and completes before every release attempt of that allocation (`Tmem.Pair.AccessSafe`). The
kernel's accesses are the MMAs' result, accumulator and A cells, and the `tcgen05.ld` and
`tcgen05.st` registers; it has no `tcgen05.cp` and no `tcgen05.shift`.

* **Allocated** (`access_allocated`): `SO.TmemLife.alloc_before` gives lane 0 of warp 0 of the
  access's CTA an allocation before the access (in causality) and an event after it; the allocation
  is complete, so recorded in the CTA's history (`covered_record`), of 512 columns at column 0
  (`alloc_zero`), and it covers every column below 512.
* **Released** (`release_info`): a release attempt of a recorded allocation is a deallocation of
  the CTA's warp 0, since the operations are `cta_group::1` and no pairing releases them.
* **Complete** (`no_access_unsafe`): a load or store is finished by its thread's `wait` before the
  deallocation (`TmemLife.ldst_before_dealloc`), an MMA by an observed commit
  (`MmaDoneDealloc`, `SO.mma_done_before_dealloc`).

Premises: `AccessInfo` (the classification of every access: a launched thread's, of a cell of its
own CTA below column 512 (`SOTmemCols`, `tm = 0`), and of the three kinds; the kernel has no
`tcgen05.cp` or `shift`), `SO.TmemLife` (the named-barrier chains of the allocation's lifetime) and
`MmaDoneDealloc`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX PTX.Proof PTX.Flow AsyncCopy Tmem.Pair TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma TmemLife)

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **AccessInfo**: every Tensor Memory access is a launched thread's MMA, load or store, of a cell
of its own CTA in the first 512 columns, and no `tcgen05.cp` or `tcgen05.shift` is issued. -/
def AccessInfo (L : Launch) (X : Execution) : Prop :=
  (∀ {e : EvId} {cell : Cell}, Access L X e cell →
    e.1 < L.threads ∧ cell.cta = e.1 / L.block ∧ cell.column < 512 ∧
      (IsMma X e ∨ (∃ a vals sh, X.TLd e a vals sh) ∨ ∃ a vals sh, X.TSt e a vals sh)) ∧
  (∀ i c, ¬ X.CpIssue i c) ∧ (∀ i s, ¬ X.ShiftIssue i s)

/-- **MmaDoneDealloc**: every MMA is done before every deallocation of its CTA
(`SO.mma_done_before_dealloc`, from the epilogue's poll of `o_final`). -/
def MmaDoneDealloc (L : Launch) (X : Execution) : Prop :=
  ∀ {i d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}, IsMma X i →
    X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
    d.1 / L.block = i.1 / L.block → DoneBefore L X i d

/-- **The MMA warp of CTA `c` and its `o_final` commit** (the inputs of `SO.f_doneBefore_at`, with
the MMA warp's MMAs restricted to its own CTA: with more than one CTA no thread issues all MMAs). -/
def OFinalFacts (L : Launch) (X : Execution) (c : Nat) : Prop :=
  ∃ cm p0, SO.Facts L X c cm p0 ∧ cm < L.threads ∧ cm / L.block = c ∧
    (∀ {x : EvId}, IsMma X x → x.1 / L.block = c → x.1 = cm) ∧
    (∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c →
        ((X.tr cm).take i).countP (commitsTo (EvW.oFinal L c)) = 0) ∧
    (∀ {x : EvId}, IsMma X x → x.1 / L.block = c → ∀ {i pc : Nat} {sp : TcCommit.Spec},
      X.get (cm, i) = some ⟨pc, .tc (.commit sp)⟩ → sp.mbar = EvW.oFinal L c → x.2 < i)

/-- **Every MMA of a CTA is done before every deallocation of the CTA**: the epilogue's poll of
`o_final` observes the MMA warp's only commit to it (`SO.mma_done_before_dealloc`, with the MMA
warp's MMAs restricted to its CTA), and the poll is before the deallocation (`TmemLife`). The
premise `hpoll` is that the deallocation follows a successful poll of `o_final` of its CTA, in
the program order of the deallocating thread. -/
theorem mmaDoneDealloc_of (hX : Consistent L K A mem0 X) (hl : TmemLife L X)
    (F : ∀ c < L.grid, OFinalFacts L X c)
    (hpoll : ∀ {d : EvId} {pc a n : Nat} {grp : CtaGroup} {dst : Option Loc},
      X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩ →
      ∃ h j pc' p sc, h < L.threads ∧ h / L.block = d.1 / L.block ∧
        X.get (h, j) = some ⟨pc', .wait (EvW.oFinal L (d.1 / L.block)) p true true sc⟩) :
    MmaDoneDealloc L X := by
  intro i d pc a n grp dst hi hd hdc
  obtain ⟨pci, di, si, acci, maski, hgeti⟩ := hi.get
  have hcl : i.1 / L.block < L.grid := by
    have := Frame.lt_of_get hX hgeti
    unfold Launch.threads at this
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at this)
  obtain ⟨cm, p0, Fa, hcm, hcmc, hone, hcommit, hbefore⟩ := F (i.1 / L.block) hcl
  obtain ⟨h, j, pc', p, sc, hh, hhc, he⟩ := hpoll hd
  rw [hdc] at hhc he
  have hbc := hl.dealloc_after_epilogue hd (by rw [hhc, hdc]) he
  exact SO.mma_done_before_dealloc hX Fa hone hcommit hbefore ⟨hcm, hh, by rw [hcmc, hhc]⟩ he hi
    rfl hbc

/-- The lane-0 thread of warp 0 of CTA `cta`. -/
theorem lane0_eq (L : Launch) (cta : Nat) : cta * L.block + 0 * 32 = cta * L.block := by simp

/-- **An access of a cell of its thread's CTA, below column 512, is allocated.** -/
theorem access_allocated (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X 0)
    (hl : TmemLife L X) {e : EvId} {cell : Cell}
    (hk : IsMma X e ∨ (∃ a vals sh, X.TLd e a vals sh) ∨ ∃ a vals sh, X.TSt e a vals sh)
    (hc : cell.cta = e.1 / L.block) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  have hto := ht.toTmem1Ops
  obtain ⟨j, pc, grp, dst, n, hal, hlen, hhb⟩ : ∃ j pc grp dst n,
      X.get ((e.1 / L.block) * L.block, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block, j) e := by
    rcases hk with hm | ⟨a, vals, sh, hld⟩ | ⟨a, vals, sh, hst⟩
    · exact hl.alloc_before (a := 0) (vals := []) (sh := .s32x32b) (.inl hm)
    · exact hl.alloc_before (.inr (.inl hld))
    · exact hl.alloc_before (.inr (.inr hst))
  have hcov := hX.tmemPairBlocking.covered ⟨pc, _, _, _, hal, trivial⟩ hlen
  rw [← lane0_eq L (e.1 / L.block)] at hcov
  obtain ⟨r, hr, hri⟩ := covered_record hX hto hcov
  obtain ⟨hcta, hw0, -⟩ := record_info hX hto hr
  have hwi : r.own.event L 0 = ((e.1 / L.block) * L.block, j) := by
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

/-- **A release attempt of a recorded allocation is a deallocation of its CTA's warp 0**: the
operations are `cta_group::1`, so no pairing releases them. -/
theorem release_info (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X 0) {cta : Nat}
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
(`Safety.Protocol.tmemAccess`). -/
theorem no_access_unsafe (hX : Consistent L K A mem0 X) (ht : Tmem1Facts L X 0)
    (hinfo : AccessInfo L X) (hl : TmemLife L X) (hmd : MmaDoneDealloc L X) :
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
end PTX.Kernels.InklingRelDecode.Proof.Tmem1

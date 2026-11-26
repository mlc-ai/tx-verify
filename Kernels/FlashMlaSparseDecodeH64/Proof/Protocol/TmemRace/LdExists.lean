-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCells

@[expose] public section

/-! # A Tensor Memory load of warpgroup 0 has a write before it

A score load (columns `[400, 464)`, 32 registers) of block `r` polled the commit of block `r` to
`qkDone`, which follows the block's first QK MMA (`mma_qkMmas`); the MMA is done before the
load (`ld_second`). A QK MMA writes every cell of lanes below 128 of these columns
(`qk_writeCell`). A rescale load (block `r ≥ 1`, `wg0_ldPlace`) of columns `[0, 256)` is after the
same commit, which follows both first PV MMAs of block `r - 1`, one per half of the columns
(`pv_writeCell`). An output load polled `svDone` at pc 1184, which observes the lane's last PV
commit, after the same MMAs (`mma_svMmas`, `done_after_svPoll`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section
set_option maxRecDepth 4000

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **A QK MMA writes every cell of the score columns** of its CTA, below lane 128. -/
theorem qk_write_of {y x pcx : Nat} {sx : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {cell : TcMma.Cell}
    (hx : X.get (y, x) = some ⟨pcx, .tc (.mma 400 sx acc mask)⟩) (hcta : cell.cta = y / L.block)
    (hl : cell.lane < 128) (h1 : 400 ≤ cell.column) (h2 : cell.column < 464) :
    TcMma.TmemWrite L X (y, x) cell := by
  have hgx := Frame.lt_of_get hX hx
  rcases tc_role (tmem_rows hp hX hFw) hgx hx rfl with ⟨-, hW⟩ | ⟨-, hMm⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hMm with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
        ⟨_, _, k, -, -, h, -, hops⟩
    · cases h
    · cases h
    · cases h
    · obtain ⟨hlo, -⟩ := ops_cta hp hgx (.inl rfl) hops
      simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
      obtain ⟨-, rfl, -, rfl⟩ := h
      obtain ⟨row, col, hw⟩ := TmemRow.qk_writeCell hops (by rw [hlo]; exact hcta) hl h1 h2
      exact .inl ⟨_, _, _, _, row, col, ⟨pcx, hx⟩, hw⟩
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
      have := h.1
      omega
  · cases hc'

/-- **A PV MMA with D at `128 kk` writes every cell of its half of the PV columns** of its CTA,
below lane 128. -/
theorem pv_write_of {y x pcx kk : Nat} {sx : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {cell : TcMma.Cell} (hkk : kk < 2)
    (hx : X.get (y, x) = some ⟨pcx, .tc (.mma (128 * kk) sx acc mask)⟩)
    (hcta : cell.cta = y / L.block) (hl : cell.lane < 128) (h1 : 128 * kk ≤ cell.column)
    (h2 : cell.column < 128 * kk + 128) : TcMma.TmemWrite L X (y, x) cell := by
  have hgx := Frame.lt_of_get hX hx
  rcases tc_role (tmem_rows hp hX hFw) hgx hx rfl with ⟨-, hW⟩ | ⟨-, hMm⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hMm with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
        ⟨_, _, k, -, -, h, -, hops⟩
    · cases h
    · cases h
    · cases h
    · simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
      have := h.1
      omega
    · obtain ⟨hlo, -⟩ := ops_cta hp hgx (.inr rfl) hops
      simp only [Kind.tc.injEq, TcKind.mma.injEq] at h
      obtain ⟨-, rfl, -, rfl⟩ := h
      obtain ⟨row, col, hw⟩ := TmemRow.pv_writeCell hops hkk (by rw [hlo]; exact hcta) hl h1 h2
      exact .inl ⟨_, _, _, _, row, col, ⟨pcx, hx⟩, hw⟩
  · cases hc'

section
variable (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **A load that polled `qkDone` for use `r / 2` saw the commit of that use**: the lane's commit
with `r / 2` earlier commits to the slot. -/
theorem ld_qkCommit {h k r : Nat} (hw : warp L h < 4)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r))) ((X.tr h).take k)) :
    ∃ ic pcc sp, X.get (mmaLane L X (h / L.block), ic) = some ⟨pcc, .tc (.commit sp)⟩ ∧
      sp.mbar = mbarLoc L (h / L.block) (.qkDone (slot2 r)) ∧
      ((X.tr (mmaLane L X (h / L.block))).take ic).countP
        (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) = r / 2 := by
  obtain ⟨b', hbq⟩ := wg0_lane hp (pc := 103) ⟨hw, by omega, by omega⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = h / L.block := ⟨_, rfl⟩
  rw [← hcd] at hbq hpol ⊢
  obtain ⟨j, pcp, p, acq, sc, hjk, hget, hq⟩ := UnitHandoff.exists_poll hpol
  have O := qkDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c (slot2 r)
  rw [hbq] at hget hq
  obtain ⟨ic, pcc, sp, rank, hcom, hmb, -, hcnt, -, -⟩ :=
    O.observes hX (u := r / 2) (qkReach hp hX hFw hR hI hB c (slot2 r) b') hget hq
  exact ⟨ic, pcc, sp, hcom, hmb, hcnt⟩

/-- **A load of warpgroup 0 has a write of each of its cells before it.** -/
theorem ld_write (hN : DequantInputs L X) {e : EvId} {a : Nat}
    {vals : List Value} {sh : TcShape} {j : Nat} {cell : TcMma.Cell}
    (hld : X.TLd e a vals sh) (hj : j < vals.length) (hc : cell = tcDataCell L e.1 sh a j) :
    ∃ w, TcMma.TmemWrite L X w cell ∧ TcMma.WriteBefore L X w e := by
  obtain ⟨h, k⟩ := e
  obtain ⟨pc, he⟩ := hld
  obtain ⟨hat, hsh, ha, hcls⟩ := ld_class hp hX hFw he
  subst hsh
  have hlen := ldLen hp hX he rfl
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha (j := j)
  rw [← hc] at hcta hlane hcol
  have hl128 : cell.lane < 128 := by
    have hw4 := hat.1
    unfold MbarRow.warp at hw4
    rw [tidOf_x_eq hp h] at hw4
    omega
  have hkl : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hpoll1 : ∀ r, (∀ j : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone j))
      ((X.tr h).take k) = ringUses 2 j (r + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady j))
        ((X.tr h).take k) = ringUses 2 j r) →
      r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r))) ((X.tr h).take k) :=
    fun r hr => by
      have := (hr (slot2 r)).1
      simp only [slot2, ringUses] at this ⊢
      omega
  rcases wg0_ldPlace hp hX hFw he hat with ⟨r, h1r, h32, hr⟩ | ⟨hlt, jw, p, hjw, hpoll⟩
  · have hpol := hpoll1 r hr
    obtain ⟨ic, pcc, sp, hcom, hmb, hcnt⟩ := ld_qkCommit hp hX hFw hR hI hB hat.1 hpol
    obtain ⟨hcy, -⟩ := mma_qkBlock hp hX hFw hcom hmb
    obtain ⟨r', hs, hall, hqk, hpv⟩ := mma_qkMmas hp hX hFw hcom hmb
    have hrr : r = r' := by
      have h1 := congrArg Fin.val hs
      simp only [slot2] at h1
      omega
    subst hrr
    have hmono : ∀ i, i ≤ ic → ((X.tr (mmaLane L X (h / L.block))).take i).countP
        (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) ≤ r / 2 :=
      fun i hi => hcnt ▸ countP_take_mono _ _ hi
    by_cases hscore : 400 ≤ a
    · obtain ⟨x, hxi, pcx, sx, acc, mask, hx, -⟩ := hqk
      have hlen32 := h32 hscore
      have hcol' : 400 ≤ cell.column ∧ cell.column < 464 := by
        rcases hcls with ⟨h1, h2⟩ | h1
        · omega
        · omega
      refine ⟨_, qk_write_of hp hX hFw hx (hcta.trans hcy) hl128 hcol'.1 hcol'.2, .inl (.inl ?_)⟩
      exact ld_second hp hX hFw hR hI hB hx he hat rfl hcy.symm (hmono x hxi.le) hpol
    · have hr1 := h1r (by omega)
      obtain ⟨x, hxi, pcx, sx, acc, mask, hx, -⟩ :=
        hpv hr1 (cell.column / 128) (by omega)
      refine ⟨_, pv_write_of hp hX hFw (by omega) hx (hcta.trans hcy) hl128 (by omega)
        (by omega), .inl (.inl ?_)⟩
      exact ld_second hp hX hFw hR hI hB hx he hat rfl hcy.symm (hmono x hxi.le) hpol
  · have hy4 := hat.1
    obtain ⟨-, ic, pci, spi, rank, hgc, hmi, -⟩ := svDone_last hp hX hFw hR hI hB hN hy4 hpoll
    obtain ⟨hcy, -⟩ := mma_svBlock hp hX hFw hgc hmi
    obtain ⟨x, hxi, pcx, sx, acc, mask, hx, -⟩ := mma_svMmas hp hX hFw hgc hmi (cell.column / 128)
      (by omega)
    refine ⟨_, pv_write_of hp hX hFw (by omega) hx (hcta.trans hcy) hl128 (by omega)
      (by omega), .inl (.inl ?_)⟩
    exact done_after_svPoll hp hX hFw hR hI hB hN hx (.inl ⟨_, _, _, _, rfl⟩) hcy hat.1
      hpoll hjw hkl

end

end

end TmRace

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

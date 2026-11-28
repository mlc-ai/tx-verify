-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdCommit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.QkSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkPrev

@[expose] public section

/-! # A score load of warpgroup 0 reads QK MMA 15 of its block

A load of warpgroup 0 of block `r` at a score column (`400 ≤ a`) has `r / 2 + 1` successful polls of
`qkDone (r % 2)`, which observe the commit of block `r` (`qk_commit_poll`): the lane's QK MMA 15 of
the block is before the commit, so done before the load (`ld_second`). A QK MMA of a later block
is ordered after the load's wait (`ld_first`). The source of a load register is the latest write
ordered before the load (`ReadSource`): it cannot be an earlier QK MMA of the block (QK MMA 15 is
a later write before the load) nor a later one. So it is QK MMA 15 of block `r` (`ld_pin`). -/

/-! # The QK MMAs of a lane write the same cells

Every QK MMA of the MMA lane has the same descriptor and CTA group (`MmaOps`), so a cell written by
one is written by all of them: the result cell of output `(row, col)` is the same.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A cell of one QK MMA is a cell of every QK MMA of the lane.** -/
theorem qk_cell_shared (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) {g i j pc pc' : Nat} {s s' : TcMma.OperandSpec} {a a' : Bool}
    {mask mask' : List Nat} {cell : TcMma.Cell}
    (hi : X.get (g, i) = some ⟨pc, .tc (.mma 400 s a mask)⟩)
    (hj : X.get (g, j) = some ⟨pc', .tc (.mma 400 s' a' mask')⟩)
    (hm : X.MmaCell (g, i) cell) : X.MmaCell (g, j) cell := by
  obtain ⟨d, s0, a0, mask0, row, col, ⟨pcx, hx⟩, hc⟩ := hm
  rw [hi] at hx
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hx
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hx
  have hg := Frame.lt_of_get hX hi
  obtain ⟨ki, -, -, -, -, -, hopsi⟩ := qk_pc hT hX hi
  obtain ⟨kj, -, -, -, hmj, -, hopsj⟩ := qk_pc hT hX hj
  have hdd : s.descriptor = s'.descriptor := by
    obtain ⟨-, hd1, -⟩ := hopsi
    obtain ⟨-, hd2, -⟩ := hopsj
    exact Option.some.inj (hd1.symm.trans hd2)
  obtain ⟨hl, hh⟩ := ops_cta hp hg (.inl rfl) hopsi
  obtain ⟨hl', hh'⟩ := ops_cta hp hg (.inl rfl) hopsj
  have hcell : TcMma.resultCell s' 400 row col = some cell := by
    have hr := TcMma.writeCell_resultCell hc
    rw [← hr]
    unfold TcMma.resultCell
    rw [hdd, hl.trans hl'.symm, hh.trans hh'.symm]
  exact ⟨400, s', a', mask', row, col, ⟨_, hj⟩, hmj ▸
    writeCell_zeroMask (ops_group (.inl rfl) hopsj) (ops_m64 (.inl rfl) hopsj) hcell⟩

/-- **An earlier QK MMA of the lane is a write ordered before a later one.** -/
theorem qk_writeBefore (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) {g i j pc pc' : Nat} {s s' : TcMma.OperandSpec} {a a' : Bool}
    {mask mask' : List Nat}
    (hi : X.get (g, i) = some ⟨pc, .tc (.mma 400 s a mask)⟩)
    (hj : X.get (g, j) = some ⟨pc', .tc (.mma 400 s' a' mask')⟩) (hij : i < j) :
    TcMma.WriteBefore L X (g, i) (g, j) := by
  have hg := Frame.lt_of_get hX hi
  obtain ⟨ki, -, -, -, -, -, hopsi⟩ := qk_pc hT hX hi
  obtain ⟨kj, -, -, -, -, -, hopsj⟩ := qk_pc hT hX hj
  have hdd : s.descriptor = s'.descriptor := by
    obtain ⟨-, hd1, -⟩ := hopsi
    obtain ⟨-, hd2, -⟩ := hopsj
    exact Option.some.inj (hd1.symm.trans hd2)
  obtain ⟨hl, hh⟩ := ops_cta hp hg (.inl rfl) hopsi
  obtain ⟨hl', hh'⟩ := ops_cta hp hg (.inl rfl) hopsj
  exact .inl (TcMma.Before.of_mma_po ⟨_, hi⟩ ⟨_, hj⟩ hg rfl hij
    ⟨rfl, by rw [hdd], by rw [hdd], by rw [hl, hl'], by rw [hh, hh']⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem qkPc_inj {k k' : Nat} (h : TmemRow.qkPc k = TmemRow.qkPc k') : k = k' := by
  simp only [TmemRow.qkPc] at h
  split_ifs at h <;> omega

private theorem ru_after {r t : Nat} (h : r < t) : r / 2 + 1 ≤ ringUses 2 (r % 2) t := by
  unfold ringUses; omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **The pin of a score load**: the source of a register of a warpgroup-0 load at a score column
is QK MMA 15 of the load's block `r` (the `24 r + 15`-th MMA issue of the MMA lane), done. -/
theorem ld_pin (hG : SyncGuarded L kernel X)
    {h k pc a j : Nat} {vals : List Value} {sh : TcShape} {src : EvId} {cell : TcMma.Cell}
    (he : X.get (h, k) = some ⟨pc, .tc (.ld a vals sh)⟩) (hat : Wg0At L h pc) (ha : 400 ≤ a)
    (hj : j < vals.length) (hcell : cell = tcDataCell L h sh a j)
    (hs : TcMma.ReadSource L X .ld src (h, k) cell) :
    ∃ r, (∀ b : Fin 2, okPolls (mbarLoc L (h / L.block) (.qkDone b)) ((X.tr h).take k) =
        ringUses 2 b.val (r + 1) ∧ arrivals (mbarLoc L (h / L.block) (.soReady b))
        ((X.tr h).take k) = ringUses 2 b.val r) ∧
      ∃ i sx mask, src = (mmaLane L X (h / L.block), i) ∧
        X.get src = some ⟨TmemRow.qkPc 15, .tc (.mma 400 sx true mask)⟩ ∧
        mmaIssues ((X.tr (mmaLane L X (h / L.block))).take i) = 24 * r + 15 ∧
        X.async.mmaDone src = true ∧ X.MmaCell src cell := by
  obtain ⟨hat', hsh, ha', -⟩ := ld_class hp hX hFw he
  subst hsh
  have hT := tmem_rows hp hX hFw
  obtain ⟨hcta, hlane, hcol⟩ := dataCell hp hat.1 ha' (j := j)
  rw [← hcell] at hcta hlane hcol
  obtain ⟨hcw, -⟩ := writer_cases hp hX hT hs.2.1
  obtain ⟨gs, is, ks, pcs, ss, as, masks, hsrc, hks, hpcs, hget, -⟩ :=
    qk_writer hp hX hT hs.2.1 (by omega)
  subst hsrc
  subst hpcs
  obtain ⟨kq, hkq, hpcq, has, -, hon, -⟩ := qk_pc hT hX hget
  have hxc : gs / L.block = h / L.block := hcw.symm.trans hcta
  have hg : gs = mmaLane L X (h / L.block) := by
    rw [← hxc]
    exact laneOn_eq (mmaOne hp hX hFw) hget (fun _ h => by cases h) hon
  have hsk := ld_src_kind hp hX hFw ⟨pc, he⟩ hj hcell hs
  obtain ⟨hmc, hdone⟩ : X.MmaCell (gs, is) cell ∧ X.async.mmaDone (gs, is) = true := by
    rcases hsk with hm | ⟨a', vals', sh', jj, ⟨pcs, hst⟩, -⟩
    · exact hm
    · cases get_tc_inj hget hst
  obtain ⟨r, -, -, hr⟩ | ⟨hlt, -⟩ := wg0_ldPlace hp hX hFw he hat
  swap
  · omega
  refine ⟨r, hr, ?_⟩
  have hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r)))
      ((X.tr h).take k) := by
    rw [(hr (slot2 r)).1]
    simp only [slot2]
    unfold ringUses
    omega
  obtain ⟨ic, pcc, sp, hcom, hmb, hcnt, hrb, hn, xM, hxi, pcx, sx, accx, maskx, hM, hatM, hcM⟩ :=
    qk_commit_poll hp hX hFw hR hI hB hat.1 hpol
  subst hg
  have hdoneM : TcMma.DoneBefore L X (mmaLane L X (h / L.block), xM) (h, k) :=
    ld_second hp hX hFw hR hI hB hM he hat rfl hxc
      (hcnt ▸ countP_take_mono _ _ hxi.le) hpol
  have hMw : TcMma.TmemWrite L X (mmaLane L X (h / L.block), xM) cell :=
    .inl (qk_cell_shared hp hX hT hget hM hmc)
  obtain ⟨-, -, -, hlat, -⟩ := TcMma.readSource_ld.mp hs
  have hisx : is = xM := by
    rcases Nat.lt_trichotomy is xM with hlt | heq | hgt
    · exfalso
      have hB1 := qk_writeBefore hp hX hT hget hM hlt
      rcases hlat _ hMw with h1 | h1 | h1 | ⟨-, -, -, a2, v2, s2, pc2, hst⟩
      · exact absurd (congrArg Prod.snd h1) (by simp only; omega)
      · exact TcMma.tcStep_asymm hX hG hB1.tcStep h1.tcStep
      · exact TcMma.tcStep_asymm hX hG hdoneM.tcStep h1.tcStep
      · cases get_tc_inj hM hst
    · exact heq
    · exfalso
      obtain ⟨kM, hkM, hpcM, -⟩ := qk_pc hT hX hM
      obtain ⟨d, k', hk', hcnS, hpolS⟩ := mma_qkAt hp hX hFw hget hon.1
      rw [hxc] at hpolS
      have hlt := mmaIssues_lt hM (by
        subst hpcM
        simp only [TmemRow.qkPc]
        split <;> omega) hgt
      have hrd : r < d := by omega
      have hwait := ld_first hp hX hFw hR hI hB he hat rfl hxc
        (List.getElem?_eq_some_iff.mp hget).1
        (by rw [(hpolS (slot2 r)).1]; exact ru_after hrd)
        (by rw [(hr (slot2 r)).2]; simp only [slot2]; unfold ringUses; omega)
      exact TcMma.tcStep_asymm hX hG hs.2.2.1.tcStep hwait.tcStep
  subst hisx
  obtain ⟨r0, hr0⟩ := mma_qkCount hp hX hFw hget hks
  obtain rfl : ks = 15 := by omega
  obtain rfl := qkPc_inj hpcq
  refine ⟨is, ss, masks, rfl, ?_, hcM, hdone, hmc⟩
  rw [hget, has]
  rfl

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

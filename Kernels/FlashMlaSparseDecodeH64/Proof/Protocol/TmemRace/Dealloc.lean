-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.SyncId
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Reads
public import Lemmas.Tmem.AccessCp
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar12
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.LdWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Block
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.StageOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SvPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # The deallocation follows every Tensor Memory access of its CTA

The deallocation (pc 1840) is warp 0 of warpgroup 0's, after its barrier-12 event (pc 1835,
`wg0_deallocBar12`). Every load and store belongs to a lane of warpgroup 0 with no barrier-12
event before it (`wg0_ldstBar12`), and the lane makes its barrier-12 event (it arrives, or exits
after one, `wg0_exitBar12`); its `wait::ld` (`wg0_ldWait`) or `wait::st` (`wg0_stWait`) lies
before that event. Barrier 12's first generation (`barId_arrive`) orders that event's lane's
earlier events before the deallocation (`dealloc_ldst`): the wait is `WaitBefore` it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : BarRows P L X)
include hp hX hFw hR

omit hR in
/-- A load or a store is warpgroup 0's. -/
private theorem ldst_wg0 {y k pc : Nat} {c : TcKind} (he : X.get (y, k) = some ⟨pc, .tc c⟩)
    (hc : (∃ a vals sh, c = .ld a vals sh) ∨ ∃ a vals sh, c = .st a vals sh) :
    MbarRow.Wg0At L y pc := by
  have hg := Frame.lt_of_get hX he
  rcases tc_role (tmem_rows hp hX hFw) hg he rfl with ⟨hat, -⟩ | ⟨-, hM⟩ | ⟨_, _, _, hc'⟩
  · exact hat
  · exfalso
    rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, -, -, h, -⟩ |
      ⟨_, _, _, -, -, h, -⟩ <;> cases h <;> rcases hc with ⟨_, _, _, h'⟩ | ⟨_, _, _, h'⟩ <;>
      cases h'
  · exfalso
    rcases hc with ⟨_, _, _, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h' <;> cases hc'

/-- **The barrier-12 event of a lane of warpgroup 0 is before the deallocation**: a lane of the
CTA's warpgroup 0 has a barrier-12 event, with none before it, and each earlier event of the lane
is before the deallocation. -/
private theorem bar12_before {y h kd pc : Nat} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request}
    (hd : X.get (h, kd) = some ⟨pc, .tc (.resource grp dst act)⟩)
    (hat : MbarRow.Wg0At L h pc) (hy : MbarRow.warp L y < 4) (hs : SameCta L y h) :
    ∃ i' pc', X.get (y, i') = some ⟨pc', .bar 12 none .sync⟩ ∧
      ((X.tr y).take i').countP (Execution.isBarId 12) = 0 ∧
      ∀ i, i < i' → baseCausality L X (y, i) (h, kd) := by
  have hmem : barIn 12 ((y % L.block) / 32) = true := by
    simp only [MbarRow.warp, tidOf_x_eq hp] at hy
    simp only [barIn]
    norm_num
    rw [hp.block]
    omega
  have hkd : kd < (X.tr h).length := (List.getElem?_eq_some_iff.mp hd).1
  have hlt := wg0_deallocBar12 hp hX hFw hd hat rfl
  obtain ⟨i', pc', hget, hcnt, hcaus⟩ := barId_arrive hp hX hR hs hmem hkd (n := 0) (by omega)
    fun ⟨j, pcx, hx⟩ => wg0_exitBar12 hp hX hFw hy hx
  exact ⟨i', pc', hget, hcnt, hcaus⟩

/-- **A load or a store of the CTA is before the barrier-12 event of its lane**, and the lane's
earlier events are before the deallocation. -/
private theorem ldst_bar12 {y ke h kd pc pcy : Nat} {c : TcKind} {grp : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request}
    (hd : X.get (h, kd) = some ⟨pc, .tc (.resource grp dst act)⟩)
    (hat : MbarRow.Wg0At L h pc) (hc : y / L.block = h / L.block)
    (hy : X.get (y, ke) = some ⟨pcy, .tc c⟩)
    (hc' : (∃ a vals sh, c = .ld a vals sh) ∨ ∃ a vals sh, c = .st a vals sh) :
    MbarRow.Wg0At L y pcy ∧ ∃ i' pc', X.get (y, i') = some ⟨pc', .bar 12 none .sync⟩ ∧
      ke < i' ∧ ∀ i, i < i' → baseCausality L X (y, i) (h, kd) := by
  have hatY := ldst_wg0 hp hX hFw hy hc'
  have hyg := Frame.lt_of_get hX hy
  have hg := Frame.lt_of_get hX hd
  obtain ⟨i', pc', hget, hcnt, hcaus⟩ := bar12_before hp hX hFw hR hd hat hatY.1
    ⟨hyg, hg, hc⟩
  have h0 : ((X.tr y).take ke).countP (Execution.isBarId 12) = 0 := by
    rcases hc' with ⟨a, vals, sh, rfl⟩ | ⟨a, vals, sh, rfl⟩
    · exact wg0_ldstBar12 hp hX hFw hy hatY (.inl rfl)
    · exact wg0_ldstBar12 hp hX hFw hy hatY (.inr rfl)
  refine ⟨hatY, i', pc', hget, ?_, hcaus⟩
  rcases Nat.lt_trichotomy ke i' with h1 | h1 | h1
  · exact h1
  · subst h1
    rw [hy] at hget
    simp only [Option.some.injEq, Event.mk.injEq] at hget
    obtain ⟨-, hk⟩ := hget
    rcases hc' with ⟨a, vals, sh, rfl⟩ | ⟨a, vals, sh, rfl⟩ <;> cases hk
  · have hbar : Execution.isBarId 12 ⟨pc', .bar 12 none .sync⟩ = true := by
      simp [Execution.isBarId]
    have := ClusterTrace.countP_take_lt (xs := X.tr y) (p := Execution.isBarId 12) h1 hget hbar
    omega

/-- **A load or a store precedes every deallocation of its CTA**, by its wait. -/
theorem dealloc_ldst {e d : EvId} {pc : Nat} {grp : CtaGroup} {dst : Option Loc} {da n a : Nat}
    {vals : List Value} {sh : TcShape}
    (hd : X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩)
    (hc : d.1 / L.block = e.1 / L.block) :
    (X.TLd e a vals sh → TcMma.WaitBefore L X .waitLd e d) ∧
    (X.TSt e a vals sh → TcMma.WaitBefore L X .waitSt e d) := by
  obtain ⟨h, kd⟩ := d
  obtain ⟨y, ke⟩ := e
  have hg := Frame.lt_of_get hX hd
  obtain ⟨-, hres⟩ := tmem_res (tmem_rows hp hX hFw) hg hd rfl
  have hat : MbarRow.Wg0At L h pc := by
    rcases hres with ⟨-, -, h1 | h1⟩ | ⟨hat, -⟩
    · cases h1
    · cases h1
    · exact hat
  refine ⟨fun ⟨pcl, hld⟩ => ?_, fun ⟨pcs, hst⟩ => ?_⟩
  · obtain ⟨hatY, i', pc', hget, hke, hcaus⟩ := ldst_bar12 hp hX hFw hR hd hat hc.symm hld
      (.inl ⟨_, _, _, rfl⟩)
    obtain ⟨w, pcw, hkw, hwi, hw⟩ := wg0_ldWait hp hX hFw hld hatY hget rfl hke
    exact ⟨(y, w), ⟨pcw, hw⟩, rfl, hkw, .inl (hcaus w hwi)⟩
  · obtain ⟨hatY, i', pc', hget, hke, hcaus⟩ := ldst_bar12 hp hX hFw hR hd hat hc.symm hst
      (.inr ⟨_, _, _, rfl⟩)
    obtain ⟨pcw, hw⟩ := wg0_stWait hp hX hFw hst hatY hget (fun fl h => by cases h) hke
    refine ⟨(y, ke + 1), ⟨pcw, hw⟩, rfl, Nat.lt_succ_self _, .inl (hcaus _ ?_)⟩
    rcases Nat.lt_or_ge (ke + 1) i' with h1 | h1
    · exact h1
    · obtain rfl : i' = ke + 1 := by omega
      rw [hw] at hget
      simp only [Option.some.injEq, Event.mk.injEq] at hget
      obtain ⟨-, hk⟩ := hget
      cases hk

omit hR in
/-- **An MMA or copy is the MMA lane's**, at a pc of its code above 1853. -/
theorem mma_role {g k pc : Nat} {c : TcKind} (he : X.get (g, k) = some ⟨pc, .tc c⟩)
    (hc : (∃ b sp acc mask, c = .mma b sp acc mask) ∨ ∃ cs, c = .cp cs) :
    MmaAt L g pc ∧ 1853 < pc := by
  have hg := Frame.lt_of_get hX he
  rcases tc_role (tmem_rows hp hX hFw) hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
  · exfalso
    rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;>
      cases h <;> rcases hc with ⟨_, _, _, _, h'⟩ | ⟨_, h'⟩ <;> cases h'
  · refine ⟨hat, ?_⟩
    rcases hM with h | ⟨_, k, hk, hpc, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, -⟩ |
      ⟨_, _, k, hk, hpc, h, -⟩
    · cases h
      rcases hc with ⟨_, _, _, _, h'⟩ | ⟨_, h'⟩ <;> cases h'
    · simp only [TmemRow.cpPc] at hpc
      split_ifs at hpc <;> omega
    · cases h
      rcases hc with ⟨_, _, _, _, h'⟩ | ⟨_, h'⟩ <;> cases h'
    · simp only [TmemRow.qkPc] at hpc
      split_ifs at hpc <;> omega
    · simp only [TmemRow.pvPc] at hpc
      split_ifs at hpc <;> omega
  · exfalso
    rcases hc with ⟨_, _, _, _, h'⟩ | ⟨_, h'⟩ <;> cases h' <;> cases hc'

variable (hMb : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hMb hI hB hN

omit hR in
/-- **An MMA or copy is done before every later event of a lane of warpgroup 0 after its poll of
`svDone`** (pc 1184, the CTA's last block's slot): the poll observes the lane's last commit,
which tracks every MMA and copy before it. -/
theorem done_after_svPoll {y0 i0 h k jw pc0 p : Nat} {k0 : TcKind}
    (hx : X.get (y0, i0) = some ⟨pc0, .tc k0⟩)
    (hk0 : (∃ b sp acc mask, k0 = .mma b sp acc mask) ∨ ∃ cs, k0 = .cp cs)
    (hc : h / L.block = y0 / L.block) (hw : MbarRow.warp L h < 4)
    (hpoll : X.get (h, jw) = some ⟨1184, .wait (mbarLoc L (h / L.block)
      (.svDone (slot2 (blocksOf P L (h / L.block) - 1)))) p true true .cta⟩)
    (hjw : jw < k) (hkl : k < (X.tr h).length) : TcMma.DoneBefore L X (y0, i0) (h, k) := by
  obtain ⟨hatm, h1853⟩ := mma_role hp hX hFw hx hk0
  have hgm : y0 = mmaLane L X (y0 / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) ⟨hatm, h1853⟩
  have hgm' : mmaLane L X (y0 / L.block) = y0 := hgm.symm
  have hg := Frame.lt_of_get hX hpoll
  have hyl : y0 < L.threads := Frame.lt_of_get hX hx
  rw [hc] at hpoll
  obtain ⟨hobs, -⟩ := svDone_done (pc0 := pc0) (i0 := i0) hp hX hFw hMb hI hB hN hw
    (by rw [hgm']) hpoll (by rw [hgm']; exact hx) (by rw [hgm']; exact hatm) h1853 hk0
  rw [hgm'] at hobs
  refine .inl ⟨(h, jw), .cta, hobs, ⟨⟨hyl, hg, ?_⟩, hg, hyl, hc⟩, ?_⟩
  · show L.clusterOfCta (y0 / L.block) = _
    rw [hc]
  exact .single (.inl (po_of_source_not_access rfl hjw hkl (by rw [hpoll]; rfl)))

/-- **Every MMA and copy is done before every deallocation of its CTA**: warpgroup 0's lane of
the deallocation polled `svDone` of the last block before its barrier-12 event (pc 1835), which
precedes the deallocation, and every MMA and copy is done at that poll (`svDone_done`). -/
theorem dealloc_async : Tmem.AccessCp.AsyncDoneDealloc L X := by
  intro i d pc a n grp dst hi hd hc
  obtain ⟨y0, i0⟩ := i
  obtain ⟨h, kd⟩ := d
  have hg := Frame.lt_of_get hX hd
  obtain ⟨-, hres⟩ := tmem_res (tmem_rows hp hX hFw) hg hd rfl
  have hat : MbarRow.Wg0At L h pc := by
    rcases hres with ⟨-, -, h1 | h1⟩ | ⟨hat, -⟩
    · cases h1
    · cases h1
    · exact hat
  obtain ⟨pc0, k0, hx, hk0⟩ : ∃ pc0 k0, X.get (y0, i0) = some ⟨pc0, .tc k0⟩ ∧
      ((∃ b sp acc mask, k0 = .mma b sp acc mask) ∨ ∃ cs, k0 = .cp cs) := by
    rcases hi with ⟨b, sp, acc, mask, pc0, hx⟩ | ⟨cs, pc0, hx⟩
    · exact ⟨pc0, _, hx, .inl ⟨b, sp, acc, mask, rfl⟩⟩
    · exact ⟨pc0, _, hx, .inr ⟨cs, rfl⟩⟩
  have hcnt := wg0_deallocBar12 hp hX hFw hd hat rfl
  have hkd : kd < (X.tr h).length := (List.getElem?_eq_some_iff.mp hd).1
  have hle := (List.take_sublist kd (X.tr h)).countP_le (p := Execution.isBarId 12)
  obtain ⟨j, pcj, hj, hjn⟩ := barId_nth hR hg (id := 12) (c := 0) (by omega)
  have hjk : j < kd := by
    by_contra hge
    have := countP_take_mono (Execution.isBarId 12) (X.tr h) (show kd ≤ j by omega)
    omega
  obtain rfl := wg0_bar12_pc hp hX hFw hat.1 hj
  obtain ⟨jw, p, hjw, hpoll⟩ := wg0_bar12_poll hp hX hFw hat.1 hj
  exact done_after_svPoll hp hX hFw hMb hI hB hN hx hk0 hc hat.1 hpoll (hjw.trans hjk) hkd

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace

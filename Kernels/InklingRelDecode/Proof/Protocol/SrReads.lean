-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SrWrites

@[expose] public section

/-!
# The Tensor Memory read branch of `Unsafe` (`Safety.Protocol.tcReads`)

`¬ TcMma.ReadsUnsafe L X`: every accumulator read and every Tensor Memory A read of an MMA is
ordered with every writer of its cell (`readsSafe_iff`); the kernel has no `tcgen05.shift`.

* **Accumulator reads** (`acc_order`): an accumulating MMA reads the cells it writes (the QK MMAs
  `j ≥ 1` the cells of `S b`, the PV MMAs the cells of `O`), so its reads are ordered as its writes
  (`WOrd`, `Sr.winfo_order`): the reader's side of an order is `ReadBefore .acc`, which contains
  the writer's `DoneBefore` and the pipelined D-write pair (`acc_conv`).
* **A reads** (`aread_order`): a PV MMA of block `m` reads `P (m % 2)` from Tensor Memory. A QK MMA
  of block `i'` of the same buffer writes it: if `i' ≤ m` it is done before the PV MMA
  (`qk_before_pv`: the QK commit is observed by thread 0's poll of `s_ready` for the use, which is
  before its arrival on `p_ready` that the lane polls before the PV MMA), else it is a later MMA of
  the lane and the A read and the D write are the pipelined pair
  (`SO.aRead_before_later_mma`; the order in the lane is the `o_done` commit counts). A `P` store
  of block `i'` of the buffer: if `i' ≤ m` it is done before the PV MMA (the `p_ready` handoff,
  `store_before_mma`), else the PV MMA is done before it (the store's poll of `s_ready` for a use
  above the MMA's commits, `mma_before_s_store`). No other writer has a cell of `P`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma InS InP InO TmOk below2)

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {c cm p0 tm : Nat} {Soft Mma : Nat → Prop}

/-- **An accumulator read of an MMA of CTA `c` is classified like a write**: the QK MMA's read
cells lie in `S (i % 2)`, the PV MMA's in `O`. -/
theorem rinfo_acc (l : Lane L X c cm p0 tm Soft) {x : EvId} {cell : Cell}
    (hr : X.MmaReadCell x cell) (hxc : x.1 / L.block = c) :
    WInfo L X c cm p0 tm Soft x cell := by
  obtain ⟨d, s, mask, row, col, hi, -⟩ := id hr
  rcases l.mma ⟨d, s, true, mask, hi⟩ hxc with ⟨i, hq⟩ | ⟨m, hv⟩
  · obtain ⟨j, pc, e, hget, hq'⟩ := hq.issue
    obtain ⟨h1, h2⟩ := qk_readCells l.tmOk hq' hget hr
    exact .qk hq h1 h2
  · obtain ⟨j, pc, e, hj, hget, hq'⟩ := hv.issue
    obtain ⟨h1, h2⟩ := pv_readCells l.tmOk hq' hget hr
    exact .pv hv h1 h2

/-- **A Tensor Memory A read is a PV MMA's**, of the cells of `P (m % 2)`. -/
theorem ainfo (l : Lane L X c cm p0 tm Soft) {x : EvId} {cell : Cell}
    (hr : X.MmaACell x cell) (hxc : x.1 / L.block = c) :
    ∃ m, PvAt L X c cm tm x m ∧ InP tm (m % 2) cell.column ∧ cell.cta = c := by
  obtain ⟨d, s, acc, mask, index, b, hi, hac⟩ := id hr
  rcases l.mma ⟨d, s, acc, mask, hi⟩ hxc with ⟨i, hq⟩ | ⟨m, hv⟩
  · exfalso
    obtain ⟨j, pc, e, hget, da, db, dsc, hd, -, -, rfl⟩ := hq.issue
    obtain ⟨pc', hget'⟩ := hi
    rw [hget] at hget'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hget'
    obtain ⟨-, rfl, rfl, -, -⟩ := hget'
    simp [aCell] at hac
  · obtain ⟨j, pc, e, hj, hget, hq'⟩ := hv.issue
    obtain ⟨h1, -, -, h2⟩ := SO.pv_aCells l.tmOk hj hq' hget hr
    exact ⟨m, hv, by simpa using h1, h2⟩

/-- **The accumulator read's order from the write order**: an MMA's side of an order of two writers
is a read order of the accumulator read. -/
theorem acc_conv (hnc : ∀ e cp, ¬ X.CpIssue e cp) {x y : EvId} (hx : IsMma X x)
    (h : WOrd L X x y) : x = y ∨ WriteBefore L X y x ∨ ReadBefore L X .acc x y := by
  rcases h with h | h | h
  · exact .inl h
  · right
    right
    rcases h with h | ⟨⟨a, vals, sh, hst⟩, -⟩ | ⟨-, -, cp, d, s, ac, mask, hcp, -⟩
    · rcases h with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · exfalso
      obtain ⟨d, s, ac, mask, pc, h1⟩ := hx
      obtain ⟨pc', h2⟩ := hst
      rw [h1] at h2
      simp at h2
    · exact (hnc _ _ hcp).elim
  · exact .inr (.inl h)

variable (H : Mbar.Ctx L K A mem0 X c cm p0 Soft Mma) (l : Lane L X c cm p0 tm Soft)
include H l

/-- **A QK MMA of the lane is done before a PV MMA of its buffer** that does not precede it in the
blocks (`i' ≤ m`): the QK commit is observed by thread 0's poll of `s_ready` (with `m / 2` earlier
polls) which precedes its arrival on `p_ready` that the lane's poll for block `m` synchronizes
with. -/
theorem qk_before_pv {y x : EvId} {i' m : Nat} (hq : QkAt L X c cm tm y i')
    (hv : PvAt L X c cm tm x m) (hpar : i' % 2 = m % 2) (hle : i' ≤ m) : DoneBefore L X y x := by
  have hb : m % 2 < 2 := Nat.mod_lt _ (by omega)
  have hxc : y.1 / L.block = c := hq.thread ▸ l.cm_ok.2
  have hf : m / 2 + 1 ≤ okPolls (pReady L c (m % 2)) ((X.tr cm).take x.2) := by
    have := hv.pPolls (m % 2) hb
    unfold SO.below2 at this
    omega
  obtain ⟨j0, pc0, e0, hj0, hget0, -⟩ := hv.issue
  have hfl := lane_len hv.thread hget0
  have hp0 := soft_info H H.route.p0_soft
  have hU := SO.p_handoff H.cons H.facts hb (cons := fun h => h = cm)
    (fun h hh => by subst hh; exact Mbar.pReach H hb H.route.cm_mma)
    (fun hh hw' => by subst hh; exact l.pAcq hb hw')
    (fun h hh => by subst hh; exact ⟨hp0.1, l.cm_ok.1, by rw [hp0.2.1, l.cm_ok.2]⟩)
  obtain ⟨jl, pcl, pl, acql, scl, hjl, hwl, hql⟩ := MbarRing.UnitHandoff.exists_poll hf
  obtain ⟨ia, hia, rs, ⟨tx, cnt, pca, hxa⟩, -⟩ := hU cm jl pcl pl acql scl (m / 2) rfl hwl hql p0
    ⟨0, rfl⟩
  obtain ⟨-, rfl, rfl, -⟩ := H.facts.p_arrive ⟨m % 2, hb, rfl⟩ hxa
  have hpolls := H.route.arrive_polls hb hxa
  rw [hia] at hpolls
  obtain ⟨jp, pcp, pp, acqp, scp, hjp, hwp, hqp⟩ :=
    MbarRing.UnitHandoff.exists_poll (m := sReady L c (m % 2)) (h := p0) (f := ia) (c := m / 2)
      (by omega)
  have hacq := l.sAcq hb hwp
  subst hacq
  have hmono := countP_take_mono (arrivesOn (pReady L c (m % 2))) (X.tr p0) hjp.le
  have hbc : baseCausality L X (p0, jp) (cm, x.2) := by
    refine MbarRing.UnitHandoff.baseCausality_of_counts hU (rfl : cm = cm) ⟨0, rfl⟩
      (e := jp) (q := m / 2) ?_ hf hfl
    unfold arrivals at hia ⊢
    omega
  have hx : x = (cm, x.2) := Prod.ext hv.thread rfl
  rw [← hx] at hbc
  refine s_doneBefore_to H hb ⟨l.cm_ok.1, hp0.1, by rw [hp0.2.1, l.cm_ok.2]⟩
    (fun hx hc => l.mma_thread hx hc) (Mbar.sReach H hb H.route.p0_soft) hwp hqp hq.isMma hxc ?_ hbc
  have := hq.sCommits
  rw [hpar] at this
  omega

/-- **A Tensor Memory A read and a writer of its cell are ordered**: the PV MMA `x` of block `m`
reads `P (m % 2)`, the cell is in it. -/
theorem aread_order {x y : EvId} {m : Nat} {cell : Cell}
    (hv : PvAt L X c cm tm x m) (hin : InP tm (m % 2) cell.column)
    (hy : WInfo L X c cm p0 tm Soft y cell) :
    x = y ∨ WriteBefore L X y x ∨ ReadBefore L X .a x y := by
  have hb2 : ∀ n : Nat, n % 2 < 2 := fun n => Nat.mod_lt _ (by omega)
  have hxc : x.1 / L.block = c := hv.thread ▸ l.cm_ok.2
  cases hy with
  | @qk _ cell' i' hq h1 _ =>
    have hpar : i' % 2 = m % 2 := inS_parity h1 (SO.inP_inS hin)
    by_cases hle : i' ≤ m
    · exact .inr (.inl (WriteBefore.of_done (qk_before_pv H l hq hv hpar hle)))
    · right
      right
      obtain ⟨j, pc, e, hj, hget, db, dsc, hd, -, rfl⟩ := hv.issue
      obtain ⟨j', pc', e', hget', da', db', dsc', hd', -, -, rfl⟩ := hq.issue
      refine SO.aRead_before_later_mma ⟨pc, hget⟩ rfl ⟨pc', hget'⟩ (hv.thread ▸ l.cm_ok.1)
        (hv.thread.trans hq.thread.symm) ?_
      by_contra hnot
      have hmono := countP_take_mono (commitsTo (oDone L c)) (X.tr cm) (show y.2 ≤ x.2 by omega)
      have h1 := hq.oCommits
      have h2 := hv.oCommits
      omega
  | @pv _ cell' m' hv' h1 _ => exact absurd h1 (SO.inP_inO_disjoint (hb2 _) hin)
  | @pst t sk i' w j' a' vals sh cell' hst hp hj ha hc hin' _ =>
    have hpar : m % 2 = i' % 2 := inP_parity hin hin'
    have hb' : i' % 2 < 2 := hb2 _
    obtain ⟨j0, pc0, e0, hj0, hget0, -⟩ := hv.issue
    by_cases hle : i' ≤ m
    · have hf : i' / 2 + 1 ≤ okPolls (pReady L c (i' % 2)) ((X.tr cm).take x.2) := by
        have := hv.pPolls (i' % 2) hb'
        unfold SO.below2 at this
        omega
      have h := store_before_mma H hb' l.cm_ok.1 l.cm_ok.2 (fun hw => l.pAcq hb' hw) hp.gate hst
        hf (lane_len hv.thread hget0)
      have hx : x = (cm, x.2) := Prod.ext hv.thread rfl
      rw [← hx] at h
      exact .inr (.inl (.inr (.inl h)))
    · have hu : ((X.tr cm).take x.2).countP (commitsTo (sReady L c (i' % 2))) ≤ i' / 2 := by
        have := hv.sCommits
        rw [hpar] at this
        omega
      exact .inr (.inr (.inr (.inl (mma_before_s_store H hb' l.cm_ok.1 l.cm_ok.2
        (fun hx hc => l.mma_thread hx hc) hp.gate hst hv.isMma hxc hu))))
  | @ost t sk i' w j' a' vals sh cell' hst ho hj ha hc hin' _ =>
    exact absurd hin' (SO.inP_inO_disjoint (hb2 _) hin)

omit H l in
/-- An event of the execution is a thread of a CTA of the grid. -/
theorem cta_lt (hX : Consistent L K A mem0 X) {w : EvId} (h : ∃ ev, X.get w = some ev) :
    w.1 / L.block < L.grid := by
  obtain ⟨ev, he⟩ := h
  have := event_thread_lt hX he
  unfold Launch.threads at this
  rw [Nat.mul_comm] at this
  exact Nat.div_lt_of_lt_mul this

omit H l in
/-- **`Safety.Protocol.tcReads`**: no Tensor Core read of a Tensor Memory cell is unordered with a
writer of the cell, given the reuse paths (`Mbar.Ctx`) and the coordinates (`Lane`) of every CTA of
the launch. -/
theorem no_reads_unsafe (hX : Consistent L K A mem0 X)
    (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
    (cm p0 tm : Nat → Nat) (Soft Mma : Nat → Nat → Prop)
    (H : ∀ c, c < L.grid → Mbar.Ctx L K A mem0 X c (cm c) (p0 c) (Soft c) (Mma c))
    (l : ∀ c, c < L.grid → Lane L X c (cm c) (p0 c) (tm c) (Soft c)) :
    ¬ ReadsUnsafe L X := by
  refine fun hn => hn (readsSafe_iff.mpr ⟨fun x y cell hrd hw => ?_, fun x y cell ha hw => ?_,
    fun x y cell hsh _ => ?_⟩)
  · obtain ⟨d, s, mask, row, col, ⟨pc, hxg⟩, -⟩ := id hrd
    have hxl := cta_lt hX ⟨_, hxg⟩
    have hyl := cta_lt hX (write_event hnc hns hw)
    have ix := rinfo_acc (l _ hxl) hrd rfl
    have iy := winfo hnc hns (l _ hyl) hw rfl
    have hxy : y.1 / L.block = x.1 / L.block := iy.cta.symm.trans ix.cta
    rw [hxy] at iy
    exact acc_conv hnc ⟨d, s, true, mask, pc, hxg⟩ (winfo_order (H _ hxl) (l _ hxl) ix iy)
  · obtain ⟨d, s, acc, mask, index, b, ⟨pc, hxg⟩, -⟩ := id ha
    have hxl := cta_lt hX ⟨_, hxg⟩
    have hyl := cta_lt hX (write_event hnc hns hw)
    obtain ⟨m, hv, hin, hcx⟩ := ainfo (l _ hxl) ha rfl
    have iy := winfo hnc hns (l _ hyl) hw rfl
    have hxy : y.1 / L.block = x.1 / L.block := iy.cta.symm.trans hcx
    rw [hxy] at iy
    exact aread_order (H _ hxl) (l _ hxl) hv hin iy
  · obtain ⟨s, hs, -⟩ := hsh
    exact (hns _ _ hs).elim

end
end PTX.Kernels.InklingRelDecode.Proof.Sr

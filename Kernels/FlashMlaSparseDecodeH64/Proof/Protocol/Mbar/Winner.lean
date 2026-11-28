-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Won
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Coll
import Lemmas.Protocol.CountNth
import Lemmas.Protocol.NamedBarMemberDone
import Lemmas.Order.DependencyWitness

@[expose] public section

/-! # A thread past barrier 0 has a winner of the pc-31 election in its CTA

A thread `h` with an event after its first barrier-0 event has passed the CTA barrier 0, so
every thread of its CTA has arrived at it (`bar0_first`: `Sources.member_arrival_any`, a thread
that exited has a barrier-0 event by `Bar0Rows.exit`). Lane 0 of warp 0 elected at pc 31 before
its barrier (`startup_bar_elect`); the leader lane of that election is a lane of warp 0 that
arrived too and elected at pc 31 with its own lane index (`elect_leader`, one mask by
`startup_elect`): the winner (`init_winner`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every thread of the CTA has a first barrier-0 event**, once a thread of the CTA has an
event after its own. -/
theorem bar0_first (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hB : Bar0Rows L X) {h f : Nat}
    (hpass : f < (X.tr h).length ∨ (f = (X.tr h).length ∧ Step.Released L X h))
    (hpos : 0 < ((X.tr h).take f).countP isBar0) {a : Nat} (ha : a / L.block = h / L.block)
    (hat : a < L.threads) :
    ∃ i pc cnt mode, X.get (a, i) = some ⟨pc, .bar 0 cnt mode⟩ ∧
      ((X.tr a).take i).countP isBar0 = 0 := by
  have hb := hp.block
  have hS := bar0_sources hp hB
  have hG := bar0_shape (L := L) hp
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 0)
    (xs := (X.tr h).take f) (c := 0) (by rw [← isBar0_eq]; omega)
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcj
  have hgetj : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pcj, kj⟩ := ev
  cases kj with
  | bar idj cntj modej =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    obtain ⟨-, rfl, -⟩ := startup_bar0 hp hX hFw hgetj rfl (by rw [isBar0_eq]; exact hcj)
    have hfb : X.IsBarrier (h, j) 0 cntj pcj := hgetj
    have hdone : ∃ key, CtaBarK L X (h, j) key ∧ CtaBarDone L X (h / L.block) key := by
      rcases Nat.lt_or_ge (j + 1) (X.tr h).length with hlt | hge
      · exact ctaBarDone_of_returned hX hfb hlt
      · obtain ⟨hfe, hrel⟩ : f = (X.tr h).length ∧ Step.Released L X h := by
          rcases hpass with hl | hl
          · omega
          · exact hl
        have hjl : j = (X.tr h).length - 1 := by omega
        have hr := hrel.ready pcj (.bar 0 cntj .sync) (by rw [← hjl]; exact hgetj)
          (by simp [Kind.resume])
        rw [← hjl] at hr
        have hmem : Need.cond (∃ key, CtaBarK L X (h, j) key ∧
            CtaBarDone L X (h / L.block) key) ∈ Needs L X (h, j) := by
          simp only [Needs, hgetj, KindNeeds, ctaBarNeeds]
          exact List.mem_append_right _ List.mem_cons_self
        exact hr _ hmem
    have hexit : (∃ jx pcx, X.get (a, jx) = some ⟨pcx, .exit⟩) →
        ∃ i pc' m', X.get (a, i) = some ⟨pc', .bar 0 none m'⟩ ∧
          ((X.tr a).take i).countP (Execution.isBarId 0) =
            ((X.tr h).take j).countP (Execution.isBarId 0) := by
      rintro ⟨jx, pcx, hx⟩
      have hp0 := hB.exit hat hx
      obtain ⟨i, ev', hi, hbi, hci⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 0)
        (xs := (X.tr a).take jx) (c := 0) (by rw [← isBar0_eq]; omega)
      have hij : i < jx := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp only [List.length_take] at this
        omega
      rw [List.take_take, Nat.min_eq_left hij.le] at hci
      have hgeti : X.get (a, i) = some ev' := by
        change (X.tr a)[i]? = some ev'
        rw [← hi, List.getElem?_take, ite_eq_left hij]
      obtain ⟨pci, ki⟩ := ev'
      cases ki with
      | bar idi cnti modei =>
        simp only [Execution.isBarId, beq_iff_eq] at hbi
        subst hbi
        have hcnt := (hS (a, i) pci cnti ⟨modei, hgeti⟩ hat).2
        subst hcnt
        exact ⟨i, pci, modei, hgeti, by rw [hci, hcj]⟩
      | _ => simp [Execution.isBarId] at hbi
    obtain ⟨i, pc', m', hgi, hci⟩ := hS.member_arrival_done hX hG hfb hdone
      (g := a) (by simpa using ha)
      (by
        have := Nat.mod_lt a (show 0 < L.block by omega)
        rw [Finset.mem_range]
        omega) hexit
    refine ⟨i, pc', none, m', hgi, ?_⟩
    rw [isBar0_eq, hci, hcj]
  | _ => simp [Execution.isBarId] at hbj

/-- **A thread past barrier 0 has a winner of the pc-31 election in its CTA**, which reaches
barrier 0, both before any barrier-0 event of its own (`InitRows.winner`). -/
theorem init_winner (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hB : Bar0Rows L X) {h f : Nat} (hh : h < L.threads)
    (hpass : f < (X.tr h).length ∨ (f = (X.tr h).length ∧ Step.Released L X h))
    (hpos : 0 < ((X.tr h).take f).countP isBar0) :
    ∃ g j kb mk inst pcb cnt mode, g / L.block = h / L.block ∧
      X.get (g, j) = some ⟨31, .elect mk inst (PTX.laneOf L g)⟩ ∧
      X.get (g, kb) = some ⟨pcb, .bar 0 cnt mode⟩ ∧ ((X.tr g).take j).countP isBar0 = 0 ∧
      ((X.tr g).take kb).countP isBar0 = 0 := by
  have hb := hp.block
  set c := h / L.block with hc
  have hcg : c < L.grid := by
    rw [hc]
    exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [Launch.threads] using hh)
  have hlt : ∀ x, x < L.block → c * L.block + x < L.threads := fun x hx => by
    have := Nat.mul_le_mul_right L.block (show c + 1 ≤ L.grid by omega)
    simp only [Launch.threads]
    nlinarith
  have key : ∀ x, x < 32 → (c * L.block + x) / L.block = c ∧ (c * L.block + x) % L.block = x ∧
      warpOf L (c * L.block + x) = 0 ∧ PTX.laneOf L (c * L.block + x) = x := fun x hx => by
    simp only [warpOf, PTX.laneOf, tidOf_eq hp, hb]
    omega
  obtain ⟨hz1, hz2, hz3, -⟩ := key 0 (by omega)
  -- lane 0 of warp 0 elects at pc 31 before its barrier
  obtain ⟨i0, pc0, cnt0, mode0, hb0, h00⟩ := bar0_first hp hX hFw hB hpass hpos
    (a := c * L.block + 0) (by rw [hz1]) (hlt 0 (by omega))
  obtain ⟨j0, hj0, mk0, inst0, ld0, he0⟩ := startup_bar_elect hp hX hFw (hlt 0 (by omega)) hb0
    rfl h00 hz3
  have h0j0 : ((X.tr (c * L.block + 0)).take j0).countP isBar0 = 0 := bar0_none hj0.le h00
  obtain ⟨hmk0, -⟩ := startup_elect hp hX hFw he0 rfl h0j0
  obtain ⟨-, -, hld, -⟩ := hX.elect.1 (c * L.block + 0, j0) 31 mk0 inst0 ld0 he0
  -- the leader lane is a thread of warp 0 of the CTA, which arrived at barrier 0 too
  have hgt := hlt ld0 (by omega)
  obtain ⟨hk11, hk12, hk13, hk14⟩ := key ld0 hld
  obtain ⟨i1, pc1, cnt1, mode1, hb1, h01⟩ := bar0_first hp hX hFw hB hpass hpos
    (a := c * L.block + ld0) (by rw [hk11]) hgt
  obtain ⟨j1, hj1, mk1, inst1, ld1, he1⟩ := startup_bar_elect hp hX hFw hgt hb1 rfl h01 hk13
  have h0j1 : ((X.tr (c * L.block + ld0)).take j1).countP isBar0 = 0 := bar0_none hj1.le h01
  obtain ⟨hmk1, -⟩ := startup_elect hp hX hFw he1 rfl h0j1
  have hsame : SameWarp L (c * L.block + 0) (c * L.block + ld0) :=
    ⟨⟨hlt 0 (by omega), hgt, by rw [hz1, hk11]⟩, by rw [hz2, hk12]; omega⟩
  have hl : ld0 = ld1 := by
    subst hmk0 hmk1
    exact elect_leader hX (e := (c * L.block + 0, j0)) (f := (c * L.block + ld0, j1)) he0 he1
      hsame
  refine ⟨c * L.block + ld0, j1, i1, mk1, inst1, pc1, cnt1, mode1, hk11, ?_, hb1, h0j1, h01⟩
  rw [hk14]
  rwa [← hl] at he1

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

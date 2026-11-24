-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Operands
public import Lemmas.Order.GuardOrder
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Before
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AccSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.LoadSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Role
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.SourceFacts
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Results
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The scores

QK step `j` of tile `u` leaves in the cell of query row `row` and key column `col` the sum of the
first `16 (j + 1)` products (`qk_result`): step 0 overwrites, and a later step accumulates on the
step before, which directly precedes it. A softmax load of tile `u` reads step 7, the last MMA
before the tile's commit, so it returns the scores `Σ_d Q(row, d) K(col, d)` (`score_load`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

/-- The score of query row `row` of stage `st` and key column `col` of the K block of tile `u`. -/
def dot (I : Inputs) (st u row col : Nat) : ℝ :=
  ∑ d ∈ Finset.range 128, I.q st row d * I.k u col d

/-- A sum over sixteen more indices. -/
theorem sum_add16 (f : Nat → ℝ) (n : Nat) : ∑ d ∈ Finset.range (16 * (n + 1)), f d =
    ∑ c ∈ Finset.range 16, f (16 * n + c) + ∑ d ∈ Finset.range (16 * n), f d := by
  rw [show 16 * (n + 1) = 16 * n + 16 by ring, Finset.sum_range_add, add_comm]

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {I : Nat → Inputs}

/-- The cell of an output position of a QK MMA. -/
theorem qk_pos {g k st u row col : Nat} {j : Fin 8} (hq : Qk L X g k st u j) (hst : st < 2)
    (da db : TcShared.Descriptor) (hrow : row < 128) (hcol : col < 128) :
    writeCell ⟨qkDsc, da, db, g / L.block, g / L.block, none, {}⟩ (128 * st) [0, 0, 0, 0] row col =
      some ⟨g / L.block, row, 128 * st + col⟩ :=
  (writeCell_zero (hq.spec da db) (by omega)).trans
    (resultCell_128 (hq.spec da db) (by omega) hrow hcol)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- A position of an MMA's output. -/
theorem mma_pos {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    (hi : X.MmaIssue i d s acc mask) (hc : X.MmaCell i cell) :
    ∃ row col, row < 128 ∧ col < 128 ∧ writeCell s d mask row col = some cell ∧
      cell = ⟨i.1 / L.block, row, d + col⟩ := by
  obtain ⟨d', s', acc', mask', row, col, hi', hw⟩ := hc
  obtain ⟨_, h1⟩ := hi
  obtain ⟨_, h2⟩ := hi'
  rw [h1] at h2
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at h2
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h2
  obtain ⟨rfl, hs, st, hst, h⟩ := mma_acc_at hp hX hFw ⟨_, h1⟩
  have hd : d + 128 ≤ 512 := by rcases h with ⟨_, _, -, h, -⟩ | ⟨_, _, -, h, -⟩ <;> omega
  have hw' := hw
  rw [writeCell_zero hs hd] at hw'
  obtain ⟨hr, hc, rfl⟩ := resultCell_128_iff hs hd hw'
  exact ⟨row, col, hr, hc, hw, rfl⟩

/-- A completed MMA's predecessor with the same cells is complete. -/
theorem prev_done {g k k' : Nat} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} {cell : Cell} (hi : X.MmaIssue (g, k') d s acc mask)
    (hi' : X.MmaIssue (g, k) d' s' acc' mask') (hk : k' < k) (hc : X.MmaCell (g, k') cell)
    (hc' : X.MmaCell (g, k) cell) (hd : X.async.mmaDone (g, k) = true) :
    X.async.mmaDone (g, k') = true := by
  have ht := scoreFacts hp hX hFw
  obtain ⟨hacc, hw⟩ := (sourceFacts hp hX hFw).same_write hi hi' rfl hc hc'
  obtain ⟨row, col, -, -, hpos, -⟩ := mma_pos hp hX hFw hi hc
  exact hX.mmaCompletion (g, k') (g, k) ⟨rfl, hk, mma_pipe ht hi hi' rfl hk hacc,
    _, _, _, _, _, _, _, _, hi, hi', hw, row, col, cell, hpos⟩ hd

/-- **QK step `n` of a tile leaves the sum of the first `16 (n + 1)` products.** -/
theorem qk_result (hI : OperandBytes I L X) {g st u : Nat} (hst : st < 2) :
    ∀ (n : Nat) {k : Nat} {j : Fin 8} {row col : Nat}, j.val = n → Qk L X g k st u j →
      X.async.mmaDone (g, k) = true → row < 128 → col < 128 →
      Result L Assumptions.all X (g, k) ⟨g / L.block, row, 128 * st + col⟩
        (.float .f32 (∑ d ∈ Finset.range (16 * (n + 1)),
          (I (g / L.block)).q st row d * (I (g / L.block)).k u col d)) := by
  intro n
  induction n with
  | zero =>
    intro k j row col hj hq hd hrow hcol
    obtain ⟨pc, da, db, he⟩ := id hq.issue
    have hi : X.MmaIssue (g, k) _ _ _ _ := ⟨pc, he⟩
    obtain ⟨ops, hops⟩ := operands_of_done hX hd
    have hacc : (j.val != 0) = false := by rw [hj]; rfl
    have hpos := qk_pos hq hst da db hrow hcol
    have hev := eval_mma hp hX hFw hi hops hpos
      (fun c hc => qk_a hp hI hst hq hi hd hops hrow hc)
      (fun c hc => qk_b hp hI hst hq hi hd hops hcol hc) (old := none) (prev := 0)
      (by rw [hacc]; rfl)
    rw [hacc] at hi hev
    rw [hj] at hev
    simp only [Nat.mul_zero, Nat.zero_add, add_zero, Nat.mul_one] at hev ⊢
    exact .overwrite hi hpos hops hev
  | succ n ih =>
    intro k j row col hj hq hd hrow hcol
    have hw := (mma_qkpv hp hX hFw (i := (g, k)) (by
      obtain ⟨pc, da, db, he⟩ := hq.issue
      exact ⟨_, _, _, _, pc, he⟩)).1
    obtain ⟨i, rfl, j', hj', hq'⟩ := Mma.qk_prev hp hX hFw hw hq (by rintro rfl; cases hj)
    obtain ⟨pc, da, db, he⟩ := id hq.issue
    have hi : X.MmaIssue (g, i + 1) _ _ _ _ := ⟨pc, he⟩
    obtain ⟨pc', da', db', he'⟩ := id hq'.issue
    have hi' : X.MmaIssue (g, i) _ _ _ _ := ⟨pc', he'⟩
    obtain ⟨ops, hops⟩ := operands_of_done hX hd
    have hacc : (j.val != 0) = true := by rw [hj]; rfl
    have hpos := qk_pos hq hst da db hrow hcol
    have hc : X.MmaCell (g, i + 1) ⟨g / L.block, row, 128 * st + col⟩ :=
      ⟨_, _, _, _, _, _, hi, hpos⟩
    have hc' : X.MmaCell (g, i) ⟨g / L.block, row, 128 * st + col⟩ :=
      ⟨_, _, _, _, _, _, hi', qk_pos hq' hst da' db' hrow hcol⟩
    have hd' := prev_done hp hX hFw hi' hi (Nat.lt_succ_self i) hc' hc hd
    have hprev := ih (by omega) hq' hd' hrow hcol
    have hH := handoffs hp hX hFw
    have hS : InS st ⟨g / L.block, row, 128 * st + col⟩ :=
      ⟨by simp only; omega, by simp only; omega⟩
    have hsrc := qk_accSource_last (scoreFacts hp hX hFw) (oAccFacts hp hX hFw) hH.s hH.p hH.p2
      (sourceFacts hp hX hFw) hst hi hc hS (Nat.lt_succ_self i) hc' (hq'.com.trans hq.com.symm)
      (fun k hk => by have := hk.1; simp only at this; omega)
    have hev := eval_mma hp hX hFw hi hops hpos
      (fun c hc => qk_a hp hI hst hq hi hd hops hrow hc)
      (fun c hc => qk_b hp hI hst hq hi hd hops hcol hc)
      (old := some (.float .f32 (∑ d ∈ Finset.range (16 * (n + 1)),
        (I (g / L.block)).q st row d * (I (g / L.block)).k u col d)))
      (by rw [hacc]; rfl)
    rw [hacc] at hi hev
    rw [hj] at hev
    rw [sum_add16 _ (n + 1)]
    exact .accumulate hi hpos hops hprev hsrc hev

/-- **The scores**: a softmax load of tile `u` returns the scores of its row. -/
theorem score_load (hI : OperandBytes I L X) {h i a j u : Nat} {vals : List Value}
    (hw : Prologue.warpIndex L h < 8) (hld : X.TLd (h, i) a vals .s32x32b) (hj : j < vals.length)
    (hu : sPolls L X h (Prologue.warpIndex L h / 4) i = u + 1) :
    vals[j]? = some (.float .f32 (dot (I (h / L.block)) (Prologue.warpIndex L h / 4) u
      (tcDataCell32 L h a j).lane
      ((tcDataCell32 L h a j).column - 128 * (Prologue.warpIndex L h / 4)))) := by
  have ht := scoreFacts hp hX hFw
  have ho := oAccFacts hp hX hFw
  have hT := sourceFacts hp hX hFw
  have hH := handoffs hp hX hFw
  obtain ⟨hh, -⟩ := ht.tc_role (.inl hld)
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  have hSc := (ht.soft_ld hh hw hld).1 j hj
  -- the commit of the tile, and step 7 before it
  obtain ⟨jp, pc, par, acq, sc, hji, hget, hq⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (m := sFull L (h / L.block) (Prologue.warpIndex L h / 4)) (h := h) (f := i)
    (c := u) (le_of_eq hu.symm)
  obtain ⟨⟨y, K⟩, s, rank, ws, hcom, hcy, hb, hcc, -⟩ := sFullHandoff hp hX hFw hh hw hget
  simp only at hcy hb hcc
  have hcc' : sCommits L X y (Prologue.warpIndex L h / 4) K = u := hcc.trans hq
  have hyw := commit_warp hp hX hFw hcom
  obtain ⟨k, rfl, hqk, ⟨pce, mk, inst, ld, hel⟩, -⟩ :=
    Mma.qk_before_commit hp hX hFw hyw hst hcom hb
  rw [hcc'] at hqk
  obtain ⟨hl, hcta⟩ := cell_lane hp (L := L) (h := h) (a := a) (j := j)
  have hcell : X.MmaCell (y, k) (tcDataCell32 L h a j) :=
    qk_cell hp hX hFw hst hqk (by rw [hcta, hcy]) hl hSc
  have hsrc : IsMma X (y, k) := by
    obtain ⟨_, _, _, he⟩ := hqk.issue
    exact ⟨_, _, _, _, _, he⟩
  have hdone := s_doneBefore ht hH.s hh hw hsrc hcy (by rw [show sCommits L X (y, k).1 _ (y, k).2 =
    u from hqk.com, hu]) (tLd_lt hld)
  have hlast : ∀ x, IsMma X x → X.MmaCell x (tcDataCell32 L h a j) →
      sCommits L X x.1 (Prologue.warpIndex L h / 4) x.2 ≤
        sCommits L X y (Prologue.warpIndex L h / 4) k → x = (y, k) ∨ x.2 < k := by
    rintro ⟨y', k'⟩ hx hxc hle
    obtain rfl : y' = y := ht.tc_one hx (.inl hsrc) (by
      rw [mma_lead ht hx hxc]
      exact hcy.symm)
    obtain ⟨d', s', acc', mask', hxi⟩ := hx
    obtain ⟨pcx, hxget⟩ := hxi
    rcases Nat.lt_trichotomy k' k with h1 | rfl | h1
    · exact .inr h1
    · exact .inl rfl
    · exfalso
      obtain ⟨pcs, hcget⟩ := id hcom
      have hne1 : k' ≠ k + 1 := by rintro rfl; rw [hel] at hxget; cases hxget
      have hne2 : k' ≠ k + 2 := by rintro rfl; rw [hcget] at hxget; cases hxget
      have h2 : ((X.tr y').take (k + 2 + 1)).countP
          (commitsTo (sFull L (y' / L.block) (Prologue.warpIndex L h / 4))) =
          sCommits L X y' (Prologue.warpIndex L h / 4) (k + 2) + 1 := by
        have hcg : (X.tr y')[k + 2]? = _ := hcget
        rw [List.take_add_one, hcg, Option.toList_some, List.countP_append]
        simp [sCommits, commitsTo, hb]
      have h3 := (List.take_sublist_take_left (l := X.tr y')
        (show k + 2 + 1 ≤ k' by omega)).countP_le
          (p := commitsTo (sFull L (y' / L.block) (Prologue.warpIndex L h / 4)))
      have h4 := hqk.com
      unfold sCommits at hle h4 h2 hcc'
      simp only at hle
      omega
  have hrs := s_readSource hp ht ho hH.p hH.p2 hH.s hh hw hld hj hsrc hcell
    (by rw [show sCommits L X (y, k).1 _ (y, k).2 = u from hqk.com, hu]) hlast
    (fun cta r hr hcov rel hrel => .inl (hT.live (.inr (.inl ⟨j, loadCell32 hld hj⟩)) cta r hr hcov
      rel hrel))
  have hcolb : 128 * (Prologue.warpIndex L h / 4) ≤ (tcDataCell32 L h a j).column ∧
      (tcDataCell32 L h a j).column < 128 * (Prologue.warpIndex L h / 4) + 128 := by
    have := hSc
    unfold InS at this
    omega
  have hres := qk_result hp hX hFw hI hst 7 (col := (tcDataCell32 L h a j).column -
    128 * (Prologue.warpIndex L h / 4)) rfl hqk (hdone.done hX.tcCommit) hl (by omega)
  have hceq : (⟨y / L.block, (tcDataCell32 L h a j).lane, 128 * (Prologue.warpIndex L h / 4) +
      ((tcDataCell32 L h a j).column - 128 * (Prologue.warpIndex L h / 4))⟩ : Cell) =
      tcDataCell32 L h a j := by
    have : 128 * (Prologue.warpIndex L h / 4) + ((tcDataCell32 L h a j).column -
        128 * (Prologue.warpIndex L h / 4)) = (tcDataCell32 L h a j).column := by omega
    rw [this, hcy, ← hcta]
  rw [hceq, hcy] at hres
  obtain ⟨word, hword, hcw⟩ :=
    hX.tcRead.1 _ a vals _ j _ _ _ hld (loadCell32 hld hj) hrs (.inl hres)
  rw [hword]
  rcases hcw with ⟨-, rfl⟩ | ⟨hb, -⟩
  · rfl
  · simp [Value.bytes, FloatFmt.bytes] at hb

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values

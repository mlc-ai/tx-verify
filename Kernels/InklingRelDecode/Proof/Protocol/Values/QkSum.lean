-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkSource
public import Kernels.InklingRelDecode.Proof.Protocol.Values.ResultReal
import Kernels.InklingRelDecode.Proof.Protocol.Values.QkResults
import Lemmas.Tcgen05.TcMmaZeroMask
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # The real a QK step leaves is the sum of the steps of its block

Step `j` of a QK block accumulates on step `j - 1` of the same round (`qk_source`), and step 0
overwrites. So the real of step `j` is the sum over the steps `i ≤ j` of the sixteen products of
step `i`, all at one position of the one cell. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

private theorem result_inj {s s' : OperandSpec} {base row col row' col' : Nat} {cell : Cell}
    (hm : s.descriptor.m = 64) (hg : s.descriptor.group = .one) (hw : s.descriptor.ws = false)
    (hm' : s'.descriptor.m = 64) (hg' : s'.descriptor.group = .one)
    (hw' : s'.descriptor.ws = false) (hl : base / 2 ^ 16 = 0)
    (h : resultCell s base row col = some cell) (h' : resultCell s' base row' col' = some cell) :
    row = row' ∧ col = col' := by
  have hh : halfDatapath s.descriptor = true := by simp [halfDatapath, hm, hg, hw]
  have hh' : halfDatapath s'.descriptor = true := by simp [halfDatapath, hm', hg', hw']
  unfold resultCell at h h'
  dsimp only at h h'
  split at h <;> split at h'
  · rename_i c1 c2
    obtain ⟨-, -, r1, -⟩ := c1
    obtain ⟨-, -, r2, -⟩ := c2
    simp only [hm, hg, hm', hg', hl] at h h' r1 r2
    simp only [CtaGroup.size] at h h'
    have e := h.trans h'.symm
    simp at e
    omega
  all_goals simp at h h'

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A cell has one position in the MMAs that write it.** -/
theorem mma_pos_eq (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {x y : EvId} {cell : Cell} {d s acc mask row col d' s' acc' mask' row' col'}
    (hx : X.MmaIssue x d s acc mask) (hy : X.MmaIssue y d' s' acc' mask')
    (px : writeCell s d mask row col = some cell)
    (py : writeCell s' d' mask' row' col' = some cell) :
    x.1 = y.1 ∧ row = row' ∧ col = col' := by
  obtain ⟨p1, h1⟩ := hx
  obtain ⟨p2, h2⟩ := hy
  obtain ⟨_, dx, sx, ax, mx, _, dy, sy, ay, my, hx, hy, thr, hd, hdesc, hlo, hhi, hm, hg, hw, hl⟩ :=
    mma_acc_eq hp hX hf base ⟨d, s, acc, mask, row, col, ⟨p1, h1⟩, px⟩
      ⟨d', s', acc', mask', row', col', ⟨p2, h2⟩, py⟩
  have e1 := get_tc_inj h1 hx
  have e2 := get_tc_inj h2 hy
  simp only [TcKind.mma.injEq] at e1 e2
  obtain ⟨rfl, rfl, -, -⟩ := e1
  obtain ⟨rfl, rfl, -, -⟩ := e2
  exact ⟨thr, result_inj hm hg hw (hdesc ▸ hm) (hdesc ▸ hg) (hdesc ▸ hw) hl
    (writeCell_resultCell px) (hd ▸ writeCell_resultCell py)⟩

/-- A real of an MMA's result is in a cell the MMA writes. -/
theorem res_real_cell {a b : EvId → Nat → Nat → ℝ} {sv : EvId → Cell → ℝ} {i : EvId}
    {cell : Cell} {r : ℝ} (h : ResReal L X a b sv i cell r) : X.MmaCell i cell := by
  cases h with
  | overwrite issue position => exact ⟨_, _, _, _, _, _, issue, position⟩
  | accumulate issue position => exact ⟨_, _, _, _, _, _, issue, position⟩
  | stored issue position => exact ⟨_, _, _, _, _, _, issue, position⟩

/-- **A QK step issues its accumulator flag by its index**: step 0 overwrites, later steps
accumulate. -/
theorem qk_acc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k d s acc mask} {j : Fin 8}
    (he : X.get (g, k) = some ⟨Lib.qkIssue j, .tc (.mma d s acc mask)⟩) :
    acc = decide (j.val ≠ 0) := by
  obtain ⟨_, _, _, _, _, h⟩ := Mma.Export.qk_block hp hX hf base he ⟨j, rfl⟩
  exact (h j rfl).1

/-- **The real of a QK step is the sum of the products of the steps of its block**, up to it. -/
theorem qk_sum (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) {a b : EvId → Nat → Nat → ℝ} {sv : EvId → Cell → ℝ}
    {g : Nat} :
    ∀ n {k : Nat} {j : Fin 8} {cell : Cell} {r : ℝ}, j.val = n → QkAt X g k j →
      ResReal L X a b sv (g, k) cell r →
      ∃ ks : Nat → Nat, ks j.val = k ∧ ∃ row col,
        (∀ i : Fin 8, i.val ≤ j.val → QkAt X g (ks i.val) i ∧
          pollRound 2462 ((X.tr g).take (ks i.val)) = pollRound 2462 ((X.tr g).take k) ∧
          ∃ d s acc mask, X.MmaIssue (g, ks i.val) d s acc mask ∧
            writeCell s d mask row col = some cell) ∧
        r = ∑ i ∈ Finset.range (j.val + 1), ∑ kk ∈ Finset.range 16,
          a (g, ks i) row kk * b (g, ks i) col kk := by
  intro n
  induction n with
  | zero =>
    intro k j cell r hj hq h
    obtain ⟨d1, s1, a1, m1, e1⟩ := hq
    cases h with
    | overwrite issue position =>
      rename_i d s mask row col
      refine ⟨fun _ => k, rfl, row, col, fun i hi => ?_, by simp [hj]⟩
      have : i = j := Fin.ext (by omega)
      subst this
      exact ⟨⟨d1, s1, a1, m1, e1⟩, rfl, d, s, false, mask, issue, position⟩
    | accumulate issue position previous provenance =>
      obtain ⟨pc, e2⟩ := issue
      rw [e1] at e2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2
      obtain ⟨-, -, -, rfl, -⟩ := e2
      have := qk_acc hp hX hf base e1
      simp [hj] at this
    | stored issue position written provenance =>
      obtain ⟨pc, e2⟩ := issue
      rw [e1] at e2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2
      obtain ⟨-, -, -, rfl, -⟩ := e2
      have := qk_acc hp hX hf base e1
      simp [hj] at this
  | succ n ih =>
    intro k j cell r hj hq h
    obtain ⟨d1, s1, a1, m1, e1⟩ := hq
    have hacc := qk_acc hp hX hf base e1
    have hj1 : j.val ≠ 0 := by omega
    simp only [hj1, ne_eq, not_false_eq_true, decide_true] at hacc
    subst hacc
    let j' : Fin 8 := ⟨n, by omega⟩
    have hjj : j'.val + 1 = j.val := by simp [j']; omega
    cases h with
    | overwrite issue position =>
      obtain ⟨pc, e2⟩ := issue
      rw [e1] at e2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2
      obtain ⟨-, -, -, hf', -⟩ := e2
      cases hf'
    | stored issue position written provenance =>
      rename_i d0 s0 mask0 row0 col0 source0
      have hrd : X.MmaReadCell (g, k) cell := ⟨d0, s0, mask0, row0, col0, issue,
        writeCell_resultCell position⟩
      exact (qk_nostore hp hX hf hu safe base rows init hG
        ⟨_, d1, s1, true, m1, e1, j, rfl⟩ hrd provenance written).elim
    | accumulate issue position previous provenance =>
      rename_i d0 s0 mask0 row0 col0 source0 r1
      have hrd : X.MmaReadCell (g, k) cell := ⟨d0, s0, mask0, row0, col0, issue,
        writeCell_resultCell position⟩
      obtain ⟨pc, e2⟩ := issue
      have e2' := e2
      rw [e1] at e2'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2'
      obtain ⟨-, rfl, rfl, -, rfl⟩ := e2'
      obtain ⟨kR, hsrc, hqR, hrR⟩ := qk_source hp hX hf hu base hG e1 hrd provenance
        (res_real_cell previous) hjj
      subst hsrc
      obtain ⟨ks, hks, row, col, facts, hsum⟩ := ih (j := j') rfl hqR previous
      obtain ⟨-, -, d2, s2, a2, m2, i2, p2⟩ := facts j' le_rfl
      obtain ⟨-, rfl, rfl⟩ := mma_pos_eq hp hX hf base ⟨pc, e2⟩ i2 position p2
      refine ⟨Function.update ks j.val k, Function.update_self .., row0, col0, fun i hi => ?_, ?_⟩
      · by_cases hij : i.val = j.val
        · have : i = j := Fin.ext hij
          subst this
          rw [Function.update_self]
          exact ⟨⟨d1, s1, true, m1, e1⟩, rfl, d1, s1, true, m1, ⟨pc, e2⟩, position⟩
        · rw [Function.update_of_ne hij]
          obtain ⟨q, rr, rest⟩ := facts i (by omega)
          exact ⟨q, rr.trans (hrR.trans rfl), rest⟩
      · have hj'v : j'.val = n := rfl
        rw [hj'v] at hsum
        rw [hsum, hj, Finset.sum_range_succ _ (n + 1)]
        have hc : ∀ i ∈ Finset.range (n + 1), ∑ kk ∈ Finset.range 16,
            a (g, Function.update ks (n + 1) k i) row0 kk *
              b (g, Function.update ks (n + 1) k i) col0 kk =
            ∑ kk ∈ Finset.range 16, a (g, ks i) row0 kk * b (g, ks i) col0 kk := fun i hi => by
          rw [Function.update_of_ne (by simp at hi; omega)]
        rw [Finset.sum_congr rfl hc, Function.update_self, add_comm]

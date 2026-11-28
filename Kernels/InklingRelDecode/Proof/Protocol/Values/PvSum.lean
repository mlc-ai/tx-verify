-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvSource
public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkSum
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # The real of a PV step is the sum of the products of the steps of its ordinal

Step `j` of a PV ordinal accumulates on step `j - 1` of the same ordinal (`pv_source`); step `0`
overwrites (ordinal `1`) or accumulates on the last step of the ordinal before it, or on the
rescale store of its round. So the real of step `j` is the sum over the steps `i ≤ j` of the
sixteen products of step `i`, all at one position of the one cell, plus the real the ordinal starts
from (`PvBase`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

/-- What the first step of PV ordinal `ord` starts from: nothing (ordinal `1`), the real of the
last step of the ordinal before it, or the word of the rescale store of its round. -/
def PvBase (L : Launch) (X : Execution) (a b : EvId → Nat → Nat → ℝ) (sv : EvId → Cell → ℝ)
    (g ord : Nat) (cell : Cell) (r0 : ℝ) : Prop :=
  (ord = 1 ∧ r0 = 0) ∨ (2 ≤ ord ∧ ((∃ kR, PvAt X g kR 7 ∧
    pollRound 2510 ((X.tr g).take kR) = ord - 1 ∧ ResReal L X a b sv (g, kR) cell r0 ∧
      ∀ st, ¬ RescaleAt L X st (ord - 1) cell) ∨
    ∃ st, RescaleAt L X st (ord - 1) cell ∧ r0 = sv st cell))

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The real of a PV step is the sum of the products of the steps of its ordinal**, up to it. -/
theorem pv_sum (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (hG : SyncGuarded L kernel X)
    (tie : RescaleLd X) {a b : EvId → Nat → Nat → ℝ} {sv : EvId → Cell → ℝ} {g : Nat} :
    ∀ n {k : Nat} {j : Fin 8} {cell : Cell} {r : ℝ}, j.val = n → PvAt X g k j →
      ResReal L X a b sv (g, k) cell r →
      ∃ ks : Nat → Nat, ks j.val = k ∧ ∃ row col,
        (∀ i : Fin 8, i.val ≤ j.val → PvAt X g (ks i.val) i ∧
          pollRound 2510 ((X.tr g).take (ks i.val)) = pollRound 2510 ((X.tr g).take k) ∧
          ∃ d s acc mask, X.MmaIssue (g, ks i.val) d s acc mask ∧
            writeCell s d mask row col = some cell) ∧
        ∃ r0, r = ∑ i ∈ Finset.range (j.val + 1), ∑ kk ∈ Finset.range 16,
          a (g, ks i) row kk * b (g, ks i) col kk + r0 ∧
          PvBase L X a b sv g (pollRound 2510 ((X.tr g).take k)) cell r0 := by
  intro n
  induction n with
  | zero =>
    intro k j cell r hj hq h
    obtain ⟨d1, s1, a1, m1, e1⟩ := hq
    obtain ⟨b0, pb, hacc, -⟩ := Mma.Export.pv_acc hp hX hf base e1 ⟨j, rfl⟩
    have hacc := hacc j rfl
    have j0 : ¬ j.val ≠ 0 := by omega
    simp only [j0, false_or] at hacc
    obtain ⟨b1, -, pb1, hb1, -⟩ := Mma.Export.pv_block hp hX hf base e1 ⟨j, rfl⟩
    have hb : b1 = b0 := by omega
    subst hb
    cases h with
    | overwrite issue position =>
      rename_i d s mask row col
      refine ⟨fun _ => k, by simp, row, col, fun i hi => ?_, 0, by simp [hj], ?_⟩
      · have : i = j := Fin.ext (by omega)
        subst this
        exact ⟨⟨d1, s1, a1, m1, e1⟩, rfl, d, s, false, mask, issue, position⟩
      · left
        obtain ⟨pc, e2⟩ := issue
        rw [e1] at e2
        simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2
        obtain ⟨-, -, -, rfl, -⟩ := e2
        rw [pb]
        have : ¬ 2 ≤ b1 := by simpa using hacc
        exact ⟨by omega, rfl⟩
    | accumulate issue position previous provenance =>
      rename_i d0 s0 mask0 row0 col0 source0 r1
      have hrd : X.MmaReadCell (g, k) cell := ⟨d0, s0, mask0, row0, col0, issue,
        writeCell_resultCell position⟩
      obtain ⟨pc, e2⟩ := issue
      have e2' := e2
      rw [e1] at e2'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2'
      obtain ⟨-, rfl, rfl, ha1, rfl⟩ := e2'
      subst ha1
      obtain ⟨b2, hc⟩ := (pv_source hp hX hf hu safe base rows init hG tie e1 hrd provenance).2
        (by omega)
      rcases hc with ⟨kR, hs, pat, rr, hno⟩ | hres
      · rw [hs] at previous
        refine ⟨fun _ => k, by simp, row0, col0, fun i hi => ?_, r1, by simp [hj], ?_⟩
        · have : i = j := Fin.ext (by omega)
          subst this
          exact ⟨⟨d1, s1, true, m1, e1⟩, rfl, d1, s1, true, m1, ⟨pc, e2⟩, position⟩
        · exact .inr ⟨b2, .inl ⟨kR, pat, rr, previous, hno⟩⟩
      · exfalso
        obtain ⟨sa, sv', ssh, sj, sy, -⟩ := hres
        obtain ⟨dd, ss, aa, mm, row, col, ⟨pc', hm⟩, -⟩ := res_real_cell previous
        rw [sy] at hm
        simp at hm
    | stored issue position written provenance =>
      rename_i d0 s0 mask0 row0 col0 source0
      have hrd : X.MmaReadCell (g, k) cell := ⟨d0, s0, mask0, row0, col0, issue,
        writeCell_resultCell position⟩
      obtain ⟨pc, e2⟩ := issue
      have e2' := e2
      rw [e1] at e2'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2'
      obtain ⟨-, rfl, rfl, ha1, rfl⟩ := e2'
      subst ha1
      obtain ⟨b2, hc⟩ := (pv_source hp hX hf hu safe base rows init hG tie e1 hrd provenance).2
        (by omega)
      rcases hc with ⟨kR, hs, pat, rr, hno⟩ | hres
      · exfalso
        obtain ⟨sa, sv', ssh, sj, ⟨pc', sy⟩, -⟩ := written
        obtain ⟨dd, ss, aa, mm, hm⟩ := pat
        rw [hs] at sy
        rw [sy] at hm
        simp at hm
      · refine ⟨fun _ => k, by simp, row0, col0, fun i hi => ?_, sv source0 cell,
          by simp [hj], ?_⟩
        · have : i = j := Fin.ext (by omega)
          subst this
          exact ⟨⟨d1, s1, true, m1, e1⟩, rfl, d1, s1, true, m1, ⟨pc, e2⟩, position⟩
        · exact .inr ⟨b2, .inr ⟨source0, hres, rfl⟩⟩
  | succ n ih =>
    intro k j cell r hj hq h
    obtain ⟨d1, s1, a1, m1, e1⟩ := hq
    obtain ⟨b0, pb, hacc, -⟩ := Mma.Export.pv_acc hp hX hf base e1 ⟨j, rfl⟩
    have hacc := hacc j rfl
    have j1 : j.val ≠ 0 := by omega
    simp only [j1, ne_eq, not_false_eq_true, true_or, decide_true] at hacc
    subst hacc
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
      obtain ⟨pc, e2⟩ := issue
      have e2' := e2
      rw [e1] at e2'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2'
      obtain ⟨-, rfl, rfl, -, rfl⟩ := e2'
      obtain ⟨kR, j', hjj, hs, pat, hrR⟩ := (pv_source hp hX hf hu safe base rows init hG tie e1
        hrd provenance).1 (by omega)
      exfalso
      obtain ⟨sa, sv', ssh, sj, ⟨pc', sy⟩, -⟩ := written
      obtain ⟨dd, ss, aa, mm, hm⟩ := pat
      rw [hs] at sy
      rw [sy] at hm
      simp at hm
    | accumulate issue position previous provenance =>
      rename_i d0 s0 mask0 row0 col0 source0 r1
      have hrd : X.MmaReadCell (g, k) cell := ⟨d0, s0, mask0, row0, col0, issue,
        writeCell_resultCell position⟩
      obtain ⟨pc, e2⟩ := issue
      have e2' := e2
      rw [e1] at e2'
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2'
      obtain ⟨-, rfl, rfl, -, rfl⟩ := e2'
      obtain ⟨kR, j', hjj, hs, pat, hrR⟩ := (pv_source hp hX hf hu safe base rows init hG tie e1
        hrd provenance).1 (by omega)
      subst hs
      obtain ⟨ks, hks, row, col, facts, r0, hsum, hbase⟩ := ih (j := j') (by omega) pat previous
      obtain ⟨-, -, d2, s2, a2, m2, i2, p2⟩ := facts j' le_rfl
      obtain ⟨-, rfl, rfl⟩ := mma_pos_eq hp hX hf base ⟨pc, e2⟩ i2 position p2
      rw [hrR] at hbase
      refine ⟨Function.update ks j.val k, Function.update_self .., row0, col0, fun i hi => ?_,
        r0, ?_, hbase⟩
      · by_cases hij : i.val = j.val
        · have : i = j := Fin.ext hij
          subst this
          rw [Function.update_self]
          exact ⟨⟨d1, s1, true, m1, e1⟩, rfl, d1, s1, true, m1, ⟨pc, e2⟩, position⟩
        · rw [Function.update_of_ne hij]
          obtain ⟨q, rr, rest⟩ := facts i (by omega)
          exact ⟨q, rr.trans hrR, rest⟩
      · have hj'v : j'.val = n := by omega
        rw [hj'v] at hsum
        rw [hsum, hj, Finset.sum_range_succ _ (n + 1)]
        have hc : ∀ i ∈ Finset.range (n + 1), ∑ kk ∈ Finset.range 16,
            a (g, Function.update ks (n + 1) k i) row0 kk *
              b (g, Function.update ks (n + 1) k i) col0 kk =
            ∑ kk ∈ Finset.range 16, a (g, ks i) row0 kk * b (g, ks i) col0 kk := fun i hi => by
          rw [Function.update_of_ne (by simp at hi; omega)]
        rw [Finset.sum_congr rfl hc, Function.update_self]
        ring

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values

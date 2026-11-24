-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.CorrVals
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatRead
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
import Kernels.TmlFa4Fwd.Proof.Correction.Export.StatRound
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Lemmas.Flow.MemTmpl
import Lemmas.Flow.Recip
import Lemmas.Flow.Step.RuleStep
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The statistics hand-off

A statistics read of a correction lane returns the bytes of one store of the row's softmax lane, of
the same named-barrier ordinal (`stat_store`): a scale read of round `u` the store of ordinal `u`,
a final read the one after the tile's last round. The bytes of those stores (`SoftStats`) are so
those of the reads: the row sums and maxima (`statVals`) and the scales (`scaleWords`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (Site)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A factor's word: its number, or the pattern `0f3F800000` when it is one. -/
def ScaleWord (w : Value) (x : ℝ) : Prop :=
  w = .float .f32 x ∨ w = .bits 32 (BitVec.ofNat 64 1065353216) ∧ x = 1

theorem ScaleWord.bytes {w : Value} {x : ℝ} (h : ScaleWord w x) : w.bytes = 4 := by
  rcases h with rfl | ⟨rfl, -⟩ <;> rfl

theorem ScaleWord.scalar {w : Value} {x : ℝ} (h : ScaleWord w x) : w.byteAt 0 = (w, 0) := by
  rcases h with rfl | ⟨rfl, -⟩ <;> rfl

/-- A factor's word reads as the factor. -/
theorem ScaleWord.reads {w : Value} {x : ℝ} (h : ScaleWord w x) :
    Assumption.readEReal .f32 w = some (.ok (x : EReal)) := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact readEReal_float_self _ _
  · rw [readEReal_bits32 1065353216 1 rfl (by decide) f32Value_one]
    simp

/-- **The bytes of the softmax lanes' statistics stores.** The store of ordinal `u` below the
tile's `T` rounds holds the factor of round `u`, the stores of ordinal `T` the row sum and, at a
valid row, the row maximum. -/
structure SoftStats (p : Params) (L : Launch) (X : Execution) (T : Nat → Option Tile)
    (D : Nat → RowData) : Prop where
  factor : ∀ {h i pc N u : Nat} {a : Acc} {bs : List Byte}, Prologue.warpIndex L h < 8 →
    X.get (h, i) = some ⟨pc, .wr a bs⟩ → a.loc = statLoc L h 0 → SoftRounds p L h N →
    barOrd X h i (Prologue.warpIndex L h + 3) = u → 1 ≤ u → u < N →
    ∃ w, ScaleWord w ((D h).f u) ∧ bs = w.toBytes
  sum : ∀ {h i pc N : Nat} {a : Acc} {bs : List Byte} {t : Tile}, Prologue.warpIndex L h < 8 →
    X.get (h, i) = some ⟨pc, .wr a bs⟩ → a.loc = statLoc L h 0 → SoftRounds p L h N →
    barOrd X h i (Prologue.warpIndex L h + 3) = N → T (h / L.block) = some t →
    t.Valid p (Prologue.warpIndex L h / 4) (rowIx L h) →
    bs = (Value.float .f32 (D h).rs).toBytes
  max : ∀ {h i pc N : Nat} {a : Acc} {bs : List Byte} {t : Tile}, Prologue.warpIndex L h < 8 →
    X.get (h, i) = some ⟨pc, .wr a bs⟩ → a.loc = statLoc L h 1 → SoftRounds p L h N →
    barOrd X h i (Prologue.warpIndex L h + 3) = N → T (h / L.block) = some t →
    t.Valid p (Prologue.warpIndex L h / 4) (rowIx L h) →
    bs = (Value.float .f32 (D h).rm).toBytes

/-- **The scale reads of the correction lanes**: the read of stage `st` with `u` P-full arrivals
before it returns a word of the factor of round `u` of the row's softmax lane. -/
def ScaleWords (L : Launch) (X : Execution) (D : Nat → RowData) : Prop :=
  ∀ {g i u : Nat} {st : Fin 2} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    8 ≤ Prologue.warpIndex L g → Prologue.warpIndex L g < 12 →
    X.get (g, i) = some ⟨(Site.rscale st).pc, .rd a bs⟩ → pArr L X g st i = u →
    ∃ w, ScaleWord w ((D (softLane L (g / L.block) st (rowIx L g))).f u) ∧ rebuild 3 bs = .ok w

theorem rebuild_word {w : Value} {bs : List (Option Byte)} {ws : List Byte}
    (hb : w.bytes = 4) (h0 : w.byteAt 0 = (w, 0)) (hws : ws = w.toBytes)
    (h : ws.length = 4 → bs = ws.map some) : rebuild 3 bs = .ok w := by
  subst hws
  rw [h (by rw [Value.toBytes, List.length_map, List.length_range, hb])]
  exact rebuild_scalar (by omega) h0

/-- The sites of the scale reads are in the rounds, of the final reads after them. -/
theorem stat_sites (st : Fin 2) : Correction.inRound (Site.rscale st).pc = true ∧
    Correction.tailR (Site.fsum st) = true ∧ Correction.tailR (Site.fmax st) = true := by
  revert st
  decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The source of a statistics read**: one store of the word by the row's softmax lane, of the
read's ordinal `A`, causally before the read, whose bytes the read returns; every other write of
the word is before the store or after the read. The ordinal is the round of a scale read and one
more than the rescale rounds at a final read. -/
theorem stat_store {y j : Nat} {a : Acc} {bs : List (Option Byte)} {s : Site} {n st : Fin 2}
    (h8 : 8 ≤ Prologue.warpIndex L y) (h12 : Prologue.warpIndex L y < 12)
    (he : X.get (y, j) = some ⟨s.pc, .rd a bs⟩) (hs : s.statRd = some (n, st)) :
    ∃ h i pcw aw ws A N, h = softLane L (y / L.block) st (rowIx L y) ∧
      h < L.threads ∧ Prologue.warpIndex L h < 8 ∧ h / L.block = y / L.block ∧
      Prologue.warpIndex L h / 4 = st.val ∧ rowIx L h = rowIx L y ∧
      X.get (h, i) = some ⟨pcw, .wr aw ws⟩ ∧ aw.size = 4 ∧ aw.loc = statLoc L h n.val ∧
      aw.loc = a.loc ∧ baseCausality L X (h, i) (y, j) ∧ (ws.length = 4 → bs = ws.map some) ∧
      1 ≤ A ∧ barOrd X h i (Prologue.warpIndex L h + 3) = A ∧ SoftRounds p L h N ∧
      (Correction.tailR s = true → A = N) ∧ (Correction.inRound s.pc = true → A < N) ∧
      (s = .rscale st → pArr L X y st j = A) ∧
      ∀ w' dst' bytes k, k < 4 → X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
        w' = .thread (h, i) ∨ modelCausality L X (a.loc.at k) w' (.thread (h, i)) ∨
          modelCausality L X (a.loc.at k) (.thread (y, j)) w' := by
  have hy := Frame.lt_of_get hX he
  have hb := hp.block
  obtain ⟨-, hl, A, hA1, hA, ⟨R, hR, htl, hlp⟩, hsc⟩ :=
    corr_stat_ord hp hX hFw h8 (by omega) he hs rfl
  obtain ⟨h, i, pcw, aw, ws, hw, hc, hg, hlw, hbc, hbs, hh, hz, hla, hord, hlast⟩ :=
    stat_source hp hX hFw hy h8 h12 he hs rfl
  have hst := st.isLt
  have hh' : h = y / 512 * 512 + 128 * st.val + y % 512 % 128 := by
    have h1 := hlw.symm.trans (hla.trans hl)
    simp only [statLoc, Loc.mk.injEq, true_and, Correction.rowN, Softmax.stN, hb] at h1
    simp only [Prologue.warpIndex, hb] at hw
    simp only [hb] at hc
    obtain ⟨-, h1⟩ := h1
    split at h1 <;> omega
  have hN : SoftRounds p L h (R + 1) := by
    obtain ⟨r, bal, hP, -⟩ := id hR
    have hT : SoftRounds p L h _ := ⟨r, bal, Epilogue.Picked.cta hc.symm hP, rfl⟩
    rwa [hT.corr hp hy hc hR] at hT
  have hAh : barOrd X h i (Prologue.warpIndex L h + 3) = A := by
    unfold barOrd at hord ⊢
    omega
  refine ⟨h, i, pcw, aw, ws, A, R + 1, ?_, hh, hw, hc, ?_, ?_, hg, hz, hlw, hla, hbc, hbs, hA1,
    hAh, hN, htl, fun hr => Nat.lt_succ_of_le (hlp hr), hsc, hlast⟩
  · simp only [softLane, rowIx, hb]
    exact hh'
  · simp only [Prologue.warpIndex, hb]
    omega
  · simp only [rowIx, hb]
    omega

/-- **The final statistics reads return the row sums and maxima.** -/
theorem statVals {D : Nat → RowData} {T : Nat → Option Tile} (hS : SoftStats p L X T D) :
    StatVals p L X T D where
  sum st t h8 h12 he hT hv := by
    obtain ⟨h, i, pcw, aw, ws, A, N, rfl, -, hw, hc, hst, hr, hg, -, hlw, -, -, hbs, -, hA, hN,
      htl, -⟩ := stat_store hp hX hFw h8 h12 he (s := .fsum st) rfl
    exact rebuild_word rfl rfl (hS.sum hw hg hlw hN (hA.trans (htl (stat_sites st).2.1))
      (by rw [hc]; exact hT) (by rw [hst, hr]; exact hv)) hbs
  max st t h8 h12 he hT hv := by
    obtain ⟨h, i, pcw, aw, ws, A, N, rfl, -, hw, hc, hst, hr, hg, -, hlw, -, -, hbs, -, hA, hN,
      htl, -⟩ := stat_store hp hX hFw h8 h12 he (s := .fmax st) rfl
    exact rebuild_word rfl rfl (hS.max hw hg hlw hN (hA.trans (htl (stat_sites st).2.2))
      (by rw [hc]; exact hT) (by rw [hst, hr]; exact hv)) hbs

/-- **The scale reads return words that read as the rounds' factors.** -/
theorem scaleWords {D : Nat → RowData} {T : Nat → Option Tile} (hS : SoftStats p L X T D) :
    ScaleWords L X D := by
  intro g i u st a bs _ h8 h12 he hu
  obtain ⟨h, i', pcw, aw, ws, A, N, rfl, -, hw, -, -, -, hg, -, hlw, -, -, hbs, hA1, hA, hN, -,
    hlt, hsc, -⟩ := stat_store hp hX hFw h8 h12 he (s := .rscale st) rfl
  obtain rfl : A = u := (hsc rfl).symm.trans hu
  obtain ⟨w, hW, hws⟩ := hS.factor hw hg hlw hN hA hA1 (hlt (stat_sites st).1)
  exact ⟨w, hW, rebuild_word hW.bytes hW.scalar hws hbs⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Coll
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.BiasLag
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollTab
public import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.LdWarp.Pos
import Kernels.TmlFa4Fwd.Proof.Lib.LdKvWait
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' places in a tile, by their collectives

`Tile` is what the picked tile fixes: the collectives before the blocks, the warm rounds, whether
the last Bias group is taken, the packets. A place of the blocks is a slot and a site (`Plc`): at
one with no more collectives than a collective place, a lane is earlier or at that place
(`plc_order`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk scanBase endBase primeBase bandL)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Pos selN Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g h : Nat}

/-- The collectives of the first pass, before the blocks. -/
def chN (R : Nat) (bal : BitVec 64) : Nat := 4 + 7 * (R + 1) + selN bal

/-- **What the picked tile fixes**: the first pass's collectives, the warm rounds, the last Bias
group, the packets. -/
def Tile (p : Params) (L : Launch) (g ch W : Nat) (l : Bool) (P : Nat) : Prop :=
  ∃ R bal, Picked p L g R bal ∧ ch = chN R bal ∧ W = w0 (r28Ref p L g R bal) ∧
    l = decide (10 < sv (r28Ref p L g R bal) ∧ sv (r29Ref p L g R bal) < 0) ∧
    P = pkts (r28Ref p L g R bal)

theorem r29Ref_cta {R : Nat} {bal : BitVec 64} (hc : g / L.block = h / L.block) :
    r29Ref p L g R bal = r29Ref p L h R bal := by
  simp only [r29Ref, refVL, setup, coords, Epilogue.chosenD, Epilogue.ctaW, hc]

/-- The lanes of a CTA are at one tile. -/
theorem Tile.same {ch W P ch' W' P' : Nat} {l l' : Bool} (hc : h / L.block = g / L.block)
    (hT : Tile p L g ch W l P) (hT' : Tile p L h ch' W' l' P') :
    ch' = ch ∧ W' = W ∧ l' = l ∧ P' = P := by
  obtain ⟨R, bal, hP, e1, e2, e3, e4⟩ := hT
  obtain ⟨R', bal', hP', e1', e2', e3', e4'⟩ := hT'
  obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hP').unique hP
  rw [r28Ref_cta hc] at e2' e4'
  rw [r28Ref_cta hc, r29Ref_cta hc] at e3'
  exact ⟨e1'.trans e1.symm, e2'.trans e2.symm, e3'.trans e3.symm, e4'.trans e4.symm⟩

theorem Tile.ch_ge {ch W P : Nat} {l : Bool} (hT : Tile p L g ch W l P) : 12 ≤ ch := by
  obtain ⟨R, bal, -, rfl, -⟩ := hT
  have := (Epilogue.selN_pos bal).1
  unfold chN; omega

theorem Tile.ch_le (hp : Pre p L m) {ch W P : Nat} {l : Bool} (hT : Tile p L g ch W l P) :
    ch ≤ Progress.cmax p := by
  obtain ⟨R, bal, hP, rfl, -⟩ := hT
  have := Epilogue.chosen_coll_le hp (d := Epilogue.chosenD p (g / L.block) R bal)
    (ns := 3 + 7 * (R + 1) + selN bal) (nv := 1) ⟨hP, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold chN Progress.cmax
  omega

theorem Tile.pkts_le (hp : Pre p L m) (hg : g < L.threads) {ch W P : Nat} {l : Bool}
    (hT : Tile p L g ch W l P) : P ≤ 2 * Progress.bmax p := by
  obtain ⟨R, bal, hP, -, -, -, hk⟩ := hT
  rw [hk]
  have hR : MmaRounds p L g _ := ⟨R, bal, hP, rfl⟩
  have h1 := pkts_rounds hP hR
  have h2 := mma_rounds_bmax hp hg hR
  omega

theorem Tile.warm_le {ch W P : Nat} {l : Bool} (hT : Tile p L g ch W l P) : 2 + 2 * W ≤ P := by
  obtain ⟨R, bal, -, -, hw, -, hk⟩ := hT
  rw [hk, hw]
  unfold pkts
  exact Nat.le_add_right _ _

/-- A block's slot (one past it; `0` is the first block's), with `W` warm rounds, the last Bias
group `l` and `P` packets. -/
def Plc (W : Nat) (l : Bool) (P x : Nat) : Blk → Prop
  | .prime => x = 0
  | .warm => 1 ≤ x ∧ x ≤ W
  | .tma6 => x = W + 1 ∧ l = true
  | .steady => W + 1 ≤ x ∧ 2 * x + 2 ≤ P

theorem Plc.le {o : Blk} {W P x B : Nat} {l : Bool} (hx : Plc W l P x o) (hW : 2 + 2 * W ≤ P)
    (hP : P ≤ 2 * B) : x ≤ B := by
  cases o <;> simp only [Plc] at hx <;> omega

/-- The collectives of the blocks before a slot. -/
def collBase (b : Bool) (W : Nat) (l : Bool) (x : Nat) : Nat :=
  if x = 0 then 0 else if x ≤ W + 1 then (if b then 64 + 64 * (x - 1) else 76 + 70 * (x - 1))
  else if b then 64 + 64 * (x - 1) else 76 + 70 * W + 64 * (x - 1 - W) + if l then 3 else 0

/-- The collectives of the blocks before a place. -/
def plcN (b : Bool) (W : Nat) (l : Bool) (x : Nat) (s : Site) : Nat :=
  collBase b W l x + loc b s +
    if b = false ∧ l = true ∧ x = W + 1 ∧ bc s = some .steady then 3 else 0

theorem plcN_prime {b : Bool} {W : Nat} {l : Bool} {s : Site} :
    plcN b W l 0 s = loc b s := by
  unfold plcN collBase
  rw [ite_eq_right (show ¬ (b = false ∧ l = true ∧ 0 = W + 1 ∧ bc s = some .steady) by omega)]
  simp

theorem plcN_warm {b : Bool} {W r : Nat} {l : Bool} {s : Site} (h : bc s ≠ some .steady)
    (hr : r ≤ W) : plcN b W l (r + 1) s = (if b then 64 + 64 * r else 76 + 70 * r) + loc b s := by
  unfold plcN collBase
  rw [ite_eq_right (show ¬ (b = false ∧ l = true ∧ r + 1 = W + 1 ∧ bc s = some .steady) from
    fun ⟨_, _, _, hc⟩ => h hc), ite_eq_right (by omega), ite_eq_left (by omega)]
  rfl

theorem plcN_steady {b : Bool} {W y : Nat} {l : Bool} {s : Site} (h : bc s = some .steady) :
    plcN b W l (W + y + 1) s =
      (if b then 64 + 64 * (W + y) else 76 + 70 * W + 64 * y + if l then 3 else 0) + loc b s := by
  unfold plcN collBase
  rw [h, ite_eq_right (by omega)]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · cases b <;> cases l <;> simp [Nat.add_right_comm]
  · rw [ite_eq_right (show ¬ (W + y + 1 ≤ W + 1) by omega)]
    have : y ≠ 0 := by omega
    cases b <;> cases l <;> simp [this]

/-- The collectives of the blocks. -/
def blkTot (b : Bool) (W : Nat) (l : Bool) (P : Nat) : Nat :=
  32 * P + if b then 0 else 12 + 6 * W + if l then 3 else 0

/-- The time of a place. -/
def blkT (p : Params) (x : Nat) (s : Site) : Nat :=
  if x = 0 then primeBase p + off s else clk p (x - 1) (bandL + off s)

theorem blkT_ge (p : Params) {o : Blk} {W P x : Nat} {l : Bool} {s : Site} (hb : bc s = some o)
    (hx : Plc W l P x o) : primeBase p + 8 ≤ blkT p x s := by
  unfold blkT
  obtain ⟨-, h1, -, -⟩ := off_bound s
  split_ifs with h0
  · have : o = .prime := by cases o <;> simp [Plc] at hx <;> first | rfl | omega
    subst this
    have := h1 hb
    omega
  · have := Progress.primeBase_le_clk p (x - 1) (bandL + off s)
    omega

theorem blkT_lt {o : Blk} {W P x : Nat} {l : Bool} {s : Site}
    (hx : Plc W l P x o) (hW : 2 + 2 * W ≤ P) (hP : P ≤ 2 * Progress.bmax p) :
    blkT p x s < endBase p := by
  obtain ⟨h0, -, -, -⟩ := off_bound s
  unfold blkT
  have hx' : x ≤ Progress.bmax p := hx.le hW hP
  have hs : x - 1 ≤ Progress.bmax p := by omega
  have := Progress.clk_lt_tail (p := p) (a := x - 1) (o := bandL + off s)
    (by simp only [Progress.span, bandL]; omega)
  rw [Progress.slotOf_eq hs] at this
  have h2 := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
  unfold endBase Progress.tailBase at *
  split_ifs <;> omega

theorem collBase_prime (b : Bool) (W : Nat) (l : Bool) : collBase b W l 0 = 0 := rfl

/-- A collective of a block is before the next slot. -/
theorem plcN_lt {b : Bool} {o : Blk} {W P x : Nat} {l : Bool} {s : Site} (hb : bc s = some o)
    (hw : s.wcoll = true) (ht : b = true → isT s = false) (hx : Plc W l P x o) {x' : Nat}
    (hlt : x < x') : plcN b W l x s < collBase b W l x' := by
  have h1 := loc_lt hb hw ht
  have h2 := off_bound s
  unfold plcN collBase
  cases o <;> simp only [Plc] at hx <;> simp only [size] at h1 <;>
    cases b <;> cases l <;> simp only [hb, reduceCtorEq, and_false, and_true, true_and,
      false_and, Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h1 hx ⊢ <;>
    split_ifs <;> omega

/-- A collective of the blocks is before their end. -/
theorem plcN_tot {b : Bool} {o : Blk} {W P x : Nat} {l : Bool} {s : Site} (hb : bc s = some o)
    (hw : s.wcoll = true) (ht : b = true → isT s = false) (hx : Plc W l P x o)
    (hW : 2 + 2 * W ≤ P) : plcN b W l x s < blkTot b W l P := by
  have h1 := loc_lt hb hw ht
  have h2 := off_bound s
  unfold plcN collBase blkTot
  cases o <;> simp only [Plc] at hx <;> simp only [size] at h1 <;>
    cases b <;> cases l <;> simp only [hb, reduceCtorEq, and_false, and_true, true_and,
      false_and, Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at h1 hx ⊢ <;>
    split_ifs <;> omega

/-- **A place with no more collectives than a collective place is earlier, or the same.** -/
theorem plc_order {b : Bool} {o o' : Blk} {W P x x' : Nat} {l : Bool} {s s' : Site}
    (hb : bc s = some o) (hb' : bc s' = some o') (hw : s.wcoll = true)
    (ht : b = true → isT s = false ∧ isT s' = false) (hx : Plc W l P x o) (hx' : Plc W l P x' o')
    (hle : plcN b W l x' s' ≤ plcN b W l x s) : blkT p x' s' < blkT p x s ∨ (x' = x ∧ s' = s) := by
  obtain ⟨f1, f2, f3, f4⟩ := off_bound s
  obtain ⟨g1, g2, g3, g4⟩ := off_bound s'
  rcases Nat.lt_trichotomy x' x with hlt | rfl | hlt
  · left
    unfold blkT
    split_ifs with h0 h1
    · omega
    · have := Progress.primeBase_le_clk p (x - 1) (bandL + off s); omega
    · omega
    · exact Progress.clk_lt_of_slot (by omega) (by simp only [Progress.span, bandL]; omega)
  · have same : o' = o → blkT p x' s' < blkT p x' s ∨ (x' = x' ∧ s' = s) := by
      rintro rfl
      have hl : loc b s' ≤ loc b s := by
        unfold plcN at hle
        rw [hb, hb'] at hle
        omega
      rcases off_lt hb hb' hw ht hl with h | h
      · left; unfold blkT; split_ifs
        · omega
        · exact Progress.clk_lt_of_off (by omega)
      · exact .inr ⟨rfl, h⟩
    by_cases ho : o' = o
    · exact same ho
    have hx0 : x' ≠ 0 := by
      rintro rfl
      cases o <;> cases o' <;> simp [Plc] at hx hx' ho
    cases o <;> cases o' <;> simp only [Plc] at hx hx' <;>
      try first
        | (exact absurd rfl ho)
        | (exfalso; omega)
    · -- a steady place, the other in the last Bias group
      left
      have := (f4 hb).1
      have := (g3 hb').1
      unfold blkT
      rw [ite_eq_right hx0, ite_eq_right hx0]
      exact Progress.clk_lt_of_off (by omega)
    · -- the last Bias group, the other at a steady place
      exfalso
      have hT := (f3 hb).2
      cases b with
      | true => rw [(ht rfl).1] at hT; cases hT
      | false =>
        have h1 := loc_lt (b := false) hb hw (fun h => by cases h)
        simp only [size, Bool.false_eq_true, ↓reduceIte] at h1
        unfold plcN at hle
        simp only [hb, hb', hx.1, hx.2, reduceCtorEq, and_false, and_true,
          Option.some.injEq, ↓reduceIte] at hle
        omega
  · exfalso
    have := plcN_lt hb hw (fun h => (ht h).1) hx hlt
    unfold plcN at hle this
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader

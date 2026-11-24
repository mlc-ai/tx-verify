-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.CollSched
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollCount
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' rounds, by their collectives

A round's warp barrier and election are a lane's collectives in the round; `softMid` places them in
the pipeline's slots. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk slotOf bandP primeBase endBase bmax)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (selN Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g h : Nat}

/-- What a softmax lane's tile fixes: the first pass's collectives, the biased rounds after the
first, the rounds. -/
@[ext]
structure SoftRun where
  ch : Nat
  nb : Nat
  T : Nat

/-- **The softmax lane's tile.** -/
def IsSoftTile (p : Params) (L : Launch) (w c g : Nat) (a : SoftRun) : Prop :=
  Prologue.warpIndex L g = w ∧ g / L.block = c ∧ a.T ≤ bmax p ∧
    ∃ R bal, Picked p L g R bal ∧ a.ch = 4 + 7 * (R + 1) + selN bal ∧
      a.nb = (Softmax.nB p L g (softRef p L g R bal)).toNat ∧
      a.T = 1 + a.nb + (Softmax.nP p L g (softRef p L g R bal)).toNat

theorem soft_stg {w : Nat} (hg : Prologue.warpIndex L g = w) (hh : Prologue.warpIndex L h = w) :
    Softmax.stg L h = Softmax.stg L g := by
  unfold Softmax.stg Softmax.warpW
  rw [show h % L.block / 32 = w from hh, show g % L.block / 32 = w from hg]

theorem IsSoftTile.same {w c : Nat} {a b : SoftRun} (hc : h / L.block = g / L.block)
    (hT : IsSoftTile p L w c g a) (hT' : IsSoftTile p L w c h b) : b = a := by
  obtain ⟨hw, -, -, R, bal, hP, h1, h2, h3⟩ := hT
  obtain ⟨hw', -, -, R', bal', hP', h1', h2', h3'⟩ := hT'
  obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hP').unique hP
  have hst := soft_stg hw hw'
  have hB : Softmax.nB p L h (softRef p L h R' bal') =
      Softmax.nB p L g (softRef p L g R' bal') := by
    simp only [Softmax.nB, Softmax.r169, Softmax.r299, Softmax.r166, Softmax.r168, Softmax.r165,
      Softmax.r1808, Softmax.rowOff, Mma.coords, softRef, Epilogue.ctaW, hc, hst]
  have hN : Softmax.nP p L h (softRef p L h R' bal') =
      Softmax.nP p L g (softRef p L g R' bal') := by
    simp only [Softmax.nP, Softmax.r431, Softmax.r169, Softmax.r299, Softmax.r166, Softmax.r168,
      Softmax.r165, Softmax.r1808, Softmax.rowOff, Mma.coords, softRef, Epilogue.ctaW, hc, hst]
  rw [hB] at h2'
  rw [hN] at h3'
  have e2 : b.nb = a.nb := h2'.trans h2.symm
  exact SoftRun.ext (h1'.trans h1.symm) e2 (by rw [h3', h3, e2])

/-- The kind of the `a`-th round of a tile with `nb` biased rounds after the first. -/
def rdOf (nb a : Nat) : Softmax.Rd :=
  if a = 1 then .first else if a ≤ 1 + nb then .bias else .plain

/-- **Where a state of the rounds stands** (stage `st`). -/
def SoftM (p : Params) (st : Nat) (a : SoftRun) (N t : Nat) (o : Option Softmax.Site) : Prop :=
  (o = none ∧ N = a.ch ∧ t < primeBase p + 8) ∨
  (o = none ∧ ∃ u, u ≤ a.T ∧ N = a.ch + 2 * u ∧ t < clk p (slotOf p u) (bandP st + 18)) ∨
  ∃ (u : Nat) (e : Bool), u + 1 ≤ a.T ∧ u + 1 ≤ bmax p ∧
    N = a.ch + 2 * u + (if e then 1 else 0) ∧
    t = clk p u (bandP st + 18 + if e then 2 else 0) ∧
    o = some (if e then .pel (rdOf a.nb (u + 1)) else .pws (rdOf a.nb (u + 1)))

/-- **The softmax warps' rounds** (warp `w` of CTA `c`, stage `st`). -/
def softMid (p : Params) (L : Launch) (w c st : Nat) (hst : st < 2) :
    Mid p L Softmax.Site SoftRun where
  tile := IsSoftTile p L w c
  ch a := a.ch
  tot a := 2 * a.T
  M := SoftM p st
  same := fun hc hT hT' => IsSoftTile.same hc hT hT'
  picked := fun hT => by
    obtain ⟨-, -, -, R, bal, hP, h1, -⟩ := hT
    exact ⟨R, bal, hP, h1⟩
  ge := by
    rintro a N t o (⟨-, h, -⟩ | ⟨-, u, -, h, -⟩ | ⟨u, e, -, -, h, -⟩) <;> omega
  tge := by
    rintro a N t x (⟨h, -⟩ | ⟨h, -⟩ | ⟨u, e, -, -, -, h, -⟩)
    · cases h
    · cases h
    · have := Progress.primeBase_le_clk p u (bandP st + 18 + if e then 2 else 0)
      omega
  lt_tot := by
    rintro a N t x (⟨h, -⟩ | ⟨h, -⟩ | ⟨u, e, h1, -, h2, -⟩)
    · cases h
    · cases h
    · cases e <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h2 <;> omega
  lt_end := by
    rintro g a N t o - - h
    have hend : Progress.tailBase p + 4096 = endBase p := rfl
    have hpt : primeBase p + 1024 ≤ Progress.tailBase p := Progress.primeBase_le_clk p _ _
    rcases h with ⟨-, -, h⟩ | ⟨-, u, -, -, h⟩ | ⟨u, e, -, hb, -, h, -⟩
    · omega
    · have := Progress.clk_lt_tail (p := p) (a := u) (o := bandP st + 18)
        (by simp only [bandP, Progress.span]; omega)
      omega
    · have := Progress.clk_lt_tail (p := p) (a := u) (o := bandP st + 18 + if e then 2 else 0)
        (by simp only [bandP, Progress.span]; split <;> omega)
      rw [Progress.slotOf_eq (by omega)] at this
      omega
  order := by
    rintro a N N' t t' x o (⟨h, -⟩ | ⟨h, -⟩ | ⟨u, e, h1, hb, h2, h3, h4⟩) hH hle
    · cases h
    · cases h
    have hT8 := Progress.primeBase_le_clk p u (bandP st + 18 + if e then 2 else 0)
    rcases hH with ⟨-, -, h⟩ | ⟨-, u', -, hN, h⟩ | ⟨u', e', -, hb', hN, h, ho⟩
    · left; omega
    · left
      have hu : u' ≤ u := by
        cases e <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h2 <;> omega
      have hs := Progress.slotOf_le (p := p) hu
      rw [Progress.slotOf_eq (show u ≤ bmax p by omega)] at hs
      rcases Nat.lt_or_eq_of_le hs with h5 | h5
      · have := Progress.clk_lt_of_slot (p := p) (o := bandP st + 18)
          (o' := bandP st + 18 + if e then 2 else 0) h5
          (by simp only [bandP, Progress.span]; omega)
        omega
      · rw [h5] at h
        rw [h3]
        unfold clk at h ⊢
        omega
    · rcases Nat.lt_trichotomy u' u with h5 | rfl | h5
      · left
        have := Progress.clk_lt_of_slot (p := p) (o := bandP st + 18 + if e' then 2 else 0)
          (o' := bandP st + 18 + if e then 2 else 0) h5
          (by simp only [bandP, Progress.span]; split <;> omega)
        omega
      · cases e <;> cases e' <;>
          simp only [Bool.false_eq_true, ite_true, ite_false] at h2 h3 h4 hN h ho
        · exact .inr ⟨by omega, ho.trans h4.symm, by omega⟩
        · omega
        · left; unfold clk at h h3; omega
        · exact .inr ⟨by omega, ho.trans h4.symm, by omega⟩
      · exfalso
        cases e <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h2 <;>
          cases e' <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hN <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Proof

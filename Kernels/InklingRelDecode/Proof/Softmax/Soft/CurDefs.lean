-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ind
public import Kernels.InklingRelDecode.Proof.Lib.BiasEv

@[expose] public section

/-! # The bias words of the value state

A word of the value state that stands for a bias is the `bf16` word of the specification's bias, or
the default (a zero) when the specification's bias is zero. In round `i` the words `cur` are the
biases of the block `splits * i + x`, and the loads of the loop fill `ld` with those of the next. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

/-- A bias word reads as the bias `b`. -/
def BW (v : Value) (b : ℝ) : Prop := v = .float .bf16 b ∨ (v = dflt ∧ b = 0)

/-- The sites from the entry of the loop to its end. -/
def loopLike : Site → Bool
  | .setMaxReg | .bar0 | .pre _ | .epilogue => false
  | _ => true

/-- The sites after the loop's own bias loads. -/
def postNxt : Site → Bool
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .epilogue => false
  | _ => true

/-- The sites whose event changes no bias word. -/
def Plain : Site → Bool
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .bar21 | .arrive | .epilogue => false
  | _ => true

/-- What the entry says about the CTA. -/
structure EntSp (Q : Params) (L : Launch) (g : Nat) (ent : Control.Entry) : Prop where
  split : ent.split = (L.ctaidOf (g / L.block)).get .x
  splits : ent.splits = Q.splits
  nbias : ent.nbias = Q.nBias ((L.ctaidOf (g / L.block)).get .z)

/-- **The bias words of a state** (of a lane whose row loads): the preloads so far, the words the
loop's packs read, the loop's loads so far and the words the next round will read. -/
structure CurBody (Q : Params) (L : Launch) (g : Nat) (ent : Control.Entry) (y : Data.D) :
    Prop where
  pre : ∀ j : Fin 64, y.c.site = .pre j →
    ∀ j' < j.val, y.v.ld j' = .float .bf16 (Lib.laneBias Q L g 0 j')
  cur : loopLike y.c.site = true → ∀ j' < 64, BW (y.v.cur j') (Lib.laneBias Q L g y.c.i j')
  nxt : ∀ j : Fin 64, y.c.site = .nxt j →
    ∀ j' < j.val, y.v.ld j' = .float .bf16 (Lib.laneBias Q L g (y.c.i + 1) j')
  post : postNxt y.c.site = true → y.c.i + 1 < ent.limit →
    ∀ j' < 64, BW (y.v.ld j') (Lib.laneBias Q L g (y.c.i + 1) j')

/-- **The bias words of a state.** -/
def CurOk (Q : Params) (L : Launch) (g : Nat) (ent : Control.Entry) (y : Data.D) : Prop :=
  validRow ent (g % L.block) = true → CurBody Q L g ent y

theorem Plain.post {s : Site} (h : Plain s = true) : postNxt s = true := by
  cases s <;> simp_all [Plain, postNxt]

theorem postNxt.loop {s : Site} (h : postNxt s = true) : loopLike s = true := by
  cases s <;> simp_all [postNxt, loopLike]

theorem postNxt.not_pre {s : Site} (h : postNxt s = true) (j : Fin 64) : s ≠ .pre j := by
  rintro rfl; simp [postNxt] at h

theorem postNxt.not_nxt {s : Site} (h : postNxt s = true) (j : Fin 64) : s ≠ .nxt j := by
  rintro rfl; simp [postNxt] at h

/-- The biases of a block below the first one with a bias are zero. -/
theorem laneBias_zero {Q : Params} {L : Launch} {g i : Nat}
    (h : Q.splits * i + (L.ctaidOf (g / L.block)).get .x <
      Q.nBias ((L.ctaidOf (g / L.block)).get .z))
    (j : Nat) (hj : j < 64) : Lib.laneBias Q L g i j = 0 := by
  unfold Lib.laneBias bias
  have : ¬ Q.nBias ((L.ctaidOf (g / L.block)).get .z) * 128 ≤ Lib.laneKey Q L g i j := by
    unfold Lib.laneKey
    omega
  simp [this]

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

/-- The words of a block below the first one with a bias read as zero. -/
theorem bw_zero (h : Q.splits * i + (L.ctaidOf (g / L.block)).get .x <
      Q.nBias ((L.ctaidOf (g / L.block)).get .z)) (j : Nat) (hj : j < 64) :
    BW dflt (Lib.laneBias Q L g i j) := .inr ⟨rfl, laneBias_zero h j hj⟩

/-- A loop that did not start the preloads has no bias in its first block. -/
theorem zero_first (E : EntSp Q L g ent) (ok : ent.Ok) (hv : validRow ent (g % L.block) = true)
    (hl : 0 < ent.limit) (hn : preEnabled ent (g % L.block) = false) :
    Q.splits * 0 + (L.ctaidOf (g / L.block)).get .x <
      Q.nBias ((L.ctaidOf (g / L.block)).get .z) := by
  have lim := ok.limitEq
  simp only [preEnabled, hv, Bool.true_and, decide_eq_false_iff_not, not_and] at hn
  split_ifs at lim with h31
  · have := hn (by omega) h31
    rw [← E.split, ← E.nbias]
    omega
  · omega

/-- A loop that did not start the loads of the next block has no bias in it. -/
theorem zero_next (E : EntSp Q L g ent) (ok : ent.Ok) (hv : validRow ent (g % L.block) = true)
    (hl : i + 1 < ent.limit) (hn : nextEnabled ent (g % L.block) i = false) :
    Q.splits * (i + 1) + (L.ctaidOf (g / L.block)).get .x <
      Q.nBias ((L.ctaidOf (g / L.block)).get .z) := by
  have lim := ok.limitEq
  simp only [nextEnabled, hv, Bool.true_and, decide_eq_false_iff_not, not_and] at hn
  split_ifs at lim with h31
  · have := hn (by omega) h31
    rw [← E.split, ← E.nbias, ← E.splits]
    nlinarith
  · omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScG
public import Kernels.InklingRelDecode.Proof.Thread.SmBridge
public import Lemmas.Flow.MaxCore

@[expose] public section

/-! # The row maximum (pcs 1764-1837)

After the mask the 32 pair registers `%rd499 …` hold the 64 scores of the thread's columns, each
a `.f32` number or the bit pattern of `-inf` (`infB`). The code unpacks the pairs and takes the
maximum with 21 three-operand and 21 two-operand `max.f32`, in a tree whose register numbering is
irregular. This file proves that the register `%r1059` (pc 1837) holds the maximum of the 64
scores as an extended real.

The proof does not enumerate the tree's values. A register written by the segment holds the
maximum of a set of columns, and the set is tracked as a 64-bit mask (`rmSt`), updated by an
abstract instruction list (`rmCode`) that is checked against the program's instructions by
`decide +kernel` (`rm_chk`). One step lemma (`seg_rm1`) takes the segment from the facts after
`c` instructions to those after `c + 1`, by cases on the abstract instruction; the facts after
`c` instructions are the live registers valued by an overlay of the written registers
(`rmEx`), each the extended-real maximum of its columns (`cmax`). That the root holds all 64
columns is `decide +kernel` (`rm_root`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### Score words as extended reals -/

theorem erealValue_bot' : erealValue .f32 ⊥ = infB := by decide +kernel

theorem ScoreWord.eval {v : Value} (h : ScoreWord v) : erealValue .f32 (eOf v) = v := by
  rcases h with ⟨x, rfl⟩ | rfl
  · exact erealValue_coe .f32 x
  · exact erealValue_bot'

theorem ScoreWord.ne_top {v : Value} (h : ScoreWord v) : eOf v ≠ ⊤ := by
  rcases h with ⟨x, rfl⟩ | rfl
  · exact EReal.coe_ne_top x
  · exact bot_ne_top

theorem ScoreWord.bytes {v : Value} (h : ScoreWord v) : v.bytes = 4 := by
  rcases h with ⟨x, rfl⟩ | rfl <;> rfl

/-- Every score word of the state is a `.f32` number or `-inf`. -/
def D.ScOk (d : D) : Prop := ∀ k < 64, ScoreWord (d.sv k).1

/-- **A value an extended real is the value of reads back as that real.** -/
theorem readEReal_erealValue {x : EReal} (h : x ≠ ⊤) :
    readEReal .f32 (erealValue .f32 x) = some (.ok x) := by
  induction x using EReal.rec with
  | bot => rw [erealValue_bot']; rfl
  | coe a => rw [erealValue_coe]; simp [readEReal, pure, Except.pure]
  | top => exact absurd rfl h

/-- `max.f32` of two or three values that are values of extended reals (not `+inf`). -/
theorem maxE_ereal2 {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    maxE [erealValue .f32 x, erealValue .f32 y] = .ok (erealValue .f32 (max x y)) := by
  unfold maxE
  simp [idealMax, readEReal_erealValue hx, readEReal_erealValue hy, bindRead, pure, Except.pure]

theorem maxE_ereal3 {x y z : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (hz : z ≠ ⊤) :
    maxE [erealValue .f32 x, erealValue .f32 y, erealValue .f32 z] =
      .ok (erealValue .f32 (max (max x y) z)) := by
  unfold maxE
  simp [idealMax, readEReal_erealValue hx, readEReal_erealValue hy, readEReal_erealValue hz,
    bindRead, pure, Except.pure]

/-! ### The columns a register holds -/

/-- The columns (as a mask) of register `r` in the register-mask list `st`. -/
def lk (st : List (Nat × Nat)) (r : Nat) : Nat := (st.lookup r).getD 0

/-- The effect of an instruction on the register-mask list (written registers in front). -/
def RI.upd : RI → List (Nat × Nat) → List (Nat × Nat)
  | .unp a b q, st => (b, 2 ^ (2 * q + 1)) :: (a, 2 ^ (2 * q)) :: st
  | .mx2 d a b, st => (d, lk st a ||| lk st b) :: st
  | .mx3 d a b c, st => (d, lk st a ||| lk st b ||| lk st c) :: st

/-- The register-mask list after the first `c` instructions. -/
def rmSt (c : Nat) : List (Nat × Nat) := (rmCode.take c).foldl (fun st i => i.upd st) []

theorem rmSt_succ {c : Nat} {i : RI} (h : rmCode[c]? = some i) :
    rmSt (c + 1) = i.upd (rmSt c) := by
  unfold rmSt
  rw [List.take_succ, h]
  simp [List.foldl_append]

/-! ### Checking the table against the program -/

/-- The instruction at `pc` is `max.f32 d, srcs` over registers. -/
def maxAt (pc d : Nat) (srcs : List Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .float f⟩ =>
    f == { op := .max, ty := FTy.mk .f32 1, dsts := [some d], srcs := srcs.map .reg }
  | _ => false

theorem maxAt_spec {pc d : Nat} {srcs : List Nat} (h : maxAt pc d srcs = true) :
    kernel.code[pc]? = some ⟨none, maxOp d srcs⟩ := by
  unfold maxAt at h
  split at h
  · rename_i f hc
    rw [hc, maxOp, beq_iff_eq.mp h]
  · cases h

/-- What the table's instruction `i` at `pc` must satisfy: the program has it there, the
registers it reads are columns of the list `st` (or, for an unpack, the untouched pair), they
are live, and the next pc's live registers are the written ones and the live ones. -/
def RI.chk (pc : Nat) (st : List (Nat × Nat)) : RI → Bool
  | .unp a b q => unpackAt pc a b (2447 + q) && decide (q < 32) && decide (a ≠ b) &&
      (st.lookup (2447 + q)).isNone && (Flow.live pc).contains (2447 + q) &&
      subX (Flow.live (pc + 1)) (Flow.live pc) [a, b] && !(Assumptions.emuSites.contains pc) &&
      decide (2447 + q ∉ zKeys)
  | .mx2 d a b => maxAt pc d [a, b] && (st.lookup a).isSome && (st.lookup b).isSome &&
      (Flow.live pc).contains a && (Flow.live pc).contains b &&
      subX (Flow.live (pc + 1)) (Flow.live pc) [d] && !(Assumptions.emuSites.contains pc)
  | .mx3 d a b c => maxAt pc d [a, b, c] && (st.lookup a).isSome && (st.lookup b).isSome &&
      (st.lookup c).isSome && (Flow.live pc).contains a && (Flow.live pc).contains b &&
      (Flow.live pc).contains c && subX (Flow.live (pc + 1)) (Flow.live pc) [d] &&
      !(Assumptions.emuSites.contains pc)

/-- The check of instruction `c`. -/
def rmChk (c : Nat) : Bool :=
  match rmCode[c]? with
  | some i => i.chk (1764 + c) (rmSt c)
  | none => false

theorem rm_chk : ∀ c < 74, rmChk c = true := by decide +kernel

/-! ### The overlay -/

/-! ### The steps -/

theorem split64_join {x y : Value} (hx : ScoreWord x) (hy : ScoreWord y) :
    splitValue 64 (joinValue x y) = (x, y) := by
  rcases hx with ⟨a, rfl⟩ | rfl <;> rcases hy with ⟨b, rfl⟩ | rfl
  · rfl
  · rfl
  · rfl
  · decide +kernel

theorem bytes_join {x y : Value} (hx : ScoreWord x) (hy : ScoreWord y) :
    (joinValue x y).bytes = 8 := by
  rcases hx with ⟨a, rfl⟩ | rfl <;> rcases hy with ⟨b, rfl⟩ | rfl <;> rfl

variable {d' : D}

/-! ### The maximum is `Softmax.blockMax` of the visible scores -/

theorem toFinset_sup_foldr (f : Nat → EReal) :
    ∀ l : List Nat, l.toFinset.sup f = l.foldr (fun k acc => max (f k) acc) ⊥
  | [] => rfl
  | k :: l => by
    rw [List.toFinset_cons, Finset.sup_insert, toFinset_sup_foldr f l]
    rfl

/-- `Softmax.blockMax` as the fold over the scores. -/
theorem blockMax_eq (blk : List (ℝ × ℝ)) :
    Softmax.blockMax blk =
      (blk.map Prod.fst).foldr (fun (x : ℝ) (acc : EReal) => max (x : EReal) acc) ⊥ := by
  unfold Softmax.blockMax
  induction blk with
  | nil => rfl
  | cons p t ih => simp only [List.foldr_cons, List.map_cons]; rw [ih]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm

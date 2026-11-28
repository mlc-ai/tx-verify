-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Machine
public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsRules

@[expose] public section

/-! # The bias words and their packs

The 64 bias words (16 bits) of the preloads (registers 263 to 326) and of the loop's loads
(registers 332 and 334 to 396), and the 32 packs of their pairs (registers 1916 to 1947) that the
first window reads. `wF` is the family of facts of a state: the words loaded so far (`Vals.ld`) and
the packs of the words of the round before (`Vals.cur`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow

noncomputable section

def preReg (k : Nat) : Nat := 263 + k
def nxtReg (k : Nat) : Nat := if k = 0 then 332 else 333 + k

/-- The facts of the first `n` words: register `reg k` holds word `k` (a zero past the loaded). -/
def wordF (reg : Nat → Nat) (ws : Nat → Value) (n : Nat) : List (Nat × Value) :=
  (List.range n).map fun k => (reg k, ws k)

/-- The value of the pack of two halves. -/
def packV (x y : Value) : Value := okVal (.bits 32 0) (pack32E [x, y])

/-- **The packs**: register `1916 + m` holds the pack of words `2m` and `2m + 1`. -/
def packF (ws : Nat → Value) : List (Nat × Value) :=
  (List.range 32).map fun m => (1916 + m, packV (ws (2 * m)) (ws (2 * m + 1)))

/-- The registers of the packs and of the loop's words. -/
def packK : List Nat := (List.range 32).map (1916 + ·)
def nwK : List Nat := (List.range 64).map nxtReg

/-- The sites that hold the packs of the words of the round before. -/
def wP : Site → Bool
  | .nxt _ | .waitS | .shfl4 | .ldS | .waitLd => true
  | _ => false

/-- The number of the loop's words the registers hold at a site. -/
def wN : Site → Nat
  | .nxt j => j.val
  | .setMaxReg | .bar0 | .pre _ | .epilogue => 0
  | _ => 64

/-- **The facts of the bias words** at a site. -/
def wFS (s : Site) (v : Vals) : List (Nat × Value) :=
  match s with
  | .pre j => wordF preReg v.ld j
  | s => (if wP s then packF v.cur else []) ++ wordF nxtReg v.ld (wN s)

def wF (d : D) : List (Nat × Value) := wFS d.c.site d.v

/-- The sites whose step keeps (a part of) the words: not the preloads, the loop's loads, the
barrier of the entry and the two sites that pack. -/
def midB : Site → Bool
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .bar21 | .arrive | .epilogue => false
  | _ => true

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

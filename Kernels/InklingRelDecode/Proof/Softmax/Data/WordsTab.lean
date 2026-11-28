-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Words
public import Lemmas.Flow.PhaseTableItem
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The bias words by position

On every path from the barrier of pc 575 or the last preload (pc 806) to a loop site (`wtab true`),
and from the barrier of pc 1012 or the arrival of pc 1013 to one (`wtab false`), the thread moves
the defaults into the registers of the loads (the loads may be skipped), packs the words and sets
the defaults of the loop's loads. `wKeys` lists, for each position, the registers whose facts
(`wV1`, and `wV2` once the defaults of the loop's words are set) hold there; `wSpec` the
positions of the moves. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The number of the preloads' defaults, the packs of a run from `a` and the loop's defaults
set before a position. -/
def preCnt (pc : Nat) : Nat := min 64 ((pc - 678) / 2)
def pkCnt (a pc : Nat) : Nat := min 32 (pc - a)
def nxtCnt (pc : Nat) : Nat := min 64 ((pc - 1122) / 2)

/-- The paths: from the barrier of pc 575 (`a`), from the last preload (`p`), from the loop's
barrier or arrival (`b`). -/
inductive WK where
  | a | p | b
  deriving DecidableEq

/-- The registers whose facts hold at a position of the path. -/
def wKeys (k : WK) (pc : Nat) : List Nat :=
  if 2560 ≤ pc then [] else
    (if k ≠ .b then (if pc < 848 then 199 :: (List.range (preCnt pc)).map preReg else []) ++
        (List.range (pkCnt 816 pc)).map (1916 + ·)
      else (if pc < 1046 then nwK else []) ++ (List.range (pkCnt 1014 pc)).map (1947 - ·)) ++
    (if 1123 ≤ pc then 333 :: (List.range (nxtCnt pc)).map nxtReg else [])

/-- The loop's words are set to their defaults from pc 1123 (the epilogue has no facts). -/
def wPost (pc : Nat) : Bool := decide (1123 ≤ pc ∧ pc < 2560)

/-- The values of the table before the loop's defaults: the 64 words (of the preloads or of the
loop's loads), their packs and the 16-bit zero. -/
def wV1 (ws : Nat → Value) (r : Nat) : Value :=
  if 263 ≤ r ∧ r < 327 then ws (r - 263)
  else if 1916 ≤ r ∧ r < 1948 then packV (ws (2 * (r - 1916))) (ws (2 * (r - 1916) + 1))
  else if r = 332 then ws 0
  else if 334 ≤ r ∧ r < 397 then ws (r - 333)
  else dflt

/-- The values after them: the loop's words are zero. -/
def wV2 (ws : Nat → Value) (r : Nat) : Value :=
  if r = 332 ∨ (334 ≤ r ∧ r < 397) then dflt else wV1 ws r

/-- The moves of a path: a default, a zero, a pack. -/
inductive WSp where
  | mv (d s : Nat)
  | mi (d : Nat)
  | pk (d a b : Nat)

def WSp.item : WSp → XItem
  | .mv d s => .fn (mv16Op d s) d [s] mv16E
  | .mi d => .fn (mi16Op d) d [] fun _ => .ok dflt
  | .pk d a b => .fn (pack32Op d [a, b]) d [a, b] pack32E

/-- The moves by position: the preloads' defaults (pc 679 + 2k), the packs of the preloads' words
(816 + m) and of the loop's (1014 + i), the zero (1122) and the loop's defaults (1123 + 2k). -/
def wSpec (pc : Nat) : Option WSp :=
  if 679 ≤ pc ∧ pc < 807 ∧ (pc - 679) % 2 = 0 then some (.mv (263 + (pc - 679) / 2) 199)
  else if 816 ≤ pc ∧ pc < 848 then
    some (.pk (1916 + (pc - 816)) (263 + 2 * (pc - 816)) (264 + 2 * (pc - 816)))
  else if 1014 ≤ pc ∧ pc < 1046 then
    some (.pk (1947 - (pc - 1014)) (nxtReg (2 * (31 - (pc - 1014))))
      (nxtReg (2 * (31 - (pc - 1014)) + 1)))
  else if pc = 1122 then some (.mi 333)
  else if 1123 ≤ pc ∧ pc < 1251 ∧ (pc - 1123) % 2 = 0 then
    some (.mv (nxtReg ((pc - 1123) / 2)) 333)
  else none

def wSpecB (pc : Nat) : Bool := (wSpec pc).isSome

/-- The code of the paths. -/
def wIvs : WK → List (Nat × Nat)
  | .a => [(576, 423), (1049, 208), (2560, 5)]
  | .p => [(807, 192), (1049, 208), (2560, 5)]
  | .b => [(1013, 244), (2560, 5)]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data

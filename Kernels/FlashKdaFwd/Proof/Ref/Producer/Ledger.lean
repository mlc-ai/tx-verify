-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Inv

@[expose] public section

/-! # The ledger of the Producer phase along the positions

The ledger of a position (`led`) is a function of the position; this file proves, once for all
sites, how it changes from a position to its successor: by the ledger of the event fired
between them. The events of the phase have five ledgers (`dBar`, `dPoll s`, `dArr s`, `dIss s`
and zero for a failed poll): a `bar.sync 0`, a successful poll of the "empty" mbarrier of
stage `s`, an arrival on the "full" mbarrier of stage `s`, a tensor load that completes on it.

The successor relations (one lemma each; `c` is the copy of the tile body, `u` the base index,
`T` the number of tiles):

| from | to | event |
|---|---|---|
| entry | `tail 0`, `poll 2 0`, `poll 0 0` (`T` = 0, 1, more), or the exit (not lane 0) | `dBar` |
| `poll c u` | `arrive c u` | `dPoll (tile % 3)` |
| `arrive c u` | `load c u 0` | `dArr (tile % 3)` |
| `load c u i` | `load c u (i + 1)` | `dIss (tile % 3)` |
| `load 0 u 69` | `poll 1 u` | `dIss` |
| `load 1 u 69` | `poll 0 (u + 2)`, `poll 2 (u + 2)` or `tail 0` (`T = u + 2`) | `dIss` |
| `load 2 u 69` | `tail 0` (`T = u + 1`) | `dIss` |
| `tail j` | `tail (j + 1)`, the exit after `tail 2` | `dPoll ((T + j) % 3)` |

Every proof is the same: unfold, split the fourteen fields, and decide each by linear
arithmetic with division by 3 and 70. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The ledger of a `bar.sync 0`. -/
def dBar : Led := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The ledger of an event that no class counts (a failed poll). -/
def dNone : Led := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The ledger of a successful poll of the "empty" mbarrier of stage `s`. -/
def dPoll (s : Nat) : Led :=
  ⟨0, 0, 0, 0, 1, if s = 0 then 1 else 0, if s = 1 then 1 else 0, if s = 2 then 1 else 0,
    0, 0, 0, 0, 0, 0⟩

/-- The ledger of an arrival on the "full" mbarrier of stage `s`. -/
def dArr (s : Nat) : Led :=
  ⟨0, 0, 1, 0, 0, 0, 0, 0, if s = 0 then 1 else 0, if s = 1 then 1 else 0,
    if s = 2 then 1 else 0, 0, 0, 0⟩

/-- The ledger of a tensor load that completes on the "full" mbarrier of stage `s`. -/
def dIss (s : Nat) : Led :=
  ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, if s = 0 then 1 else 0, if s = 1 then 1 else 0,
    if s = 2 then 1 else 0⟩

/-- `led_tac`: an equation between ledgers in closed form. -/
macro "led_tac" : tactic => `(tactic| (
  simp only [led, ledAt, ledEntry, ledExit, issuedOn, tile, dBar, dNone, dPoll, dArr, dIss,
    Led.add_def, Led.mk.injEq, PTX.Kernels.FlashKdaFwd.Proof.Ref.finVal, ↓reduceIte,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero, OfNat.ofNat_ne_one, OfNat.zero_ne_ofNat,
    one_ne_zero, zero_ne_one, *]
  <;> (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | trivial | omega | (split_ifs <;> (first | trivial | omega))))))

variable {P : Params} {g : Nat}

theorem led_poll_no (pos : Pos) : led P g pos = led P g pos + dNone := by
  simp [dNone, Led.add_def]

theorem led_entry_exit (h : tid g ≠ 128) : ledExit P g = led P g .entry + dBar := by
  led_tac

theorem led_entry_tail (h : tid g = 128) (hT : tilesOf P g = 0) :
    led P g (.tail 0) = led P g .entry + dBar := by
  led_tac

theorem led_entry_poll (h : tid g = 128) (c : Fin 3) (hc : c.val ≠ 1) :
    led P g (.poll c 0) = led P g .entry + dBar := by
  led_tac

theorem led_poll (c : Fin 3) (u : Nat) :
    led P g (.arrive c u) = led P g (.poll c u) + dPoll (tile c u % 3) := by
  led_tac

theorem led_arrive (c : Fin 3) (u : Nat) :
    led P g (.load c u 0) = led P g (.arrive c u) + dArr (tile c u % 3) := by
  led_tac

theorem led_load (c : Fin 3) (u : Nat) (i : Fin 70) (h : i.val + 1 < 70) :
    led P g (.load c u ⟨i.val + 1, h⟩) = led P g (.load c u i) + dIss (tile c u % 3) := by
  led_tac

theorem led_last_0 (u : Nat) :
    led P g (.poll 1 u) = led P g (.load 0 u 69) + dIss (tile 0 u % 3) := by
  led_tac

theorem led_last_1 (c : Fin 3) (hc : c.val ≠ 1) (u : Nat) :
    led P g (.poll c (u + 2)) = led P g (.load 1 u 69) + dIss (tile 1 u % 3) := by
  led_tac

theorem led_last_1_tail (u : Nat) (hT : tilesOf P g = u + 2) :
    led P g (.tail 0) = led P g (.load 1 u 69) + dIss (tile 1 u % 3) := by
  led_tac

theorem led_last_2 (u : Nat) (hT : tilesOf P g = u + 1) :
    led P g (.tail 0) = led P g (.load 2 u 69) + dIss (tile 2 u % 3) := by
  led_tac

theorem led_tail (j : Fin 3) (h : j.val + 1 < 3) :
    led P g (.tail ⟨j.val + 1, h⟩) = led P g (.tail j) + dPoll ((tilesOf P g + j.val) % 3) := by
  led_tac

theorem led_tail_exit (h : tid g = 128) :
    ledExit P g = led P g (.tail 2) + dPoll ((tilesOf P g + 2) % 3) := by
  led_tac

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer

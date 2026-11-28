-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Machine
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Plain
public import Lemmas.Flow.StepsQ

@[expose] public section

/-! # The tags of the prologue's untracked registers by program counter

The value machine (`Data.code`) states the control registers (`ctlLive`) and the data facts of the
copies (`Data.tags`) exactly. The other live registers are data (the block-table words and what
the spans compute from them, the query pointer chain's scratch), and `QT proQt`
(`Lemmas/Flow/HavocTyped.lean`) keeps them defined: they hold 32-bit words. The query payload
registers (`qReg`: sixteen-bit loads) and the packed store operands (`packReg`) are no 32-bit
words (a load returns the scalar that was stored, a pack of two such is a pair): the value machine
holds them as data facts (`Data.qTags`) wherever they live across a site and they carry no tag. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control

/-- The sixteen-bit query payload registers. -/
def qReg (r : Nat) : Bool := 198 ≤ r && r ≤ 262

/-- The packed words of the vector stores. -/
def packReg (r : Nat) : Bool := 747 ≤ r && r ≤ 785 && (r - 747) % 5 < 4

/-- The registers `QS` is about. -/
def qS (r : Nat) : Bool := qReg r || packReg r

/-- The registers the data facts hold at the last site at or before `pc`. -/
noncomputable def trackedAt (pc : Nat) : List Nat :=
  match (allSites.filter fun s => s.pc ≤ pc).getLast? with
  | some s => (Data.tags s).map Data.Tag.reg
  | none => []

/-- **The tags the prologue's data registers hold before `pc`.** -/
noncomputable def proQt (pc : Nat) : Env :=
  ((Flow.live pc).filter fun r => !ctl r && !qS r && !(trackedAt pc).contains r).map
    fun r => (r, .bits 32)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict

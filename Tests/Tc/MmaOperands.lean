-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Tcgen05.MmaComplete

/-! Regression: an MMA issue never commits to future operand-read outcomes.
Observed operands belong to the async snapshot and must survive extension unchanged. -/
namespace PTX.Tests.MmaOperands
open PTX AsyncCopy
noncomputable section

def smem : TcShared.Descriptor := ⟨0, 128, 256, 0, false, false, .none⟩
def spec : TcMma.OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩, smem, smem, 0, 0, none,
    {}⟩
def issue : Event := ⟨0, .tc (.mma 0 spec false [0, 0, 0, 0])⟩
def pending : Execution where
  tr := fun g => if g = 0 then [issue] else []
  rf := fun _ _ => none

def readA (v : Byte) : Execution :=
  { pending with async := { mmaOperands := fun i =>
      if i = (0, 0) then some ⟨List.replicate (128 * 32) (some v),
        List.replicate (8 * 32) (some v)⟩ else none } }

example : pending.MmaIssue (0, 0) 0 spec false [0, 0, 0, 0] := ⟨0, rfl⟩

example (v : Byte) : (readA v).tr = pending.tr := rfl

example (v : Byte) : (readA v).MmaIssue (0, 0) 0 spec false [0, 0, 0, 0] := ⟨0, rfl⟩

example : pending.async.mmaStarted (0, 0) = false := rfl

/-- Issuing work is already a drain obligation, before any operand has been read. -/
example : ¬ AsyncDrained pending := by
  intro h
  have hd := h (0, 0) .mmaDone
    (.inr (.inr (.inr (.inl ⟨.inl ⟨0, spec, false, [0, 0, 0, 0], ⟨0, rfl⟩⟩, rfl⟩))))
  cases hd

example (v : Byte) : (readA v).async.mmaStarted (0, 0) = true := by
  rfl

/-- A pending MMA still has its input footprint, so early reuse remains checkable. -/
example : pending.Intent (.async (0, 0) (.mmaRead false 0)) { loc := ⟨.shared, 0, 0⟩, size := 1 }
    false :=
  ⟨rfl, rfl, .inl ⟨0, spec, false, [0, 0, 0, 0], ⟨0, rfl⟩, rfl⟩⟩

-- The last A byte of row 127 and the last B byte of column 7, at their K-major addresses.
example : pending.MmaFootprint (0, 0) false (127 * 32 + 31) ⟨.shared, 0,
    16 * 7 + 256 * 15 + 15 + 128⟩ :=
  .inl ⟨0, spec, false, [0, 0, 0, 0], ⟨0, rfl⟩, rfl⟩
example : pending.MmaFootprint (0, 0) true (7 * 32 + 31) ⟨.shared, 0, 16 * 7 + 15 + 128⟩ :=
  .inl ⟨0, spec, false, [0, 0, 0, 0], ⟨0, rfl⟩, rfl⟩
-- B has only N = 8 rows.
example (l : Loc) : ¬ pending.MmaFootprint (0, 0) true (8 * 32) l := by
  rintro (⟨d, s, accum, mask, ⟨pc, hp⟩, hl⟩ | ⟨-, -, -, -, h, -⟩)
  swap; · cases h
  simp only [Execution.get, pending, List.getElem?_cons_zero, issue, Option.some.injEq,
    Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq,↓reduceIte] at hp
  obtain ⟨-, -, rfl, -, -⟩ := hp
  have : spec.byteLoc .b (8 * 32) = none := rfl
  simp_all

example (a : Acc) (bytes : List (Option Byte)) :
    ¬ pending.MemReads (.async (0, 0) (.mmaRead false 0)) a bytes := by
  rintro ⟨b, ⟨_, operands, hop, _⟩, _⟩
  cases hop

example (v : Byte) :
    (readA v).MemReads (.async (0, 0) (.mmaRead false 0)) { loc := ⟨.shared, 0, 0⟩, size := 1 }
      [some v] :=
  ⟨some v, ⟨.inl ⟨0, spec, false, [0, 0, 0, 0], ⟨0, rfl⟩, rfl⟩, _, rfl, rfl⟩, rfl, rfl⟩

/-- Once operands have been observed, extension cannot replace them with another guess. -/
example {X Y : Execution} (h : X.le Y) {i : EvId} {values : AsyncCopy.MmaOperands}
    (hr : X.async.mmaOperands i = some values) : Y.async.mmaOperands i = some values :=
  h.2.2.1.2.2.2.1 i values hr

/-- A first source MMA has no earlier completion predecessor. -/
example {L : Launch} {K : Kernel} {mem0 : Mem0} {X : Execution} {g : Nat}
    (hm : Maximal L K [] mem0 X) (hs : X.async.mmaStarted (g,0) = true) :
    X.async.mmaDone (g,0) = true := by
  apply hm.mma_done_of_started hs
  intro p hp
  have hlt := hp.2.1
  simp only at hlt
  omega

open Lean Elab Command in
run_elab do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``PTX.Execution.le_finishMma, ``PTX.finishMma_sinkFrame,
      ``PTX.consistent_finishMma, ``PTX.consistent_completeMma,
      ``PTX.Maximal.mma_done_of_started] do
    for ax in ← collectAxioms name do
      unless ax ∈ allowed do throwError "{name} uses unexpected axiom {ax}"
    logInfo m!"{name}: axioms checked"


end
end PTX.Tests.MmaOperands

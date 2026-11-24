-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Core.Async.Tensor.TensorStoreMemory
public import Lemmas.Order.Order

namespace PTX.Tests.TensorStoreMemory
noncomputable section

private def spec : TensorStore.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 0,
    128⟩, none⟩, none⟩
private def byte : Byte := (.float .f16 0, 0)
private def observation : TensorStore.Observation :=
  ⟨spec, { read := fun _ => some byte, write := fun _ => some byte }⟩
private def X : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorStore 1024 spec⟩] else [],
  rf := fun _ _ => none, tensorStores := fun i => if i = (0, 0) then some observation else none }
private def src : Acc := { loc := ⟨.shared, 0, 144⟩, size := 1 }
private def dst : Acc := { loc := ⟨.global, 0, 4096⟩, size := 1 }

private theorem read : X.MemReads (.async (0, 0) (.read (.store 0 0 0))) src [some byte] :=
  ⟨observation, 1024, byte, rfl, ⟨0, rfl⟩, rfl, rfl, rfl, rfl⟩
private theorem write : X.MemWrites (.async (0, 0) (.write (.store 0 0 0))) dst [byte] :=
  ⟨observation, 1024, byte, rfl, ⟨0, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
example : X.Intent (.async (0, 0) (.read (.store 0 0 0))) src false := read.intent
example : X.Intent (.async (0, 0) (.write (.store 0 0 0))) dst true := write.intent

-- Before observation, both footprints already participate in safety checks.
example : ({ X with tensorStores := fun _ => none } : Execution).Intent
    (.async (0, 0) (.read (.store 0 0 0))) src false :=
  ⟨rfl, spec, 1024, ⟨0, rfl⟩, rfl, rfl⟩
example : ({ X with tensorStores := fun _ => none } : Execution).Intent
    (.async (0, 0) (.write (.store 0 0 0))) dst true :=
  ⟨rfl, spec, 1024, ⟨0, rfl⟩, rfl, rfl⟩
example : ¬ ({ X with tensorStores := fun _ => none } : Execution).AsyncPresent
    (0, 0) (.read (.store 0 0 0)) := by rintro ⟨o, ho, _⟩; cases ho

example : TensorStore.readLoc spec 8 0 0 = none := rfl
example : TensorStore.writeLoc spec 0 0 2 = none := rfl
example : TensorStore.readLoc { spec with origin := ![8, 0] } 0 0 0 = some src.loc := rfl
example : TensorStore.writeLoc { spec with origin := ![8, 0] } 0 0 0 = none := rfl

-- Common execution-extension theorems preserve the byte values and memory footprints.
example (Y : Execution) (h : X.le Y) :
    Y.MemReads (.async (0, 0) (.read (.store 0 0 0))) src [some byte] :=
      Execution.le_memReads h read
example (Y : Execution) (h : X.le Y) :
    Y.MemWrites (.async (0, 0) (.write (.store 0 0 0))) dst [byte] := Execution.le_memWrites h write

private def overwritten : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorStore 1024 spec⟩,
    ⟨1, .wr { loc := src.loc, size := 2 } [byte, byte]⟩] else [], rf := fun _ _ => none }
-- A later ordinary store conflicts with the pending source read even with no observed effects.
example : Conflict overwritten (.async (0, 0) (.read (.store 0 0 0))) (.thread (0, 1)) src
    { loc := src.loc, size := 2 } := by
  refine ⟨by decide, false, true, ?_, ?_, Or.inr rfl, ?_⟩
  · exact ⟨rfl, spec, 1024, ⟨0, rfl⟩, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨[byte, byte], ⟨1, rfl⟩, rfl⟩)
  · exact ⟨src.loc, by simp [Acc.Covers, Loc.InRange, src], by simp [Acc.Covers, Loc.InRange, src]⟩

end
end PTX.Tests.TensorStoreMemory

-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Tensor.TensorMemory

namespace PTX.Tests.TensorMemory
noncomputable section

private def spec : TensorCopy.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 1,
    128⟩, none⟩, ⟨.shared, 0, 64⟩, true, .two⟩
private def observation : TensorCopy.Observation := ⟨spec, {
  read := fun slot => some ((Value.float .f16 3).byteAt slot.2.2.val),
  write := fun slot => some (.copied ((Value.float .f16 3).byteAt slot.2.2.val)) }⟩
private def X : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorIssue 1024 spec⟩] else [],
  rf := fun _ _ => none,
  tensor := fun i => if i = (0, 0) then some observation else none }

example : X.MemReads (.async (0, 0) (.read (.load 0 0 0))) { loc := ⟨.global, 0, 4096⟩, size := 1 }
    [some (.float .f16 3, 0)] :=
  ⟨observation, 1024, _, rfl, ⟨0, rfl⟩, rfl, rfl, rfl, rfl⟩
example : X.MemWrites (.async (0, 0) (.write (.load 0 0 0))) { loc := ⟨.shared, 1, 144⟩, size := 1 }
    [(.float .f16 3, 0)] :=
  ⟨observation, 1024, _, rfl, ⟨0, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Safety sees the pending destination even before a snapshot or write exists.
example : ({ X with tensor := fun _ => none } : Execution).Intent
    (.async (0, 0) (.write (.load 0 0 0))) { loc := ⟨.shared, 1, 144⟩, size := 1 } true :=
  ⟨rfl, spec, 1024, ⟨0, rfl⟩, rfl, rfl⟩
example : TensorCopy.writeLoc spec 8 0 0 = none := rfl
example : TensorCopy.readLoc { spec with origin := ![-16, 0] } 0 0 0 = none := rfl

example : (TensorCopy.Content.filled .zero .f16 1).byte = some (.float .f16 0, 1) := rfl
example : (TensorCopy.Content.filled .zero .bf16 0).byte = some (.float .bf16 0, 0) := rfl
example : (TensorCopy.Content.filled .zero .u32 3).byte = some (.bits 32 0, 3) := rfl
example : (TensorCopy.Content.filled .oobNan .f16 0).byte = none := rfl

end
end PTX.Tests.TensorMemory

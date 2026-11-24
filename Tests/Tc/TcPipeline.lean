-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaOrder

/-! The rows of `tcgen05.st` and `tcgen05.ld` in the pipeline table (`Pipelined`,
DEP-TC-PIPELINE): a store is ordered before a later load or store of the same warp without a
wait, a load is read before a later store of the same warp (`ReadBefore .ld`), and instructions
of different warps are never pipelined. -/
namespace PTX.Tests.TcPipeline
open TcMma
noncomputable section

private def L : Launch := { grid := 1, block := 64, params := fun _ => none, clusterSize := 1 }
private def w : Value := .bits 32 (BitVec.ofNat 64 7)

/-- Thread 0: store, load, store. Thread 32 (another warp): load. -/
def X : Execution where
  tr := fun g => if g = 0 then
      [⟨0, .tc (.st 0 [w] .s32x32b)⟩, ⟨1, .tc (.ld 0 [w] .s32x32b)⟩,
        ⟨2, .tc (.st 0 [w] .s32x32b)⟩]
    else if g = 32 then [⟨0, .tc (.ld 0 [w] .s32x32b)⟩] else []
  rf := fun _ _ => none

private theorem sameWarp : SameWarp L 0 0 := by
  simp [SameWarp, SameCta, L, Launch.threads]

-- st → ld of one thread: pipelined, so the store is ordered before the load without a wait.
example : Pipelined L X .stWrite (0, 0) .ldRead (0, 1) :=
  ⟨sameWarp, .inl (.single (.inl ⟨rfl, by decide, by decide⟩)), ⟨_, _, _, ⟨0, rfl⟩⟩,
    ⟨_, _, _, ⟨1, rfl⟩⟩⟩

example : StoreDoneBefore L X (0, 0) (0, 1) :=
  ⟨⟨_, _, _, ⟨0, rfl⟩⟩, .inr (.inl ⟨sameWarp, .inl (.single (.inl ⟨rfl, by decide, by decide⟩)),
    ⟨_, _, _, ⟨0, rfl⟩⟩, ⟨_, _, _, ⟨1, rfl⟩⟩⟩)⟩

-- st → st of one thread: pipelined.
example : StoreDoneBefore L X (0, 0) (0, 2) :=
  ⟨⟨_, _, _, ⟨0, rfl⟩⟩, .inr (.inr ⟨sameWarp, .inl (.single (.inl ⟨rfl, by decide, by decide⟩)),
    ⟨_, _, _, ⟨0, rfl⟩⟩, ⟨_, _, _, ⟨2, rfl⟩⟩⟩)⟩

-- ld → st of one thread: the load has read before the later store.
example : ReadBefore L X .ld (0, 1) (0, 2) :=
  .inr ⟨sameWarp, .inl (.single (.inl ⟨rfl, by decide, by decide⟩)), ⟨_, _, _, ⟨1, rfl⟩⟩,
    ⟨_, _, _, ⟨2, rfl⟩⟩⟩

-- A store and a load of different warps are not pipelined.
example : ¬ Pipelined L X .stWrite (0, 0) .ldRead (32, 0) := by
  rintro ⟨h, -⟩
  simp [SameWarp, SameCta, L, Launch.threads] at h

-- A load is not the first instruction of the st → ld row.
example : ¬ Pipelined L X .stWrite (0, 1) .ldRead (0, 2) := by
  rintro ⟨-, -, ⟨_, _, _, pc, h⟩, -⟩
  simp [Execution.get, X] at h

end
end PTX.Tests.TcPipeline

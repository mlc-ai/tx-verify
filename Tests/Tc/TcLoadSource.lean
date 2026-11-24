-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcLoadSource

namespace PTX.Tests.TcLoadSource
noncomputable section

-- Two unordered MMA writes are unsafe even if the execution contains no load.
example (L : Launch) (X : Execution) (x y : EvId) (cell : TcMma.Cell)
    (hx : X.MmaCell x cell) (hy : X.MmaCell y cell) (hne : x ≠ y)
    (hxy : ¬ TcMma.WriteBefore L X x y) (hyx : ¬ TcMma.WriteBefore L X y x) :
    TcMma.WritesUnsafe L X := by
  intro h
  rcases h x y cell (.inl hx) (.inl hy) with he | he | he
  · exact hne he
  · exact hxy he
  · exact hyx he

-- A load register with no completed, stable, live source is outside the supported
-- fragment, whatever its returned value.
example (L : Launch) (A : List Assumption) (X : Execution) (load : EvId)
    (cell : TcMma.Cell) (hc : TcMma.LoadCell L X load 0 cell)
    (hn : ∀ source value, ¬ (TcMma.ReadSource L X .ld source load cell ∧
      TcMma.Wrote L A X source cell value)) :
    ¬ TcMma.SourceSafe L A X := by
  intro h
  obtain ⟨source, value, hs, hw⟩ := h .ld load cell ⟨0, hc⟩
  exact hn source value ⟨hs, hw⟩

-- Safety provides both obligations.
example (L : Launch) (A : List Assumption) (X : Execution) (mem0 : Mem0)
    (hs : ¬ Unsafe L K A mem0 X) : TcMma.SourceSafe L A X ∧ TcMma.WritesSafe L X :=
  ⟨sourceSafe_of_safe hs, writesSafe_of_safe hs⟩

end
end PTX.Tests.TcLoadSource

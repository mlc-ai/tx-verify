-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaRead
public import Lemmas.Tcgen05.TcMmaValue
public import Mathlib.Tactic

namespace PTX.Tests.TcMmaRead
open TcMma
noncomputable section

-- FP32 uses a full word; it cannot quietly change the result or format.
example (x y : ℝ) (h : WordContains (.float .f32 x) (.float .f32 y)) : y = x := by
  have he := h.f32
  cases he
  rfl
example (x : ℝ) : ¬ WordContains (.float .f32 x) (.float .f16 x) := by
  intro h
  cases h.f32

-- FP16 occupies the low half only. Both upper halves below are allowed.
example (x : ℝ) (bits : BitVec 64) :
    WordContains (.float .f16 x) (.pair (.float .f16 x) (.bits 16 bits)) := by
  right
  refine ⟨rfl, rfl, ?_⟩
  intro k hk
  simp [Value.byteAt, Value.bytes, FloatFmt.bytes, hk]

private def L : Launch :=
  { grid := 2, block := 128, clusterSize := 2, params := fun _ => none }
private def X : Execution := {
  tr := fun _ => [⟨0, .tc (.ld 4 [.float .f32 7, .float .f32 8] .s32x32b)⟩],
  rf := fun _ _ => none }
-- CTA 1, warp position 1, thread lane 3, raw row zero, second register.
example : LoadCell L X (163, 0) 1 ⟨1, 35, 5⟩ :=
  ⟨4, _, _, ⟨0, rfl⟩, by decide, rfl⟩
example : ¬ LoadCell L X (163, 0) 1 ⟨0, 35, 5⟩ := by
  intro h
  have ho := h.owner
  cases ho

-- Any conflicting MMA, of either kind or group, is checked in the load interval.
example (Y : Execution) (source load other : EvId) (cell : Cell)
    (hw : Y.MmaCell other cell) (hs : other ≠ source)
    (hb : ¬ WriteBefore L Y other source)
    (ha : ¬ ReadBefore L Y .ld load other) : ¬ ReadSource L Y .ld source load cell := by
  intro h
  rcases h.2.2.2.1 other (.inl hw) with h | h | h
  · exact hs h
  · exact hb h
  · exact ha h

-- The same conflict must also be excluded inside an accumulation chain.
example (Y : Execution) (source consumer other : EvId) (cell : Cell)
    (hw : Y.MmaCell other cell) (hs : other ≠ source)
    (hb : ¬ WriteBefore L Y other source)
    (ha : ¬ ReadBefore L Y .acc consumer other) : ¬ ReadSource L Y .acc source consumer cell := by
  intro h
  rcases h.2.2.2.1 other (.inl hw) with h | h | h
  · exact hs h
  · exact hb h
  · exact ha h

-- Observing no completion cannot establish an MMA load source.
example (Y : Execution) (source load : EvId) (cell : Cell) {d : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} {a : Nat} {vals : List Value} {sh : TcShape}
    (hi : Y.MmaIssue source d s acc mask) (hl : Y.TLd load a vals sh)
    (hn : ∀ c rank, AsyncCopy.TracksMma Y source c → rank ∉ Y.tcNotified c) :
    ¬ ReadSource L Y .ld source load cell := by
  intro h
  obtain ⟨c, rank, ht, hr⟩ := (h.2.2.1.mma_load hi hl).tracked
  exact hn c rank ht hr

end
end PTX.Tests.TcMmaRead

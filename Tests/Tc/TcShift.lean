-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TcGroup
public import Core.Tc.TcMmaValue

/-! `tcgen05.shift` (THREAD-TC-SHIFT-CELLS, EXT-TCSHIFT, DEP-TMEM-SHIFT-VALUE): decoding, the cells
a shift reads and writes, the source of each moved word, and the rejected forms. -/
namespace PTX.Tests.TcShift
open PTX.TcShift
noncomputable section

private def env : Decode.Env := { classes := [⟨"r".toList, 2, 32⟩], labels := [], params := [] }

private def shift (q : String) : Except String Op := Decode.op env q [.address [.register "r0"]]

/-! ## Decoding -/

example : shift "tcgen05.shift.cta_group::1.down" = .ok (.tcShift .one 0) := rfl
example : shift "tcgen05.shift.cta_group::2.down" = .ok (.tcShift .two 0) := rfl
-- Rejected: an address with an offset (the destination takes a register only).
example : (Decode.op env "tcgen05.shift.cta_group::1.down"
    [.address [.offset "+" (.register "r0") (.literal "4")]]).toOption = none := rfl
example : (Op.tcShift .two 0).rule = some .threadTc := rfl
example : (Op.tcShift .two 0).tcGroup = some 2 := rfl

/-! ## Cells -/

private def s : Spec := ⟨16, [0]⟩

-- Lane 5 of the first chunk takes lane 6's word; lane 32 takes lane 33's.
example : source ⟨0, 5, 18⟩ = ⟨0, 6, 18⟩ := rfl
example : source ⟨0, 32, 18⟩ = ⟨0, 33, 18⟩ := rfl
-- Lane 32 w + 30 takes lane 32 w + 31's word, in the second CTA too.
example : source ⟨0, 30, 18⟩ = ⟨0, 31, 18⟩ := rfl
example : source ⟨1, 126, 18⟩ = ⟨1, 127, 18⟩ := rfl
-- The shift writes lanes 0 to 30 of each chunk in its 8 columns and reads lanes 1 to 31.
example : s.Writes ⟨0, 32, 23⟩ := ⟨0, 32, 7, by simp [s], by decide, by decide, by decide, rfl⟩
example : s.Writes ⟨0, 62, 16⟩ := ⟨0, 62, 0, by simp [s], by decide, by decide, by decide, rfl⟩
example : ¬ s.Writes ⟨0, 32, 24⟩ := by
  rintro ⟨cta, lane, col, -, -, -, hc, h⟩
  simp only [Spec.cell, s, TcMma.Cell.mk.injEq] at h
  omega
-- The last lane of a chunk (lanes 31, 63 and 127) is not written: it keeps its word, so no
-- shift is a writer of it and a later read takes the word of the write before the shift.
example : ¬ s.Writes ⟨0, 63, 16⟩ := by
  rintro ⟨cta, lane, col, -, -, hl, -, h⟩
  simp only [Spec.cell, s, TcMma.Cell.mk.injEq] at h
  omega
example : ¬ (⟨16, [0, 1]⟩ : Spec).Writes ⟨1, 127, 23⟩ := by
  rintro ⟨cta, lane, col, -, -, hl, -, h⟩
  simp only [Spec.cell, TcMma.Cell.mk.injEq] at h
  omega
example (X : Execution) (sh : EvId) : ¬ TcMma.ShiftCell X sh ⟨0, 31, 18⟩ ∧
    ∀ (L : Launch) (A : List Assumption) v, ¬ TcMma.ShiftValue L A X sh ⟨0, 31, 18⟩ v := by
  have h : ¬ TcMma.ShiftCell X sh ⟨0, 31, 18⟩ := by
    rintro ⟨s', -, cta, lane, col, -, -, hl, -, h⟩
    simp only [Spec.cell, TcMma.Cell.mk.injEq] at h
    omega
  refine ⟨h, fun L A v hv => ?_⟩
  obtain ⟨src, f, hs', -⟩ := hv
  exact h hs'.1
-- A shift is no Tensor Memory write of the last lane of a chunk, whatever its address.
private theorem shift_not_write {L : Launch} {X : Execution} {sh : EvId} {pc : Nat} {s' : Spec}
    (hsh : X.get sh = some ⟨pc, .tc (.shift s')⟩) (cta col : Nat) :
    ¬ TcMma.TmemWrite L X sh ⟨cta, 31, col⟩ := by
  intro hw
  rcases hw with ⟨_, _, _, _, _, _, ⟨_, h⟩, _⟩ | ⟨_, _, _, _, ⟨_, h⟩, _⟩ |
    ⟨_, _, _, _, ⟨_, h⟩, _⟩ | ⟨_, _, ⟨_, _, _, _, _, hl, _, h⟩⟩
  · rw [hsh] at h; cases h
  · rw [hsh] at h; cases h
  · rw [hsh] at h; cases h
  · simp only [Spec.cell, TcMma.Cell.mk.injEq] at h
    omega
-- Positive read case: a load of lane 31 takes the word of the write before the shift. Its read
-- source is that write when every other writer of the cell except the shift is ordered, and the
-- shift needs no order with the load; the shift itself is never the read source of the cell.
example (L : Launch) (X : Execution) (source sh e : EvId) (pc : Nat) (s' : Spec)
    (hsh : X.get sh = some ⟨pc, .tc (.shift s')⟩) (hne : source ≠ e)
    (hw : TcMma.TmemWrite L X source ⟨0, 31, 18⟩) (hb : TcMma.WriteBefore L X source e)
    (ho : ∀ other, TcMma.TmemWrite L X other ⟨0, 31, 18⟩ → other ≠ sh →
      other = source ∨ TcMma.WriteBefore L X other source ∨ TcMma.ReadBefore L X .ld e other)
    (hl : TcMma.SourceLive L X source e ⟨0, 31, 18⟩) :
    TcMma.ReadSource L X .ld source e ⟨0, 31, 18⟩ ∧
      ¬ TcMma.ReadSource L X .ld sh e ⟨0, 31, 18⟩ := by
  refine ⟨⟨hne, hw, hb, fun other ho' => ?_, hl⟩, fun h => shift_not_write hsh 0 18 h.2.1⟩
  by_cases h : other = sh
  · subst h; exact absurd ho' (shift_not_write hsh 0 18)
  · exact ho other ho' h
example : s.Reads ⟨0, 63, 16⟩ := ⟨0, 63, 0, by simp [s], by decide, by decide, by decide, rfl⟩
example : ¬ s.Reads ⟨0, 64, 16⟩ := by
  rintro ⟨cta, lane, col, -, -, hl, -, h⟩
  simp only [Spec.cell, s, TcMma.Cell.mk.injEq] at h
  omega
-- The address needs lane field 0 and its 8 columns within 512.
example : AddressOk 504 := by decide
example : ¬ AddressOk 505 := by decide
example : ¬ AddressOk (2 ^ 16) := by decide

end
end PTX.Tests.TcShift

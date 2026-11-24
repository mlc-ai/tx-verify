-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Execution.NoAsync
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

namespace PTX.Tests.MixedAccess
noncomputable section

def launch : Launch := { grid := 1, block := 1, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def base : Loc := ⟨.shared, 0, 0⟩
def wide : Acc := { loc := base, size := 8 }
def narrow : Acc := { loc := base.at 4, size := 4 }
def payload : List Byte := (Value.bits 64 0x8877665544332211).toBytes

def ex : Execution where
  tr g := if g = 0 then [⟨0, .wr wide payload⟩,
    ⟨1, .rd narrow ((payload.drop 4).map some)⟩] else []
  rf _ _ := some (.thread (0, 0))

private theorem event_cases {e : EvId} {v : Event} (h : ex.get e = some v) :
    e = (0, 0) ∨ e = (0, 1) := by
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst g
    have hi : i < 2 := by
      have hh := (List.getElem?_eq_some_iff.mp h).1
      simpa [ex] using hh
    interval_cases i <;> simp
  · simp [Execution.get, ex, hg] at h

private theorem no_async : ex.NoTma := by
  intro e pc k he
  rcases event_cases he with hh | hh <;> rw [hh] at he <;>
    simp [Execution.get, ex] at he <;> rcases he with ⟨rfl, rfl⟩ <;> rfl

/-- These footprints genuinely overlap and differ in width. -/
example : wide.Overlap narrow ∧ wide ≠ narrow := by
  refine ⟨⟨base.at 4, ?_, ?_⟩, ?_⟩
  · exact ⟨rfl, rfl, by decide, by decide⟩
  · exact ⟨rfl, rfl, by decide, by decide⟩
  · decide

private theorem ordered : baseCausality launch ex (0, 0) (0, 1) :=
  .single (.inl ⟨rfl, by decide, by decide⟩)

/-- A wide store followed by a narrower overlapping read is not a mixed-size race. -/
example : ¬ Mixed launch ex := by
  rintro ⟨e, f, a, b, l, ⟨hne, we, wf, he, hf, _⟩, _, _, _, hef, hfe⟩
  obtain ⟨e, heRef, heThread⟩ := Execution.NoTma.intent_thread no_async he
  obtain ⟨f, hfRef, hfThread⟩ := Execution.NoTma.intent_thread no_async hf
  subst heRef; subst hfRef
  have ec : e = (0, 0) ∨ e = (0, 1) := by
    rcases heThread with ⟨_, ⟨_, h⟩, _⟩ | ⟨_, ⟨_, h⟩, _⟩ | ⟨_, _, ⟨_, h⟩⟩ <;> exact event_cases h
  have fc : f = (0, 0) ∨ f = (0, 1) := by
    rcases hfThread with ⟨_, ⟨_, h⟩, _⟩ | ⟨_, ⟨_, h⟩, _⟩ | ⟨_, _, ⟨_, h⟩⟩ <;> exact event_cases h
  rcases ec with rfl | rfl <;> rcases fc with rfl | rfl
  · exact hne rfl
  · exact hef (.direct (.inl ordered))
  · exact hfe (.direct (.inl ordered))
  · exact hne rfl

-- Narrow loads decode the actual subrange of a wider integer store.
example : rebuild 3 ((payload.drop 4).map some) =
    .ok (.bits 32 0x88776655) := by
  norm_num [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte,
    Value.bitPattern, payload,
    Value.toBytes, Value.byteAt, Value.bytes, List.range_succ, Function.comp_def,
    pure, Except.pure, bind, Option.bind, BitVec.toNat_ofNat, BitVec.toNat_ofNatLT]

-- Separate narrower stores can jointly supply one wider read.
example : rebuild 3 (((Value.bits 32 0x44332211).toBytes ++
    (Value.bits 32 0x88776655).toBytes).map some) =
    .ok (.bits 64 0x8877665544332211) := by
  norm_num [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte,
    Value.bitPattern, payload,
    Value.toBytes, Value.byteAt, Value.bytes, List.range_succ, Function.comp_def,
    pure, Except.pure, bind, Option.bind, BitVec.toNat_ofNat, BitVec.toNat_ofNatLT]

-- A 16-byte load retains the high 64 bits, rather than truncating to 64 bits.
example : rebuild 3 (((Value.bits 32 0x44332211).toBytes ++
    (Value.bits 32 0x88776655).toBytes ++ (Value.bits 32 0xccbbaa99).toBytes ++
    (Value.bits 32 0x00ffeedd).toBytes).map some) =
    .ok (.pair (.bits 64 0x8877665544332211) (.bits 64 0x00ffeeddccbbaa99)) := by
  norm_num [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte,
    Value.bitPattern, payload,
    Value.toBytes, Value.byteAt, Value.bytes, List.range_succ, Function.comp_def,
    pure, Except.pure, bind, Option.bind, BitVec.toNat_ofNat, BitVec.toNat_ofNatLT]

end
end PTX.Tests.MixedAccess

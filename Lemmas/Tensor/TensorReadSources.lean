-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.ReadSources
public import Lemmas.Tensor.TensorMemory

@[expose] public section

/-! Connecting tensor byte effects to memory read sources.
These consequences do not require the whole transfer to have completed.
-/
namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A recorded tensor read of an immutable initialized byte returns that byte. -/
theorem tensor_readByte_of_initial (hX : Consistent L K A mem0 X)
    {i : EvId} {o : TensorCopy.Observation} {address x y k : Nat} {l : Loc} {b value : Byte}
    (ho : X.tensor i = some o) (hi : X.TensorIssue i address o.spec)
    (hl : TensorCopy.readLoc o.spec x y k = some l)
    (hr : TensorCopy.readByte o x y k = some b)
    (hm : mem0 l = some (some value))
    (hn : ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers l) : b = value := by
  have hread : X.MemReads (.async i (.read (.load x y k)))
      { loc := l, size := 1 } [some b] := ⟨o, address, b, ho, hi, hl, hr, rfl, rfl⟩
  have hv := read_initial_of_no_writer hX hread (k := 0) (by exact Nat.zero_lt_succ 0)
    (by simpa only [Loc.at, Nat.add_zero] using hm)
    (by simpa only [Loc.at, Nat.add_zero] using hn)
  simpa using hv

namespace TensorCopy

/-- A tensor write at an in-bounds source position copies its recorded read byte. -/
theorem CopyOk.readByte_of_writeByte {o : Observation} (hok : CopyOk o.spec o.effects)
    {x y k : Nat} {l : Loc} {b : Byte}
    (hl : readLoc o.spec x y k = some l)
    (hw : writeByte o x y k = some b) : readByte o x y k = some b := by
  cases hs : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [writeByte, hs] at hw
  | some slot =>
    have hsource : ∃ address, source o.spec slot = .global address := by
      cases hsrc : source o.spec slot with
      | global address => exact ⟨address, rfl⟩
      | fill mode format byte => simp [readLoc_source, hs, hsrc] at hl
    obtain ⟨address, hsource⟩ := hsource
    cases hwrite : o.effects.write slot with
    | none => simp [writeByte, hs, hwrite] at hw
    | some content =>
      have hc := hok.writes slot content hwrite
      rw [hsource] at hc
      obtain ⟨read, hr, rfl⟩ := hc
      have heq : read = b := by simpa [writeByte, hs, hwrite, Content.byte] using hw
      simp [readByte, hs, hr, heq]

end TensorCopy

/-- An actual tensor destination byte with an immutable initialized global source
has that source byte's value. This does not assert completion or visibility. -/
theorem tensor_writeByte_of_initial (hX : Consistent L K A mem0 X)
    {i : EvId} {o : TensorCopy.Observation} {address x y k : Nat} {l : Loc} {b value : Byte}
    (ho : X.tensor i = some o) (hi : X.TensorIssue i address o.spec)
    (hl : TensorCopy.readLoc o.spec x y k = some l)
    (hw : TensorCopy.writeByte o x y k = some b)
    (hm : mem0 l = some (some value))
    (hn : ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers l) : b = value := by
  have hok := (hX.tensor i o ho).2.1
  exact tensor_readByte_of_initial hX ho hi hl (hok.readByte_of_writeByte hl hw) hm hn

end
end PTX

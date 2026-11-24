-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

/-!
# A `tcgen05.shift` read races with an unordered MMA write (ERR-TMEM-RACE)

One thread issues, with nothing between them,

```
tcgen05.shift.cta_group::1.down [t];               // t = 0: reads lanes 1 to 31 of each chunk
tcgen05.mma.cta_group::1.kind::i8 [t], adesc, bdesc, idesc, {mask, mask, mask, mask}, 0;
                                                    // M = 128, N = 8, mask = 0x7fffffff:
                                                    // writes only lane 31 of each chunk
```

The shift reads lane 31 of the first chunk and the MMA writes it. §9.7.18.6.2 lists
"tcgen05.shift.cta_group::N (writes) -> tcgen05.mma.cta_group::N (A and metadata reads)" but no
pair from a shift's reads to an MMA's D writes, and "The asynchronous tcgen05 operations may
execute and complete in a different order than they were issued." Nothing observes either
completion, so the read and the write are unordered and the execution is unsafe, although the
shift's result is never read.
-/

namespace PTX.Tests.TmemShiftRace
open TcMma
noncomputable section

private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
private def smem : TcShared.Descriptor := ⟨0, 128, 256, 0, false, false, .none⟩
/-- `kind::i8`, M = 128, N = 8, `.cta_group::1`, D at Tensor Memory address 0. -/
private def spec : OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩, smem, smem, 0, 0,
    none, {}⟩
/-- Every output lane masked except lane 31 of each chunk. -/
private def masks : List Nat := List.replicate 4 0x7fffffff

private def X : Execution := {
  tr := fun t => if t = 0 then
    [⟨0, .tc (.shift ⟨0, [0]⟩)⟩, ⟨1, .tc (.mma 0 spec false masks)⟩] else []
  rf := fun _ _ => none }

/-- The cell of lane 31, column 0 of CTA 0. -/
private def cell : Cell := ⟨0, 31, 0⟩

-- The MMA writes the cell (row 31, column 0) despite the mask, and the shift reads it.
example : writeCell spec 0 masks 31 0 = some cell := by decide
private theorem mma_writes : TmemWrite L X (0, 1) cell :=
  .inl ⟨0, spec, false, masks, 31, 0, ⟨1, rfl⟩, by decide⟩
private theorem shift_reads : ShiftReadCell X (0, 0) cell :=
  ⟨⟨0, [0]⟩, ⟨0, rfl⟩, 0, 31, 0, by simp, by decide, by decide, by decide, rfl⟩

/-- `X` has no `mbarrier` wait, so no completion is observed. -/
private theorem no_observed (i w : EvId) (p : AsyncCopy.Part) (acq : Bool) (ws : MbarScope) :
    ¬ AsyncCopy.AsyncObserved X i p w acq ws := by
  rintro ⟨n, m, -, ⟨pc, parity, h⟩, -⟩
  obtain ⟨t, k⟩ := w
  rcases t with _ | t <;> rcases k with _ | _ | k <;> simp [Execution.get, X] at h

private theorem no_doneBefore (i e : EvId) : ¬ DoneBefore L X i e := by
  rintro (⟨w, ws, h, -⟩ | ⟨w, ⟨acq, ws, h, -⟩, -⟩) <;> exact no_observed _ _ _ _ _ h

/-- The shift (an operation that is no MMA, store or copy) and the MMA are ordered in neither
direction: no completion is observed and no pipelined pair of the table applies. -/
theorem shift_mma_race : ReadsUnsafe L X := by
  intro h
  rcases h .shift (0, 0) (0, 1) cell shift_reads mma_writes with he | he | he
  · simp at he
  · rcases he with (hd | ⟨-, -, d, s, a, m, d', s', a', m', -, ⟨pc, hs⟩, -⟩) |
      ⟨⟨a, v, sh, pc, hs⟩, -⟩ | ⟨-, -, c, d, s, a, m, ⟨pc, hs⟩, -⟩
    · exact no_doneBefore _ _ hd
    · simp [Execution.get, X] at hs
    · simp [Execution.get, X] at hs
    · simp [Execution.get, X] at hs
  · rcases he with he | hd
    · simp at he
    · exact no_doneBefore _ _ hd

end

end PTX.Tests.TmemShiftRace

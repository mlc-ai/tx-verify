-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.MmaCompletionFrame

namespace PTX.Tests.TcMmaReads
noncomputable section

private def desc : TcMma.Descriptor := ⟨.two, .f16 .f16 .f32, 256, 128, false, false, false, false,
    false⟩
private def smem : TcShared.Descriptor := ⟨1024, 0, 1024, 0, false, false, .b128⟩
private def spec : TcMma.OperandSpec := ⟨desc, smem, smem, 6, 7, none, {}⟩
private def issue : Event := ⟨0, .tc (.mma 0 spec true [])⟩
private def pending : Execution where
  tr := fun g => if g = 0 then [issue] else []
  rf := fun _ _ => none

private def values (b : Option Byte) : AsyncCopy.MmaOperands :=
  ⟨List.replicate (256 * 16 * 2) b, List.replicate (128 * 16 * 2) b⟩

private def observed (b : Option Byte) : Execution :=
  { pending with async := { mmaOperands := fun i =>
      if i = (0, 0) then some (values b) else none } }

private theorem footprint : pending.MmaFootprint (0, 0) true (64 * 16 * 2)
    ⟨.shared, 7, 1024⟩ :=
  .inl ⟨0, spec, true, [], ⟨0, rfl⟩, rfl⟩

-- Peer-CTA memory remains touched before the actual read occurs.
example : pending.Intent (.async (0, 0) (.mmaRead true (64 * 16 * 2)))
    { loc := ⟨.shared, 7, 1024⟩, size := 1 } false := ⟨rfl, rfl, footprint⟩
example (a : Acc) (bytes : List (Option Byte)) :
    ¬ pending.MemReads (.async (0, 0) (.mmaRead true 0)) a bytes := by
  simp [Execution.MemReads, Execution.MmaRead, pending]

private theorem actual (b : Option Byte) :
    (observed b).MmaRead (0, 0) true (64 * 16 * 2) ⟨.shared, 7, 1024⟩ b := by
  refine ⟨footprint, _, rfl, ?_⟩
  change (List.replicate 4096 b)[2048]? = some b
  simp only [List.getElem?_replicate]
  rfl

example (b : Option Byte) :
    (observed b).MemReads (.async (0, 0) (.mmaRead true (64 * 16 * 2)))
      { loc := ⟨.shared, 7, 1024⟩, size := 1 } [b] := (actual b).memReads

-- The effects rule accepts the real f16 issue and its full byte observations.
example (b : Option Byte) : AsyncCopy.TcEffectsOk (observed b) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    by_cases he : i = (0, 0)
    · subst i
      refine .inl ⟨0, spec, true, [], values b, ⟨0, rfl⟩, rfl, ?_, ?_, ?_⟩
      · decide
      · change (List.replicate 8192 b).length = 8192
        exact List.length_replicate
      · change (List.replicate 4096 b).length = 4096
        exact List.length_replicate
    · simp only [observed, AsyncCopy.Snapshot.mmaStarted, ite_eq_right he,
        Option.isSome_none, Bool.false_eq_true] at hi
  · intro i hi
    simp [observed] at hi

-- A fabricated value cannot pass RF even though the read bytes were left open.
example (a b : Byte) (hne : a ≠ b) :
    ¬ RfWf (fun _ => some (some a)) (observed (some b)) := by
  intro h
  have he := mma_read_w0 h (actual (some b)) rfl rfl
  have hb : b = a := by simpa [Execution.initialByte] using he
  exact hne hb.symm

-- The pending instruction creates an actual completion obligation.
example : ¬ AsyncDrained pending := by
  intro h
  have htc : pending.TcAsync (0, 0) := Or.inl ⟨0, spec, true, [], ⟨0, rfl⟩⟩
  have hd : pending.AsyncPresent (0, 0) .mmaDone :=
    h (0, 0) .mmaDone (.inr (.inr (.inr (.inl ⟨htc, rfl⟩))))
  simp [Execution.AsyncPresent, pending] at hd

-- The malformed empty lane mask is instead rejected by the actual issue rule.
example (L : Launch) (A : List Assumption) : ¬ TcMma.InstructionSafe L A pending := by
  intro h
  have hm := (h.1 (0, 0) 0 spec true [] ⟨0, rfl⟩).1.2.2.1.1
  cases hm

end
end PTX.Tests.TcMmaReads

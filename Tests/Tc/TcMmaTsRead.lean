-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

/-! The Tensor Memory A read rule (`ReadSource .a`, `AReadOk`): a word stored with
`tcgen05.st`, completed by `wait::st`, is what a later `[a-tmem]` MMA reads. Without the wait the
store is no source, and a completed MMA whose A read has no source is unsafe (`SourceUnsafe`,
ERR-TMEM-READ-SOURCE). -/
namespace PTX.Tests.TcMmaTsRead
open TcMma
noncomputable section

private def L : Launch := { grid := 1, block := 32, params := fun _ => none, clusterSize := 1 }
private def k8 : TcShared.Descriptor := ⟨1024, 128, 256, 0, false, false, .none⟩
private def i8x1 : Descriptor := ⟨.one, .i8 true true false, 128, 8, false, false, false, false,
    false⟩
-- A at Tensor Memory column 0, D at column 64.
private def spec : OperandSpec := ⟨i8x1, k8, k8, 0, 0, some 0, {}⟩
private def masks : List Nat := [0, 0, 0, 0]
private def w : Value := .bits 32 (BitVec.ofNat 64 0x04030201)

/-- Thread 0: store `w` to lane 0, column 0; wait::st; issue the MMA. -/
def X (ops : AsyncCopy.MmaOperands) : Execution where
  tr := fun g => if g = 0 then
      [⟨0, .tc (.st 0 [w] .s32x32b)⟩, ⟨1, .tc .waitSt⟩, ⟨2, .tc (.mma 64 spec false masks)⟩] else []
  rf := fun _ _ => none
  async := { mmaOperands := fun i => if i = (0, 2) then some ops else none }

private theorem writes (ops : AsyncCopy.MmaOperands) (other : EvId) (cell : Cell)
    (h : TmemWrite L (X ops) other cell) : other = (0, 0) ∨ other = (0, 2) := by
  obtain ⟨g, i⟩ := other
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, hp⟩, -⟩ | ⟨_, _, _, _, ⟨pc, hp⟩, -⟩ |
    ⟨_, _, _, _, ⟨pc, hp⟩, -⟩ | ⟨_, ⟨pc, hp⟩, -⟩ <;>
  · by_cases hg : g = 0
    · subst g
      match i with
      | 0 => exact .inl rfl
      | 2 => exact .inr rfl
      | 1 | _ + 3 => simp [Execution.get, X] at hp
    · simp [Execution.get, X, hg] at hp

-- Byte 0 of A is lane 0, column 0, byte 0 of the stored word.
example : aCell spec 0 = some (⟨0, 0, 0⟩, 0) := by decide

private theorem issue (ops : AsyncCopy.MmaOperands) :
    ∃ d s accum mask, (X ops).MmaIssue (0, 2) d s accum mask ∧ aCell s 0 = some (⟨0, 0, 0⟩, 0) :=
  ⟨64, spec, false, masks, ⟨2, rfl⟩, by decide⟩

private theorem wrote (ops : AsyncCopy.MmaOperands) : Wrote L [] (X ops) (0, 0) ⟨0, 0, 0⟩ w :=
  .inr (.inl ⟨0, [w], .s32x32b, 0, ⟨0, rfl⟩, rfl, rfl⟩)

theorem source (ops : AsyncCopy.MmaOperands) :
    ReadSource L (X ops) .a (0, 0) (0, 2) ⟨0, 0, 0⟩ := by
  refine ⟨by decide, .inr (.inl ⟨0, [w], .s32x32b, 0, ⟨0, rfl⟩, by simp, rfl⟩),
    .inr (.inl ⟨⟨_, _, _, ⟨0, rfl⟩⟩, .inl ⟨(0, 1), ⟨1, rfl⟩, rfl, by decide,
      .inl (.single (.inl ⟨rfl, by decide, by simp [X], by simp [X, SameAccess, Execution.get,
        Event.acc]⟩))⟩⟩), ?_, ?_⟩
  · intro other ho
    rcases writes ops other _ ho with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inl rfl))
  · intro key r hr
    simp [X] at hr

-- In any execution satisfying the rule, the MMA read the stored byte, not an arbitrary one.
example (ops : AsyncCopy.MmaOperands) (h : ReadOk L [] (X ops)) :
    ops.a[0]? = some (some (w.byteAt 0)) :=
  h.2 (0, 2) 0 ⟨0, 0, 0⟩ 0 (0, 0) w ops (issue ops) (source ops) (wrote ops) (by simp [X])
    (by decide)

-- So a recorded A byte that differs from the stored one is excluded.
example (b : Byte) (hb : b ≠ w.byteAt 0) (h : ReadOk L [] (X ⟨[some b], []⟩)) : False := by
  have := h.2 (0, 2) 0 ⟨0, 0, 0⟩ 0 (0, 0) w ⟨[some b], []⟩ (issue _) (source _) (wrote _)
    (by simp [X]) (by decide)
  simp at this
  exact hb this

-- Without the wait::st, the store is not ordered before the MMA and is no A source.
def Y : Execution where
  tr := fun g => if g = 0 then
    [⟨0, .tc (.st 0 [w] .s32x32b)⟩, ⟨2, .tc (.mma 64 spec false masks)⟩] else []
  rf := fun _ _ => none
  async := { mmaDone := fun i => i = (0, 1) }

theorem notBefore : ¬ WriteBefore L Y (0, 0) (0, 1) := by
  intro hb
  rcases hb with (((⟨w', ws, ⟨n, m, -, ⟨pc, p, hw⟩, -⟩, -, -⟩ |
      ⟨w', ⟨acq, sc, ⟨n, m, -, ⟨pc, p, hw⟩, -⟩, -⟩, -⟩) |
      ⟨-, -, d, sp, a, mk, -, -, -, -, ⟨pc, hx⟩, -⟩) | ⟨-, hw | ⟨-, -, -, hk⟩ | ⟨-, -, -, hk⟩⟩ |
      ⟨-, -, _, _, _, _, _, ⟨pc, hc⟩, -⟩)
  · obtain ⟨g, i⟩ := w'
    by_cases hg : g = 0
    · subst g; match i with
      | 0 | 1 | _ + 2 => simp [Execution.get, Y] at hw
    · simp [Execution.get, Y, hg] at hw
  · obtain ⟨g, i⟩ := w'
    by_cases hg : g = 0
    · subst g; match i with
      | 0 | 1 | _ + 2 => simp [Execution.get, Y] at hw
    · simp [Execution.get, Y, hg] at hw
  · simp [Execution.get, Y] at hx
  · obtain ⟨w', ⟨pc, hp⟩, hw1, -, -⟩ := hw
    obtain ⟨g, i⟩ := w'
    simp only at hw1; subst hw1
    match i with
    | 0 | 1 | _ + 2 => simp [Execution.get, Y] at hp
  · obtain ⟨_, _, _, pc, hp⟩ := hk; simp [Execution.get, Y] at hp
  · obtain ⟨_, _, _, pc, hp⟩ := hk; simp [Execution.get, Y] at hp
  · simp [Execution.get, Y] at hc

example : ¬ ReadSource L Y .a (0, 0) (0, 1) ⟨0, 0, 0⟩ := fun ⟨_, _, hb, _⟩ => notBefore hb

private theorem writesY (other : EvId) (cell : Cell) (h : TmemWrite L Y other cell) :
    other = (0, 0) ∨ other = (0, 1) := by
  obtain ⟨g, i⟩ := other
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, hp⟩, -⟩ | ⟨_, _, _, _, ⟨pc, hp⟩, -⟩ |
    ⟨_, _, _, _, ⟨pc, hp⟩, -⟩ | ⟨_, ⟨pc, hp⟩, -⟩ <;>
  · by_cases hg : g = 0
    · subst g
      match i with
      | 0 => exact .inl rfl
      | 1 => exact .inr rfl
      | _ + 2 => simp [Execution.get, Y] at hp
    · simp [Execution.get, Y, hg] at hp

-- The completed MMA of `Y` reads A byte 0 from a cell without a source: unsafe.
example : SourceUnsafe L [] Y := by
  intro h
  obtain ⟨source, value, ⟨hne, hw, hb, -⟩, -⟩ :=
    h .a (0, 1) ⟨0, 0, 0⟩ ⟨by simp [Y], 64, spec, false, masks, 0, 0, ⟨2, rfl⟩, by decide⟩
  rcases writesY source _ hw with rfl | rfl
  · exact notBefore hb
  · exact hne rfl

end
end PTX.Tests.TcMmaTsRead

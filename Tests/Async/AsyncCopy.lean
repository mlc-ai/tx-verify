-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncCopy
public import Core.Data.Events
public import Core.Assembly.Waiting

namespace PTX.Tests.AsyncCopy
open PTX.AsyncCopy
noncomputable section

def mbar : Loc := ⟨.shared, 0, 64⟩
def src : Acc := { loc := ⟨.global, 0, 0⟩, size := 16 }
def dst : Acc := { loc := ⟨.shared, 0, 0⟩, size := 16 }
def spec : Spec := { src := src, dst := dst, completion := .mbarrier mbar }

theorem copyOk_iff {e : Effects} : CopyOk spec e ↔ spec.src.size = spec.dst.size ∧
    (∀ bs, e.readBytes = some bs → bs.length = spec.src.size) ∧
    (∀ bs, e.writeBytes = some bs → e.readBytes = some bs) ∧
    (e.notified = true → ∃ bs, e.writeBytes = some bs) ∧ ElemsOk spec e := by
  rw [copyOk_iff_of_size_eq rfl rfl rfl rfl]
  tauto
def bytes : List Byte := List.replicate 16 (.bits 32 7, 0)
def readOnly : Effects := { readBytes := some bytes, notified := false }
def written : Effects := { readBytes := some bytes, writeBytes := some bytes }
def done : Effects := { readBytes := some bytes, writeBytes := some bytes, notified := true }

def issued : EvId → Option Spec := fun i => if i = (0, 0) ∨ i = (0, 1) then some spec else none

-- The second issued copy may have completed while the first has no effects yet.
def laterFirst : Snapshot where
  copies := fun i => if i = (0, 1) then done else {}

theorem done_ok : CopyOk spec done := by
  refine copyOk_iff.2 ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro bs h; cases h; rfl
  · intro bs h; exact h
  · intro _; exact ⟨bytes, rfl⟩
  · simp [ElemsOk, done]

theorem later_first_valid : WellFormed issued laterFirst := by
  intro i hi
  by_cases h : i = (0, 1)
  · subst i; exact ⟨spec, by simp [issued], done_ok⟩
  · obtain ⟨p, hp⟩ := hi
    cases p <;> simp [present, laterFirst, h] at hp

-- Issue and the destination write are distinct from the completion notification.
example : CopyOk spec written ∧ ¬ present written (.notify .copy) := by
  refine ⟨copyOk_iff.2 ⟨rfl, ?_, ?_, ?_, ?_⟩, by simp [present, written]⟩
  · intro bs h; cases h; rfl
  · intro bs h; exact h
  · intro h; cases h
  · simp [ElemsOk, written]

example : CopyOk spec readOnly := by
  refine copyOk_iff.2 ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro bs h; cases h; rfl
  · intro bs h; cases h
  · intro h; cases h
  · simp [ElemsOk, readOnly]

-- Neither notification without a write, nor a different value at the destination,
-- can be justified by this copy's operation rule.
example : ¬ CopyOk spec { readBytes := some bytes, notified := true } := by
  intro h; replace h := copyOk_iff.1 h; obtain ⟨bs, hb⟩ := h.2.2.2.1 rfl; cases hb

example : ¬ CopyOk spec { readBytes := some bytes, writeBytes := some [] } := by
  intro h
  replace h := copyOk_iff.1 h
  have hc := h.2.2.1 [] rfl
  have : bytes = [] := Option.some.inj hc
  have hlen := congrArg List.length this
  simp [bytes] at hlen

-- A notification belongs to the actual issuing copy, not to a nearby instruction.
example (X : Execution) :
    ¬ StageEdge X (.async (0, 1) (.write .copy)) (.async (0, 0) (.notify .copy)) := by
  simp [StageEdge]

example (X : Execution) : ¬ StageEdge X (.async (0, 1) (.notify .copy)) (.thread (0, 2)) := by
  simp [StageEdge]

example : ¬ Notification issued laterFirst (0, 0) mbar 16 := by
  rintro ⟨s, _, h, _⟩
  change (false : Bool) = true at h
  cases h

example : Notification issued laterFirst (0, 1) mbar 16 :=
  ⟨spec, by simp [issued], rfl, rfl, rfl⟩

-- Whole-execution extension preserves the RF of every actual async read.
example (X Y : Execution) (h : X.le Y) (a : Acc) (bs : List (Option Byte))
    (hr : X.MemReads (.async (0, 1) (.read .copy)) a bs)
    (hx : X.rf (.async (0, 1) (.read .copy)) 0 = none) :
    Y.rf (.async (0, 1) (.read .copy)) 0 = none := by
  rw [h.2.1 _ 0 ⟨a, bs, hr⟩, hx]

-- An orphan write has no instruction authorizing it.
example (X : Snapshot) (hw : (X.copies (9, 9)).writeBytes = some bytes) :
    ¬ WellFormed issued X := by
  intro h
  have hp : nonempty (X.copies (9, 9)) := ⟨.write .copy, by simp [present, hw]⟩
  obtain ⟨s, hs, _⟩ := h (9, 9) hp
  simp [issued] at hs

end
end PTX.Tests.AsyncCopy

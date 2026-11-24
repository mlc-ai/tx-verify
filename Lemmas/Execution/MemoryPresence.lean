-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Async.AsyncCopy

@[expose] public section

namespace PTX
noncomputable section
open AsyncCopy
variable {X : Execution}

/-- Actual memory observations have dependency-graph nodes. -/
theorem Execution.MemReads.present {e : Ref} {a : Acc} {bs : List (Option Byte)}
    (h : X.MemReads e a bs) : X.RefPresent e := by
  cases e with
  | thread e =>
    obtain ⟨pc, hh⟩ | ⟨new, pc, hh⟩ := h
    · exact ⟨⟨pc, .rd a bs⟩, hh⟩
    · exact ⟨⟨pc, .rmw a bs new⟩, hh⟩
  | async i p =>
    cases p <;> simp only [Execution.MemReads] at h
    case readCopy =>
      obtain ⟨_, _, _, _, hh, _⟩ := h
      simp [Execution.RefPresent, Execution.AsyncPresent, hh]
    case oldElem j =>
      obtain ⟨_, _, raw, _, _, _, hh, _⟩ := h
      simp [Execution.RefPresent, Execution.AsyncPresent, hh]
    case mmaRead b k =>
      obtain ⟨value, hi, _, _⟩ := h
      exact ⟨a.loc, value, hi⟩
    case readLoad x y k =>
      obtain ⟨o, _, b, ho, _, _, hb, _, _⟩ := h
      exact ⟨o, ho, by simp [hb]⟩
    case readStore x y k =>
      obtain ⟨o, _, b, ho, _, _, hb, _, _⟩ := h
      exact ⟨o, ho, by simp [hb]⟩
    case oldStore x y k =>
      obtain ⟨o, _, b, ho, _, _, _, hb, _, _⟩ := h
      exact ⟨o, ho, by simp [hb]⟩

theorem Execution.MemWrites.present {e : Ref} {a : Acc} {bs : List Byte}
    (h : X.MemWrites e a bs) : X.RefPresent e := by
  cases e with
  | thread e =>
    obtain ⟨pc, hh⟩ | ⟨old, pc, hh⟩ := h
    · exact ⟨⟨pc, .wr a bs⟩, hh⟩
    · exact ⟨⟨pc, .rmw a old (some bs)⟩, hh⟩
  | async i p =>
    cases p <;> simp only [Execution.MemWrites] at h
    case writeCopy =>
      obtain ⟨_, _, _, hh⟩ := h
      simp [Execution.RefPresent, Execution.AsyncPresent, hh]
    case writeElem j =>
      obtain ⟨_, _, _, hh⟩ := h
      simp [Execution.RefPresent, Execution.AsyncPresent, hh]
    case writeStore x y k =>
      obtain ⟨o, _, b, ho, _, _, hb, _, _, _, _, _⟩ := h
      exact ⟨o, ho, by simp [hb]⟩
    case writeLoad x y k =>
      obtain ⟨o, _, b, ho, _, _, hb, _, _, _, _, _⟩ := h
      unfold TensorCopy.writeByte at hb
      cases hs : TensorTransfer.slotAt o.spec.descriptor x y k with
      | none => simp [hs] at hb
      | some slot =>
        cases hw : o.effects.write slot with
        | none => simp [hs, hw] at hb
        | some v => exact ⟨o, slot, v, ho, hs, hw⟩
    case writeCta c =>
      obtain ⟨s, targets, hi, ht, hw⟩ := h
      exact hw.1

end
end PTX

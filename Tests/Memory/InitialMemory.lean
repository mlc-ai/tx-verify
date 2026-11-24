-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.InitialMemory

@[expose] public section

/-! Reads-from regressions for allocated but unspecified initial bytes. The copy fixture
exercises the memory rule itself; it is not a complete kernel or an mbarrier protocol. -/
namespace PTX.Tests.InitialMemory
open PTX
noncomputable section

def src : Acc := { loc := ⟨.global, 0, 64⟩, size := 16 }
def dst : Acc := { loc := ⟨.shared, 0, 128⟩, size := 16 }
def mb : Loc := ⟨.shared, 0, 256⟩
def unknown : Mem0 := fun _ => some none

def bytes (choice : Loc → Byte) : List Byte :=
  (List.range src.size).map (fun k => choice (src.loc.at k))

def copy (choice : Loc → Byte) : Execution where
  tr := fun g => if g = 0 then [⟨0, .copy { src := src, dst := dst, completion := .mbarrier mb }⟩]
    else []
  rf := fun _ _ => none
  async := { copies := fun i => if i = (0, 0) then
    { readBytes := some (bytes choice), writeBytes := some (bytes choice) } else {} }
  initial := choice

theorem copy_read {choice : Loc → Byte} :
    (copy choice).MemReads (.async (0, 0) (.read .copy)) src ((bytes choice).map some) :=
  ⟨{ src := src, dst := dst, completion := .mbarrier mb }, bytes choice, ⟨0, rfl⟩, rfl, rfl, rfl⟩

/-- Every fixed choice of the sixteen unspecified source bytes can be copied. -/
theorem copy_rf (choice : Loc → Byte) : RfWf unknown (copy choice) := by
  intro e a bs he
  cases e with
  | thread e =>
    obtain ⟨g, j⟩ := e
    rcases he with ⟨pc, he⟩ | ⟨new, hnew⟩
    · simp only [Execution.get, copy] at he
      split_ifs at he with hg
      · cases j <;> simp_all
      · simp at he
    · obtain ⟨pc, he⟩ := hnew
      simp only [Execution.get, copy] at he
      split_ifs at he with hg
      · cases j <;> simp_all
      · simp at he
  | async i p =>
    cases p with
    | readCopy =>
      obtain ⟨s, raw, hc, hsrc, hr, hbs⟩ := he
      by_cases hi : i = (0, 0)
      · subst hi
        obtain ⟨pc, hb⟩ := hc
        simp only [Execution.get, copy, ↓reduceIte, List.getElem?_cons_zero,
          Option.some.injEq, Event.mk.injEq, Kind.copy.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        simp only [copy, ↓reduceIte, Option.some.injEq] at hr
        subst raw
        subst hbs
        subst hsrc
        refine ⟨by simp [bytes], ?_⟩
        intro k hk c hc
        cases hc
        simp [bytes, List.getElem?_map, List.getElem?_range hk,
          Execution.initialByte, copy]
      · simp [copy, hi] at hr
    | oldElem j =>
      obtain ⟨s, r, x, hc, hw, helem, hx, hbs⟩ := he
      by_cases hi : i = (0, 0) <;> simp [copy, hi] at hx
    | _ => simp [Execution.MemReads, Execution.MmaRead, copy] at he

/-- The same arbitrary bytes can be present at the destination; no missing-byte
placeholder is required, and the asynchronous copy's own rules are satisfied. -/
theorem copy_effects (choice : Loc → Byte) :
    AsyncCopy.WellFormed (AsyncCopy.issuedBy (copy choice)) (copy choice).async := by
  intro i hi
  by_cases h : i = (0, 0)
  · subst h
    refine ⟨{ src := src, dst := dst, completion := .mbarrier mb }, rfl, by decide, ?_, ?_, ?_, ?_⟩
    · intro bs hb
      change some (bytes choice) = some bs at hb
      cases hb
      simp [bytes]
    · intro bs hb; exact hb
    · intro hf; cases hf
    · simp [AsyncCopy.ElemsOk, AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets,
        AsyncCopy.Spec.elemWidth, AsyncCopy.sourceBytes, copy]
  · obtain ⟨p, hp⟩ := hi
    change AsyncCopy.present (if i = (0, 0) then
      { readBytes := some (bytes choice), writeBytes := some (bytes choice) } else {}) p at hp
    rw [ite_eq_right h] at hp
    cases p <;> simp [AsyncCopy.present] at hp

/-- A known initial byte overrides the execution's arbitrary choice. -/
example {X : Execution} {mem0 : Mem0} (hrf : RfWf mem0 X)
    {e : AsyncCopy.Ref} {bs : List (Option Byte)} (he : X.MemReads e src bs)
    (he0 : X.rf e 0 = none) {b : Byte} (hb : mem0 (src.loc.at 0) = some (some b)) :
    bs[0]? = some (some b) := initial_read_byte hrf he (by decide) he0 hb

/-- Allocated unknown memory cannot return the old `none` placeholder as its byte. -/
example {X : Execution} (hrf : RfWf unknown X)
    {e : AsyncCopy.Ref} {bs : List (Option Byte)} (he : X.MemReads e src bs)
    (he0 : X.rf e 0 = none) : bs[0]? ≠ some none := by
  rw [initial_read_byte hrf he (by decide) he0 (show unknown (src.loc.at 0) = some none from rfl)]
  simp [Execution.initialByte]

/-- Once an unknown byte is observed, a different value at the same location cannot
also be read from W0. This covers thread and async reads equally. -/
example {X : Execution} (hrf : RfWf unknown X)
    {e f : AsyncCopy.Ref} {xs ys : List (Option Byte)}
    (he : X.MemReads e src xs) (hf : X.MemReads f src ys)
    (he0 : X.rf e 0 = none) (hf0 : X.rf f 0 = none) : xs[0]? = ys[0]? :=
  initial_reads_agree hrf he hf (by decide) (by decide) he0 hf0 rfl rfl

end
end PTX.Tests.InitialMemory

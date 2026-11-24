-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open Epilogue (Scan)

private abbrev okD (d : Correction.D) := schedulerSite d.site = true

private theorem ite_ok {a b : Correction.D} {c : Bool} (ha : okD a) (hb : okD b) :
    okD (Correction.D.ite c a b) := by cases c <;> assumption

private theorem scan_ok {p late d gx cur} : okD (scanExit p late d gx cur) := ite_ok rfl rfl
private theorem loop_ok {p L g late d grp acc} : okD (loopHead p L g late d grp acc) :=
  ite_ok scan_ok (ite_ok rfl rfl)
private theorem total_ok {p L g k d x} : okD (afterTotal p L g k d x) := by
  cases k with
  | first | second => exact ite_ok scan_ok loop_ok
  | loop | loop2 => exact ite_ok loop_ok scan_ok

private def okNext : Option (Option Correction.D) → Prop
  | some (some d) => okD d
  | _ => True

private theorem word_ok {v : Value} {f : BitVec 64 → Correction.D} (h : ∀ x, okD (f x)) :
    okNext (word32 v f) := by
  unfold word32
  split
  · exact h _
  · trivial

private theorem tiles_ok {p L g d x} : okNext ((afterTiles p L g d x).map some) := by
  unfold afterTiles
  dsimp only
  split
  · split
    · exact ite_ok rfl rfl
    · trivial
  · trivial

/-- The final named barrier is the scheduler's only exit into the data-processing region. -/
theorem scheduler_succ {p L g} {d d' : Correction.D} {e : Event}
    (hs : schedulerSite d.site = true) (hn : d.site ≠ .nb 1)
    (he : Correction.succ p L g d e = some (some d')) : schedulerSite d'.site = true := by
  suffices h : okNext (Correction.succ p L g d e) by rw [he] at h; exact h
  obtain ⟨s, v, k⟩ := d
  cases s with
  | setmax | bar1 | free | barEnd | exit => trivial
  | arr i =>
    fin_cases i
    · rfl
    · exact ite_ok rfl rfl
  | nb i =>
    fin_cases i
    · rfl
    · exact (hn rfl).elim
  | word i | q0 | q1 | uk =>
    simp only [Correction.succ]
    split
    · split
      · exact word_ok (fun _ => rfl)
      · trivial
    · trivial
  | down i =>
    simp only [Correction.succ]
    split
    · exact word_ok (fun _ => rfl)
    · trivial
  | up i j =>
    simp only [Correction.succ]
    split
    · apply word_ok
      intro x
      fin_cases j <;> rfl
    · trivial
  | total i =>
    simp only [Correction.succ]
    split
    · exact word_ok (fun _ => total_ok)
    · trivial
  | vote late =>
    simp only [Correction.succ]
    split
    · exact ite_ok rfl rfl
    · trivial
  | pre late =>
    simp only [Correction.succ]
    split
    · apply word_ok
      intro x
      cases late <;> rfl
    · trivial
  | tiles late =>
    simp only [Correction.succ]
    split
    · split
      · cases late
        · exact tiles_ok
        · rfl
      · trivial
    · trivial
  | wend late =>
    simp only [Correction.succ]
    split
    · rename_i _ _ ok _ _ _
      cases ok <;> rfl
    · trivial
  | _ => cases hs

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

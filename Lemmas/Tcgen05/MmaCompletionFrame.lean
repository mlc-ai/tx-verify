-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Tc.TcMmaCompletion

@[expose] public section

section
namespace PTX
noncomputable section

/-- MMA operand observations participate in the same RF relation as other reads. -/
theorem Execution.MmaRead.memReads {X : Execution} {i : EvId} {isB : Bool}
    {index : Nat} {l : Loc} {b : Option Byte} (h : X.MmaRead i isB index l b) :
    X.MemReads (.async i (.mmaRead isB index)) { loc := l, size := 1 } [b] :=
  ⟨b, h, rfl, rfl⟩

/-- W0 can supply only its actual initial byte, even for a peer-CTA MMA read. -/
theorem mma_read_w0 {X : Execution} {mem0 : Mem0} (hrf : RfWf mem0 X)
    {i : EvId} {isB : Bool} {index : Nat} {l : Loc} {b : Option Byte}
    (hr : X.MmaRead i isB index l b)
    (hs : X.rf (.async i (.mmaRead isB index)) 0 = none)
    {initial : Option Byte} (hm : mem0 l = some initial) :
    b = X.initialByte initial l := by
  have h := (hrf _ _ _ hr.memReads).2 0 (by exact Nat.zero_lt_succ 0)
  rw [hs] at h
  have he := h initial (by simpa [Loc.at] using hm)
  simpa [Loc.at] using he

end
end PTX
end

section
namespace PTX.TcMma
noncomputable section

/-- A single-operation arithmetic-completion candidate is ready only after its
actual qualifying source predecessors have completed. -/
def CompletionReady (L : Launch) (X : Execution) (i : EvId) : Prop :=
  ∀p,CompletionPrecedes L X p i → X.async.mmaDone p=true

/-- An MMA issue is in its thread's trace and is no memory operation. -/
private theorem mmaIssue_po {X : Execution} {i j : EvId} {d : Nat} {s : OperandSpec}
    {a : Bool} {m : List Nat} (hj : X.MmaIssue j d s a m) (hg : i.1 = j.1) (hlt : i.2 < j.2) :
    po X i j := by
  obtain ⟨pc, he⟩ := hj
  refine ⟨hg, hlt, (List.getElem?_eq_some_iff.mp he).1, fun hh => ?_⟩
  have h := hh.1
  rw [he] at h
  simp [Event.acc] at h

/-- On one thread in program order, the D→D pipeline condition reduces to the issues: the
`TcBefore` conjunct is program order. -/
theorem completionPrecedes_iff {L : Launch} {X : Execution} {i j : EvId} :
    CompletionPrecedes L X i j ↔ i.1 = j.1 ∧ i.2 < j.2 ∧ SameWarp L i.1 j.1 ∧
      (∃ d s a m d' s' a' m', X.MmaIssue i d s a m ∧ X.MmaIssue j d' s' a' m' ∧
        SameAccumulator d s d' s') ∧ SameWrites X i j := by
  constructor
  · rintro ⟨hg, hlt, ⟨hw, -, hi⟩, hs⟩
    exact ⟨hg, hlt, hw, hi, hs⟩
  · rintro ⟨hg, hlt, hw, ⟨d, s, a, m, d', s', a', m', hi, hj, hsa⟩, hs⟩
    exact ⟨hg, hlt, ⟨hw, .inl (.single (.inl (mmaIssue_po hj hg hlt))),
      d, s, a, m, d', s', a', m', hi, hj, hsa⟩, hs⟩

theorem sameWrites_congr {X Y : Execution}
    (h : ∀ i d s a m, X.MmaIssue i d s a m ↔ Y.MmaIssue i d s a m) {i j : EvId} :
    SameWrites X i j ↔ SameWrites Y i j := by
  constructor <;> rintro ⟨d, s, a, m, d', s', a', m', hi, hj, hrest⟩
  · exact ⟨d, s, a, m, d', s', a', m', (h ..).mp hi, (h ..).mp hj, hrest⟩
  · exact ⟨d, s, a, m, d', s', a', m', (h ..).mpr hi, (h ..).mpr hj, hrest⟩

/-- The domain depends only on actual source issues, never async observations. -/
theorem completionPrecedes_congr {L : Launch} {X Y : Execution}
    (h : ∀ i d s a m, X.MmaIssue i d s a m ↔ Y.MmaIssue i d s a m)
    {i j : EvId} : CompletionPrecedes L X i j ↔ CompletionPrecedes L Y i j := by
  simp only [completionPrecedes_iff, sameWrites_congr h, h]

/-- Pure source/effect frame for one operation's D-write completion. -/
theorem completionClosed_update {L : Launch} {X Y : Execution} {i : EvId}
    (hissues : ∀p d s a m,X.MmaIssue p d s a m ↔Y.MmaIssue p d s a m)
    (hdone : ∀p,Y.async.mmaDone p=if p=i then true else X.async.mmaDone p)
    (hX : CompletionClosed L X) (hready : CompletionReady L X i) : CompletionClosed L Y := by
  intro p q hp hq
  have hpold : CompletionPrecedes L X p q := (completionPrecedes_congr hissues).mpr hp
  rw [hdone p]
  by_cases he : p=i
  · simp [he]
  · simp only [ite_eq_right he]
    by_cases hqi : q=i
    · subst q
      exact hready p hpold
    · exact hX p q hpold (by simpa only [hdone q,ite_eq_right hqi] using hq)
end
end PTX.TcMma
end

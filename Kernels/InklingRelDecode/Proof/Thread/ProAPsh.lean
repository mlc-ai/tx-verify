-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ClassBt

@[expose] public section

/-!
# The received words of the prologue's broadcasts along the machine

The machine records the word the broadcast of block `j` (`psh0`, `psh1`, `psh2`) received
(`shOf dt j`). For the layers above, which prove what the word is in an execution
(`Interface.pshSo_all`):

* `pshAfter j`: the sites of block `j` after its broadcast (the election that reads the word,
  the four copies, the loads and barriers between them);
* `sh_next`: a step from a site other than a broadcast keeps the three words;
* `pshAfter_next`: a step into a site after the broadcast of block `j` is from such a site or
  from the broadcast;
* `next_psh`: the step at the broadcast of block `j` records the received word as word `j` and
  keeps the others.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The broadcast of the warp index in block `j`. -/
def pshSite : Nat → Site
  | 0 => .psh0
  | 1 => .psh1
  | _ => .psh2

/-- The sites of block `j` after its broadcast. -/
def pshAfter : Nat → List Site
  | 0 => [.pel0_0, .ptc0_0, .pbC0, .pel0_1, .ptc0_1, .lbB0, .pbD0, .pel0_2, .ptc0_2, .pbE0,
      .pel0_3, .ptc0_3]
  | 1 => [.pel1_0, .ptc1_0, .pbC1, .pel1_1, .ptc1_1, .lbB1, .pbD1, .pel1_2, .ptc1_2, .pbE1,
      .pel1_3, .ptc1_3]
  | 2 => [.pel2_0, .ptc2_0, .pbC2, .pel2_1, .ptc2_1, .lbB2, .pbD2, .pel2_2, .ptc2_2, .pbE2,
      .pel2_3, .ptc2_3]
  | _ => []

/-- The three broadcast sites. -/
def pshSites : List Site := [.psh0, .psh1, .psh2]

theorem pelSite_after {j : Nat} (hj : j < 3) : pelSite j ∈ pshAfter j := by
  interval_cases j <;> decide

theorem ptcSite_after {i : Nat} (hi : i < 12) : ptcSite i ∈ pshAfter (i / 4) := by
  interval_cases i <;> decide

/-- **A step from a site other than a broadcast keeps the three received words.** -/
theorem sh_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hs : s ∉ pshSites) :
    d'.dt.sh0 = dt.sh0 ∧ d'.dt.sh1 = dt.sh1 ∧ d'.dt.sh2 = dt.sh2 := by
  cases s <;> first
    | exact absurd (by decide) hs
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h; simp_all [elDt, qUpd]))

/-- The first site of the query loads is none of the sites after a broadcast. -/
theorem qSite_not_pshAfter {L : Launch} {g : Nat} (dt : Dat) (G j : Nat) :
    qSite L g dt G ∉ pshAfter j := by
  have h : ∀ G, qSite L g dt G = .ldq0 ∨ qSite L g dt G = .ldq16 ∨ qSite L g dt G = .ldq32 ∨
      qSite L g dt G = .ldq48 ∨ qSite L g dt G = .stq0_0 := by
    intro G
    unfold qSite
    split <;> (repeat' split) <;> simp
  rcases h G with h | h | h | h | h <;> rw [h] <;> (match j with
    | 0 | 1 | 2 => decide
    | j + 3 => simp [pshAfter])

/-- **A step into a site after the broadcast of block `j` is from such a site or from the
broadcast.** -/
theorem pshAfter_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) :
    ∀ j < 3, d'.site ∈ pshAfter j → s ∈ pshAfter j ∨ s = pshSite j := by
  cases s <;> first
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h
            dsimp only
            first
              | decide
              | (intro j _ hm; exact absurd hm (qSite_not_pshAfter _ _ _))))

/-- **The step at the broadcast of block `j`**: the event is a shuffle, its received word is
recorded as word `j`, the other two are kept, and the machine moves to the election after it. -/
theorem next_psh {L : Launch} {g j : Nat} (hj : j < 3) {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨pshSite j, dt⟩ e = some (some d')) :
    ∃ m av b c recv ok, e.kind = .shfl m av b c recv ok ∧ shOf d'.dt j = recv ∧
      d'.site = pelSite j ∧ ∀ i < 3, i ≠ j → shOf d'.dt i = shOf dt i := by
  obtain ⟨pc, k⟩ := e
  interval_cases j
  all_goals
    simp only [pshSite, next] at h
    cases k <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, fun i hi hne => ?_⟩
    interval_cases i <;> first | rfl | exact absurd rfl hne

end
end PTX.Kernels.InklingRelDecode.Proof.ProA

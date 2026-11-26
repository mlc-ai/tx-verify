-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
public import Lemmas.Flow.StrictLift
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictRole

@[expose] public section

/-! # The hand-offs of warpgroup 1's dispatch level, and its strict step for one event

The loop-glue facts of `wg1_steps` (`Common/Sound.lean`), as theorems: the exits' stubs
(`wg1_hstub`), the hand-off to each sub-role (`wg1_hrole`), the returns (`wg1_hback`) and the
sub-roles' first states not returning (`wg1_hinit`). With them the strict step of one state for
one event (`Code.StepFor`) of the head or of a sub-role is the strict step of the level
(`wg1_inl_stepFor`, `wg1_inr_stepFor`), and of the whole thread (`thread_wg1_stepFor`,
`thread_start_stepFor`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

theorem wg1_hstub : ∀ d r, wg1Enter P L g d = some r → (wg1HeadCode P L g).inv d →
    (wg1HeadCode P L g).pc d = SubEntry.pc P L g r ∧ (wg1HeadCode P L g).sub d = 0 ∧
      (wg1HeadCode P L g).acc d = [] ∧ StubSite kernel (SubEntry.pc P L g r) = true := by
  intro d r hx _
  refine ⟨?_, ?_, ?_, sub_sites r⟩
  all_goals
    cases d <;> simp only [wg1Enter, Wg1.exitOf, Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;> rfl

theorem wg1_hrole : ∀ d r i t, wg1Enter P L g d = some r → subSel P L g r d = some i →
    (wg1HeadCode P L g).AtD d t → (wg1HeadCode P L g).inv d →
    (subFrag P L g i).AtD (subFrag P L g i).init t ∧
      (subFrag P L g i).inv (subFrag P L g i).init := by
  intro d r i t hx hs hat _
  simp only [subSel] at hs
  split_ifs at hs
  obtain rfl := Option.some.inj hs
  cases d <;> simp only [wg1Enter, Wg1.exitOf, Option.map_some, Option.map_none,
    Option.some.injEq, reduceCtorEq] at hx <;> subst hx
  · exact ⟨head_mma hat, trivial⟩
  · exact ⟨head_tma hat, trivial⟩
  · exact ⟨hat, Index.IxSite.elems_pos _⟩
  · exact ⟨hat, trivial⟩

theorem wg1_hback : ∀ i d p t, subBack P L g i d = some p → (subFrag P L g i).AtD d t →
    (subFrag P L g i).inv d → (wg1HeadCode P L g).AtD p t ∧ (wg1HeadCode P L g).inv p := by
  intro i d p t hb hat _
  cases i with
  | mma =>
    simp only [subBack] at hb
    split_ifs at hb with hl
    obtain rfl := Option.some.inj hb
    exact ⟨mmaLeave d t hl hat, trivial⟩
  | tma =>
    simp only [subBack] at hb
    split_ifs at hb with hl
    obtain rfl := Option.some.inj hb
    exact ⟨tmaLeave d t hl hat, trivial⟩
  | _ => cases hb

theorem wg1_hinit : ∀ i, subBack P L g i (subFrag P L g i).init = none := by
  intro i; cases i <;> rfl


/-- **The strict step of a head state for one event, at the dispatch level.** -/
theorem wg1_inl_stepFor {s : Wg1.Site} {e : Event}
    (hP : Wg1.exitOf s = none → (wg1HeadCode P L g).StepFor s e) :
    (wg1Code P L g).StepFor (Sum.inl s) e :=
  Code.roleLoop_inl_stepFor (fun hx => hP (by simpa [wg1Enter] using hx)) wg1_hstub wg1_hrole
    wg1_hinit

/-- **The strict step of a sub-role's state for one event, at the dispatch level.** -/
theorem wg1_inr_stepFor {i : SubEntry} {d : (subFrag P L g i).D} {e : Event}
    (h : subBack P L g i d = none → (subFrag P L g i).StepFor d e) :
    (wg1Code P L g).StepFor (.inr ⟨Sum.inl i, d⟩) e :=
  Code.roleLoop_inr_stepFor h wg1_hstub wg1_hrole wg1_hback wg1_hinit

/-- **A step of the thread machine at a state of warpgroup 1**, from the level's. -/
theorem thread_wg1_stepFor {s : (wg1Code P L g).D} {n : Cls → Nat} {e : Event}
    (h : (wg1Code P L g).StepFor s e) :
    (thread P L g).StepFor (.inr ⟨Sum.inl Entry.wg1, s⟩, n) e :=
  Code.counted_stepFor (Code.glue_inr_stepFor (i := Sum.inl Entry.wg1) h) n

/-- **A step of the thread machine at a startup state** is strict. -/
theorem thread_start_stepFor {m : Mem0} (hp : Pre P L m) {d : (startupCode P L g).D}
    {n : Cls → Nat} {e : Event} : (thread P L g).StepFor (.inl d, n) e :=
  Code.counted_stepFor (Code.glue_inl_stepFor
    (fun hx => (startup_steps hp d hx).stepFor e) thread_handoff) n

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

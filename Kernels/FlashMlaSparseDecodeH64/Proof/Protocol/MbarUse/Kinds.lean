-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Assumptions

@[expose] public section

/-! # The kinds of the kernel's mbarrier events

From `mbar_use` only: an event that names an mbarrier is an initialization, an arrival, a poll,
a `tcgen05.commit` or a tensor load (`use_kind`). So no event invalidates an mbarrier, none is a
`cp.async` arrival, a linear copy completing on one or a cluster launch control request
(`no_inval`, `no_asyncArrive`, `no_copy`, `no_clc`), and `fam_eq` reads the family and the CTA
off an object's location. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {X : Execution}

/-- The five kinds of an mbarrier event. -/
def MbarKind (e : Event) (l : Loc) : Prop :=
  (∃ c, e.kind = .mbInit l c) ∨ (∃ tx, MbarRow.Arrive e l tx) ∨ (∃ q, MbarRow.Wait e l q) ∨
    MbarRow.Commit e l ∨ ∃ n, MbarRow.Issue e l n

/-- **The kind of a use.** -/
theorem use_kind {g k : Nat} {e : Event} {l : Loc} (hu : MbarUse L X g k e l) :
    MbarKind e l := by
  rcases hu with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ _ hk => exact .inr (.inl ⟨_, hk⟩)
    | coordReady _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | qkDone _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | coordFree _ _ hk => exact .inr (.inl ⟨_, hk⟩)
    | soReady _ _ hk => exact .inr (.inl ⟨_, hk⟩)
    | svDone _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
  · cases h with
    | qLoad _ _ hk => exact .inr (.inr (.inr (.inr ⟨_, hk⟩)))
    | qArrive _ _ hk => exact .inr (.inl ⟨_, hk⟩)
    | qWait _ _ hk _ => exact .inr (.inr (.inl ⟨_, hk⟩))
    | qCommit _ _ hk => exact .inr (.inr (.inr (.inl hk)))
    | qCopyWait _ _ hk _ => exact .inr (.inr (.inl ⟨_, hk⟩))
    | kvWait _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | qkCommit _ _ hk => exact .inr (.inr (.inr (.inl hk)))
    | soWait _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | svCommit _ _ hk => exact .inr (.inr (.inr (.inl hk)))
  · cases h with
    | qWait _ _ hk _ => exact .inr (.inr (.inl ⟨_, hk⟩))
    | lastWait _ _ hk _ => exact .inr (.inr (.inl ⟨_, hk⟩))
    | coordWait _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | freeWait _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | rawLoad _ _ hk => exact .inr (.inr (.inr (.inr ⟨_, hk⟩)))
    | rawArrive _ _ hk => exact .inr (.inl ⟨_, hk⟩)
    | coordFree _ _ hk => exact .inr (.inl ⟨_, hk⟩)
  · cases h with
    | freeWait _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | readyArrive _ _ hk => exact .inr (.inl ⟨_, hk⟩)
  · cases h with
    | qWait _ _ hk _ => exact .inr (.inr (.inl ⟨_, hk⟩))
    | rawWait _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | svWait _ _ hk => exact .inr (.inr (.inl ⟨_, hk⟩))
    | readyArrive _ _ hk => exact .inr (.inl ⟨_, hk⟩)
    | freeArrive _ _ hk => exact .inr (.inl ⟨_, hk⟩)

variable {m : Mem0}

/-- An mbarrier event of a launched thread is of one of the five kinds. -/
theorem mbar_kind (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {i : EvId} {e : Event} {l : Loc} (he : X.get i = some e) (hm : Frame.MbarOf e l) :
    MbarKind e l :=
  use_kind (mbar_use hR (Frame.lt_of_get hX he) he hm)

/-- An mbarrier event is not undefined behaviour. -/
theorem notUb_of_kind {e : Event} {l : Loc} (h : MbarKind e l) : ∀ f, e.kind ≠ .ub f := by
  intro f hf
  rcases h with ⟨c, hc⟩ | ⟨tx, hc⟩ | ⟨q, ok, hc⟩ | ⟨s, hc, -⟩ | ⟨n, a, s, hc, -⟩
  · rw [hf] at hc; exact Kind.noConfusion hc
  · unfold MbarRow.Arrive at hc; rw [hf] at hc; exact Kind.noConfusion hc
  all_goals rw [hf] at hc; exact Kind.noConfusion hc

/-- **No event invalidates an mbarrier.** -/
theorem no_inval (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    (i : EvId) (l : Loc) : ¬ X.MbInval i l := by
  rintro ⟨pc, he⟩
  rcases mbar_kind hX hR he rfl with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, hc, -⟩ |
    ⟨_, _, _, hc, -⟩ <;> cases hc

/-- **No event is a `cp.async` arrival.** -/
theorem no_asyncArrive (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {i : EvId} {pc : Nat} {l : Loc} {noinc : Bool}
    (he : X.get i = some ⟨pc, .asyncArrive l noinc⟩) : False := by
  rcases mbar_kind hX hR he rfl with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, hc, -⟩ |
    ⟨_, _, _, hc, -⟩ <;> cases hc

/-- **No linear copy completes on an mbarrier.** -/
theorem no_copy (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {i : EvId} {pc : Nat} {s : AsyncCopy.Spec} {l : Loc} (he : X.get i = some ⟨pc, .copy s⟩)
    (hc : s.completion = .mbarrier l) : False := by
  rcases mbar_kind hX hR he hc with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, hc, -⟩ |
    ⟨_, _, _, hc, -⟩ <;> cases hc

/-- **No cluster launch control request targets an mbarrier.** -/
theorem no_clc (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat} {c : Nat}
    (he : X.get i = some ⟨pc, .clcIssue sp tg⟩) (hc : c ∈ tg) : False := by
  rcases mbar_kind hX hR he (l := { sp.mbar with cta := c }) ⟨c, hc, rfl⟩ with
    ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, hc, -⟩ |
    ⟨_, _, _, hc, -⟩ <;> cases hc

/-- **An object's location names its family and CTA.** -/
theorem fam_eq {c c' : Nat} {f f' : MbarFam} (h : mbarLoc L c f = mbarLoc L c' f') :
    c = c' ∧ f = f' := by
  simp only [mbarLoc, Loc.mk.injEq, true_and] at h
  exact ⟨h.1, MbarFam.off_inj (by omega)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

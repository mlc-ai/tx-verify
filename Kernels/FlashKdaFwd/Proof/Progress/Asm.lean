-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions
public import Kernels.FlashKdaFwd.Proof.Progress.Lead
public import Kernels.FlashKdaFwd.Proof.Progress.Wf
public import Lemmas.Snoc.PlainAsyncExtend

@[expose] public section

/-!
# The assumptions' execution constraints on the extensions a progress proof builds

A progress proof extends a consistent execution by one more event (or by one instance of a
warp-wide event, or by one stage of an asynchronous operation), and the extension must again
satisfy the execution constraint (`Assumption.wf`) of every assumption of the kernel. Two of the
six assumptions of this kernel have a constraint:

* `electZero`: every election over the full member mask elects lane 0 (`LeaderZero`);
* `inputReadOnly`: a plain read at one of the 21 loads of the packed-offsets array returns, at
  every byte of that array whose launch content is known, the launch content.

Both constraints look only at the threads' events. So they survive an extension that adds no
memory read and whose new full-mask elections elect lane 0 (`wf_ext`). The corollaries below
are the forms the extension lemmas of the library ask for (`hasm` premises):

* `wf_snoc`, `wf_snocObject`: one appended event that is no read and no election (a store, a
  fence, an mbarrier operation, a poll, a barrier arrival, an issue of a copy, an exit, an
  undefined-behaviour event);
* `wf_appendLanes`: events appended to the lanes of a warp, none a read, every election
  electing lane 0 (`QuietFor 0`): a shuffle, a matrix instance, an election with leader 0;
* `wf_tr`, `wfStoreExtensions_all`, `wfCtaHistory_all`: an extension with the same thread
  events (a stage of an asynchronous copy, appended barrier records);
* `wf_snoc_read`: one appended read whose bytes have sources (`NewRead`), when at an offsets
  load no write of the execution covers a byte of the offsets array that it reads (then every
  such byte comes from launch memory, which is what `inputReadOnly` demands);
  `wf_snoc_read_of_noOffsetWrite` derives that from the absence of the assumption's undefined
  behaviour, which the safety proof establishes.

`wfStepE_all` states the same in the shape of the library's `Assumption.WfStep`, with one more
premise: the extension adds no election (`WfStepE`, `Wf.lean`). It is the hypothesis of the
progress steps of this directory. The library's `Assumption.WfStep` itself (every extension
that adds no read) is FALSE for this assumption list, because an extension may add an election
with a leader other than 0 (`not_wfStep`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Step PTX.Kernels.FlashKdaFwd

variable {L : Launch} {K : Kernel} {mem0 : Mem0} {X Y : Execution}

/-- Every full-mask election of `Y` is an election of `X` or elects lane 0. -/
def ElectsZeroOver (X Y : Execution) : Prop :=
  ∀ e pc inst leader, Y.Elect e pc 0xffffffff inst leader →
    X.Elect e pc 0xffffffff inst leader ∨ leader = 0

/-- **The constraints survive an extension that adds no read and whose new full-mask elections
elect lane 0.** -/
theorem wf_ext (hX : ∀ a ∈ Assumptions.all, a.wf L mem0 X) (hr : X.NoNewRead Y)
    (he : ElectsZeroOver X Y) : ∀ a ∈ Assumptions.all, a.wf L mem0 Y := by
  intro a ha
  have hz : Assumptions.LeaderZero X := hX Assumptions.electZero (by simp [Assumptions.all])
  have hi := hX Assumptions.inputReadOnly (by simp [Assumptions.all])
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · intro e pc inst leader h
    rcases he e pc inst leader h with h' | h'
    · exact hz e pc inst leader h'
    · exact h'
  · intro e pc acc bs hget hs
    exact hi e pc acc bs (hr e _ hget rfl) hs

/-- The constraints of a consistent execution. -/
theorem wf_of_consistent (hX : Consistent L K Assumptions.all mem0 X) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 X := fun a ha => hX.asm a ha

/-- **Every full-mask election of a consistent execution elects lane 0.** -/
theorem leaderZero (hX : Consistent L K Assumptions.all mem0 X) :
    ∀ e pc inst l, X.Elect e pc 4294967295 inst l → l = 0 :=
  hX.asm Assumptions.electZero (by simp [Assumptions.all])

/-- Lane 0 is a member of the full mask. -/
theorem zero_member : electMember 4294967295 0 := Sched.full_member (by decide)

/-- **One appended event that is no read and no election keeps the constraints.** -/
theorem wf_snoc (hX : Consistent L K Assumptions.all mem0 X) {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (hr : e.kind.readsMem = false)
    (he : ∀ mask inst l, e.kind ≠ .elect mask inst l) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.snoc g e r) := by
  refine wf_ext (wf_of_consistent hX) (Execution.noNewRead_snoc hr) ?_
  intro v pc inst leader h
  unfold Execution.Elect at h ⊢
  rw [snoc_get] at h
  split_ifs at h
  · exact absurd (by rw [Option.some.inj h]) (he 4294967295 inst leader)
  · exact .inl h

/-- **One appended event with a record in an object's history keeps the constraints**, when the
event is no read and no election (an mbarrier initialization, arrival or poll). -/
theorem wf_snocObject (hX : Consistent L K Assumptions.all mem0 X) {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} {mb : Loc} {rec : MBarrier.Record AsyncCopy.Ref}
    (hr : e.kind.readsMem = false) (he : ∀ mask inst l, e.kind ≠ .elect mask inst l) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.snocObject g e r mb rec) := by
  refine wf_ext (wf_of_consistent hX)
    ((Execution.noNewRead_snoc (r := r) hr).trans (Execution.noNewRead_of_tr rfl)) ?_
  intro v pc inst leader h
  unfold Execution.Elect at h ⊢
  change (X.snoc g e r).get v = _ at h
  rw [snoc_get] at h
  split_ifs at h
  · exact absurd (by rw [Option.some.inj h]) (he 4294967295 inst leader)
  · exact .inl h

/-- **Events appended to the lanes of a warp keep the constraints**, when none is a read and
every election among them elects lane 0. -/
theorem wf_appendLanes (hX : Consistent L K Assumptions.all mem0 X) (ds : List Nat)
    (ev : Nat → Event) (h : ∀ x, QuietFor 0 (ev x).kind) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.appendLanes ds ev) := by
  refine wf_ext (wf_of_consistent hX) (noNewRead_appendLanes fun x => (h x).1) ?_
  intro v pc inst leader hv
  rcases appendLanes_get_cases hv with ⟨-, hx⟩ | ⟨-, -, hq⟩
  · exact .inl hx
  · exact .inr ((h v.1).2 4294967295 inst leader (by rw [← hq]))

/-- **An extension with the same thread events keeps the constraints.** -/
theorem wf_tr (hX : Consistent L K Assumptions.all mem0 X) (htr : Y.tr = X.tr) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 Y := by
  refine wf_ext (wf_of_consistent hX) (Execution.noNewRead_of_tr htr) ?_
  intro v pc inst leader h
  unfold Execution.Elect Execution.get at h ⊢
  rw [htr] at h
  exact .inl h

/-- **The constraints survive the stages of a tensor store**: the premise of the library's
store-completion lemmas (`Step.StoreDone.pending_issue_visible_of_effects`). -/
theorem wfStoreExtensions_all :
    Step.StoreDone.WfStoreExtensions L K mem0 Assumptions.all :=
  fun _ _ hX _ htr _ _ => wf_tr hX htr

/-- **The constraints survive the append of records to a CTA barrier's history**: the premise of
the library's release of a `bar.sync` whose participants have all arrived, in the form that does
not go through `Assumption.WfStep` (`NamedBar.sync_release_of_wf`). -/
theorem wfCtaHistory_all :
    Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) Assumptions.all :=
  fun _ _ _ hX => wf_tr hX rfl

/-- **One appended read whose bytes have sources keeps the constraints**, when at a load of the
packed-offsets array no write of the execution covers a byte of the array that it reads: each
such byte then has no write source, so it is the launch byte. -/
theorem wf_snoc_read (hX : Consistent L K Assumptions.all mem0 X) {g pc : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)}
    (hread : NewRead L mem0 X g e r a bs)
    (hfresh : Assumptions.inputReadSites.contains pc = true →
      ∀ k < a.size, Assumptions.OffsetByte L (a.loc.at k) →
      ∀ w a' bs', X.MemWrites w a' bs' → ¬ a'.Covers (a.loc.at k)) :
    ∀ a' ∈ Assumptions.all, a'.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r) := by
  intro a' ha'
  have hz := leaderZero hX
  have hi := hX.asm Assumptions.inputReadOnly (by simp [Assumptions.all])
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · intro v pc' inst leader h
    unfold Execution.Elect at h
    rw [snoc_get] at h
    split_ifs at h
    · cases h
    · exact hz v pc' inst leader h
  · intro v pc' acc bs' hv hs
    rw [snoc_get] at hv
    split_ifs at hv
    · simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      intro k hk hoff c hc
      have hsrc := hread.src k hk
      cases hrk : r k with
      | none =>
        rw [hrk] at hsrc
        simpa [Execution.initialByte] using hsrc _ hc
      | some w =>
        rw [hrk] at hsrc
        obtain ⟨a'', bs'', hw, hcov, -⟩ := hsrc
        exact absurd hcov (hfresh hs k hk hoff w a'' bs'' hw)
    · exact hi v pc' acc bs' hv hs

/-- **An appended read keeps the constraints when no operation of the execution writes a byte
of the packed-offsets array**, that is, when the undefined-behaviour clause of `inputReadOnly`
does not hold. The safety proof shows exactly that (it is one disjunct of `Unsafe`), so the
premise `readWf` of the progress skeleton needs no fact about the addresses of the loads. -/
theorem wf_snoc_read_of_noOffsetWrite (hX : Consistent L K Assumptions.all mem0 X)
    (hub : ¬ Assumptions.inputReadOnly.ub L mem0 X) {g pc : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)}
    (hread : NewRead L mem0 X g e r a bs) :
    ∀ a' ∈ Assumptions.all, a'.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r) :=
  wf_snoc_read hX hread fun _ _ _ hoff w a' _ hw hcov => hub ⟨w, a', _, hw.intent, hcov, hoff⟩

/-! ### The interface of the progress steps -/

/-- **The constraints survive every extension of a consistent execution that adds no memory
read and no election** (`WfStepE`, `Wf.lean`): the hypothesis under which the progress steps of
this directory are stated. It is the library's `Assumption.WfStep` with one more premise. -/
theorem wfStepE_all {sel : Nat → Bool} : WfStepE sel L K mem0 Assumptions.all :=
  fun _ _ hX _ _ hr he =>
    wf_ext (wf_of_consistent hX) hr fun e _ _ _ h => .inl (he e _ h rfl)

/-- **The library's `Assumption.WfStep` is false for this assumption list**, as soon as one
consistent execution exists: appending to it an election over the full mask with leader 5 adds
no memory read and performs no commit arrive-on, and breaks `LeaderZero`. So the progress
templates that take `Assumption.WfStep` as a hypothesis cannot be applied to this kernel; the
restatements under `WfStepE` (`Free.lean`, `Wait.lean`, `Barrier.lean`, `TensorLoad.lean`) are
used instead, with `wfStepE_all`. -/
theorem not_wfStep {sel : Nat → Bool} (hX : Consistent L K Assumptions.all mem0 X) :
    ¬ Assumption.WfStep sel L K mem0 Assumptions.all := by
  intro h
  have hz : Assumptions.LeaderZero
      (X.snoc 0 ⟨0, .elect 4294967295 0 5⟩ (fun _ => none)) :=
    h X _ hX le_snoc (Execution.notifiedInOrder_of_eq rfl) (Execution.noNewRead_snoc rfl)
      Assumptions.electZero (by simp [Assumptions.all])
  have h5 := hz (0, (X.tr 0).length) 0 0 5 (by
    unfold Execution.Elect
    rw [snoc_get]
    simp)
  cases h5

end PTX.Kernels.FlashKdaFwd.Proof.Progress

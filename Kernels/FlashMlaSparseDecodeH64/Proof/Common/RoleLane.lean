-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # A lane's synchronizing events are its role's

The general part of "a lane of the role's warps polls, arrives, commits and issues only at pcs of
its role, so its trace-level prefix counts are the role's ledger counts":

* `lane_role`: a synchronizing event (`PollCommit`: a successful poll, a commit, a tensor issue
  or an mbarrier arrival) of a lane is fired from a state of a working role (`RoleAt`), at a pc
  of no quiet role (the startup, warpgroup 1's head and idle code fire none);
* `count_role`: if every synchronizing event of a lane is at a pc of the role (`inRole`), the
  lane's prefix count of a synchronizing predicate `p` is the role's ledger count of the class
  that is `p` inside the role; `okPoll_sync`, `arrives_sync`, `commits_sync`, `issues_sync` are
  the four predicates' side conditions;
* `take_noUb_of`: no event before a thread's event is undefined behaviour.

A role's instance (`Common/{Mma,Tma,Dequant,Wg0}Lane.lean`) proves `<lane>_inRole` from
`lane_role` (its `RoleAt` case, the exit's shape, `omega` on the warp for the others) and each
count by `count_role` with its class's `cls` unfolding. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat} {f : Event}

/-- A successful poll, a commit, a tensor copy or an mbarrier arrival. -/
def PollCommitK (K : Kind) : Prop :=
  (∃ l q a sc, K = .wait l q true a sc) ∨ (∃ s, K = .tc (.commit s)) ∨
    (∃ a s, K = .tensorIssue a s) ∨ ∃ l tx c r sc, K = .arrive l tx c r sc

/-- An event of `PollCommitK`. -/
def PollCommit (f : Event) : Prop := PollCommitK f.kind

/-- An exit synchronizes nothing. -/
theorem exit_not_sync (hx : f.kind = .exit) (hk : PollCommit f) : False := by
  unfold PollCommit PollCommitK at hk
  rw [hx] at hk
  simp at hk

/-- **The role of a synchronizing event**: fired from a state of a working role, at a pc of no
startup, head or idle state. -/
theorem lane_role (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hf : X.get (g, j) = some f) (hk : PollCommit f) :
    ∃ σ, RoleAt P L g f.pc σ ∧ (table P L).Ev g σ f ∧ 103 ≤ f.pc ∧ f.pc ≠ 1842 ∧
      f.pc ≠ 1843 ∧ ∀ s n, σ ≠ (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, s⟩⟩, n) := by
  have no : ∀ K : Kind, f.kind = K → ¬ PollCommitK K → False := fun K hK hn =>
    hn (hK ▸ hk)
  have hub : ∀ fl, f.kind ≠ .ub fl := fun fl h => no _ h (by simp [PollCommitK])
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw hf hub
  have h := state_role hJ hi
  rw [← hpc] at h
  refine ⟨σ, h, hev, ?_⟩
  cases h with
  | startup d n _ _ hx _ _ =>
    exfalso
    obtain ⟨site, x1, x2⟩ := d
    cases site with
    | sh j => fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev <;> exact no _ hk (by simp [PollCommitK])
    | elect j => obtain ⟨inst, ld, -, hk⟩ := hev; exact no _ hk (by simp [PollCommitK])
    | init n => exact no _ hev (by simp [PollCommitK])
    | fence | alloc | relinq | bar => exact no _ hev (by simp [PollCommitK])
    | allocSt => obtain ⟨col, -, hk⟩ := hev; exact no _ hk (by simp [PollCommitK])
    | ld =>
      rcases hev with ⟨a, bs, hk, -⟩ | ⟨fl, hk⟩
      · exact no _ hk (by simp [PollCommitK])
      · exact hub fl hk
    | trap => exact (hub _ hev).elim
    | enter r => simp [Startup.exitOf] at hx
  | head s n hs =>
    exfalso
    rcases hs with rfl | rfl
    · obtain ⟨inst, hk⟩ := hev
      exact no _ hk (by simp [PollCommitK])
    · obtain ⟨r, ok, hk⟩ := hev
      exact no _ hk (by simp [PollCommitK])
  | idle s n =>
    exfalso
    cases s with
    | ldA | ldB =>
      rcases hev with ⟨a, bs, hk⟩ | ⟨fl, hk⟩
      · exact no _ hk (by simp [PollCommitK])
      · exact hub fl hk
    | bar | ret => exact no _ hev (by simp [PollCommitK])
  | _ => exact ⟨by omega, by omega, by omega, fun s n h => by cases h⟩

/-- An event of the lane's first `k` is an event of the lane. -/
theorem get_of_mem_take {k : Nat} (hf : f ∈ (X.tr g).take k) : ∃ j, X.get (g, j) = some f := by
  obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem (List.mem_of_mem_take hf)
  exact ⟨j, by rw [← hfj]; exact List.getElem?_eq_getElem hj⟩

/-- **A lane's count of a synchronizing predicate is its role's**: every synchronizing event of
the lane is at a pc of the role, and inside the role the class `c` is the predicate `p`. -/
theorem count_role {inRole p c : Event → Bool}
    (hin : ∀ j f, X.get (g, j) = some f → PollCommit f → inRole f = true)
    (hps : ∀ f, p f = true → PollCommit f) (hc : ∀ f, c f = (inRole f && p f)) (k : Nat) :
    ((X.tr g).take k).countP p = ((X.tr g).take k).countP c := by
  refine List.countP_congr fun f hf => ?_
  obtain ⟨j, hj⟩ := get_of_mem_take hf
  rw [hc]
  constructor
  · intro h
    simp [hin j f hj (hps f h), h]
  · intro h
    simp only [Bool.and_eq_true] at h
    exact h.2

/-- A successful poll synchronizes. -/
theorem okPoll_sync {l : Loc} (h : okPoll l f = true) : PollCommit f := by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | wait l' q ok a sc => cases ok <;> simp_all [PollCommit, PollCommitK, sourceWaitSuccess]
  | _ => simp [sourceWaitSuccess] at h

/-- An arrival synchronizes. -/
theorem arrives_sync {l : Loc} (h : arrivesOn l f = true) : PollCommit f := by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | arrive l' tx c r sc => exact .inr (.inr (.inr ⟨l', tx, c, r, sc, rfl⟩))
  | _ => simp [sourceArrive] at h

/-- A commit synchronizes. -/
theorem commits_sync {l : Loc} (h : MbarRow.commitsTo l f = true) : PollCommit f := by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | tc t =>
    cases t with
    | commit s => exact .inr (.inl ⟨s, rfl⟩)
    | _ => simp [MbarRow.commitsTo] at h
  | _ => simp [MbarRow.commitsTo] at h

/-- A tensor issue synchronizes. -/
theorem issues_sync {l : Loc} (h : issuesTo l f = true) : PollCommit f := by
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | tensorIssue a s => exact .inr (.inr (.inl ⟨a, s, rfl⟩))
  | _ => simp [issuesTo] at h

/-- **No event before a thread's event is undefined behaviour** (it would be the thread's last),
so a class of undefined behaviour counts none. -/
theorem take_noUb_of {c : Event → Bool} (hc : ∀ f, c f = true → ∃ fl, f.kind = .ub fl)
    {k : Nat} {e : Event} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, k) = some e) : ((X.tr g).take k).countP c = 0 := by
  refine List.countP_eq_zero.mpr fun f hf hcl => ?_
  obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem hf
  have hjk : j < k := by simp only [List.length_take] at hj; omega
  have hget : X.get (g, j) = some f := by
    show (X.tr g)[j]? = some f
    rw [← List.getElem?_take_of_lt hjk, List.getElem?_eq_getElem hj, hfj]
  obtain ⟨fl, hfl⟩ := hc f hcl
  obtain ⟨pc, kd⟩ := f
  simp only at hfl
  subst hfl
  have := ub_last hX hget he
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

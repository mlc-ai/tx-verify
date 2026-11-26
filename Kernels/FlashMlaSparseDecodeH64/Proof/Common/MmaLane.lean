-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane

@[expose] public section

/-! # The MMA lane's polls and commits are its role's

The MMA instance of `Common/RoleLane.lean`: a lane of warp 4 synchronizes only at pcs of the MMA
code (`lane4_inRole`), so its prefix counts of successful polls and of commits on an object are
the MMA ledger's (`lane4_okPolls`, `lane4_commits`), before which no event is undefined behaviour
(`take_noUb`). For the MMA role's trace-level exports, which import this file privately. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat} {f : Event}

/-- **A lane of warp 4 polls successfully, commits, issues tensor copies and arrives only at pcs
of the MMA code.** -/
theorem lane4_inRole (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 4) (hf : X.get (g, j) = some f) (hk : PollCommit f) :
    Mma.inRole f = true := by
  obtain ⟨σ, h, hev, h0, h1, h2, hid⟩ := lane_role hp hX hFw hf hk
  cases h with
  | mma d n _ _ _ _ _ hr =>
    rcases hr with hr | ⟨hx, -⟩
    · simp only [Mma.inRole, decide_eq_true_eq]
      omega
    · obtain ⟨-, hk'⟩ : Mma.Ev L g d f := hev
      unfold Mma.EvK at hk'
      rw [hx] at hk'
      exact (exit_not_sync hk' hk).elim
  | idle s n => exact absurd rfl (hid s n)
  | _ => exfalso; omega

/-- **A lane of warp 4's successful polls on `l` are the MMA ledger's.** -/
theorem lane4_okPolls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 4) (k : Nat) (l : Loc) :
    okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (Mma.cls (.acq l)) :=
  count_role (fun _ _ hj hk => lane4_inRole hp hX hFw hw hj hk) (fun _ => okPoll_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf, sourceWaitSuccess, eq_comm]
      | tc t => cases t <;> simp [Mma.cls, Mma.kindOf, sourceWaitSuccess]
      | _ => simp [Mma.cls, Mma.kindOf, sourceWaitSuccess]) k

/-- **A lane of warp 4's commits addressing `l` are the MMA ledger's.** -/
theorem lane4_commits (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 4) (k : Nat) (l : Loc) :
    ((X.tr g).take k).countP (MbarRow.commitsTo l) =
      ((X.tr g).take k).countP (Mma.cls (.commit l)) :=
  count_role (fun _ _ hj hk => lane4_inRole hp hX hFw hw hj hk) (fun _ => commits_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf, MbarRow.commitsTo]
      | tc t => cases t <;> simp [Mma.cls, Mma.kindOf, MbarRow.commitsTo]
      | _ => simp [Mma.cls, Mma.kindOf, MbarRow.commitsTo]) k

/-- **No event before a thread's event is undefined behaviour** (it would be the thread's last). -/
theorem take_noUb {k : Nat} {e : Event} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, k) = some e) : ((X.tr g).take k).countP (Mma.cls .ub) = 0 :=
  take_noUb_of (fun f h => by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | ub fl => exact ⟨fl, rfl⟩
    | wait l q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at h
    | tc t => cases t <;> simp [Mma.cls, Mma.kindOf] at h
    | _ => simp [Mma.cls, Mma.kindOf] at h) hX he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

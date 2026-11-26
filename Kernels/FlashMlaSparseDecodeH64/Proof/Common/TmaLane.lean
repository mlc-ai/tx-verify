-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane

@[expose] public section

/-! # The TMA lane's polls and arrivals are its role's

The TMA instance of `Common/RoleLane.lean`: a lane of warp 5 synchronizes only at pcs
of the TMA code (`lane5_inRole`), so its prefix counts of successful polls and of arrivals on
an object are the TMA ledger's (`lane5_okPolls`, `lane5_arrivals`), as are its tensor loads
(`lane5_issues`), before which no event is
undefined behaviour (`lane5_take_noUb`). For the TMA role's trace-level exports, which import this
file privately. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat} {f : Event}

/-- **A lane of warp 5 synchronizes only at pcs of the TMA code.** -/
theorem lane5_inRole (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 5) (hf : X.get (g, j) = some f)
    (hk : PollCommit f) : Tma.inRole f = true := by
  obtain ⟨σ, h, hev, h0, h1, h2, hid⟩ := lane_role hp hX hFw hf hk
  cases h with
  | tma d n _ _ _ _ _ hr =>
    rcases hr with hr | ⟨hx, -⟩
    · simp only [Tma.inRole, decide_eq_true_eq]
      omega
    · obtain ⟨-, hk'⟩ : Tma.Ev L g d f := hev
      unfold Tma.EvK at hk'
      rw [hx] at hk'
      exact (exit_not_sync hk' hk).elim
  | idle s n => exact absurd rfl (hid s n)
  | _ => exfalso; omega

/-- **A lane of warp 5's successful polls on `l` are the TMA ledger's.** -/
theorem lane5_okPolls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 5) (k : Nat) (l : Loc) :
    okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (Tma.cls (.acq l)) :=
  count_role (fun _ _ hj hk => lane5_inRole hp hX hFw hw hj hk) (fun _ => okPoll_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc =>
        cases ok <;> simp [Tma.cls, Tma.kindOf, sourceWaitSuccess, eq_comm]
      | _ => simp [Tma.cls, Tma.kindOf, sourceWaitSuccess]) k

/-- **A lane of warp 5's arrivals on `l` are the TMA ledger's.** -/
theorem lane5_arrivals (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 5) (k : Nat) (l : Loc) :
    arrivals l ((X.tr g).take k) = ((X.tr g).take k).countP (Tma.cls (.arrive l)) :=
  count_role (fun _ _ hj hk => lane5_inRole hp hX hFw hw hj hk) (fun _ => arrives_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc => cases ok <;> simp [Tma.cls, Tma.kindOf, sourceArrive]
      | _ => simp [Tma.cls, Tma.kindOf, sourceArrive, eq_comm]) k

/-- **A lane of warp 5's tensor loads on `l` are the TMA ledger's gathers on `l`.** -/
theorem lane5_issues (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 5) (k : Nat) (l : Loc) :
    ((X.tr g).take k).countP (issuesTo l) = ((X.tr g).take k).countP (Tma.cls (.gather l)) :=
  count_role (fun _ _ hj hk => lane5_inRole hp hX hFw hw hj hk) (fun _ => issues_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc => cases ok <;> simp [Tma.cls, Tma.kindOf, issuesTo]
      | _ => simp [Tma.cls, Tma.kindOf, issuesTo, eq_comm]) k

/-- **No event before a thread's event is undefined behaviour** (it would be the thread's last). -/
theorem lane5_take_noUb {k : Nat} {e : Event} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, k) = some e) : ((X.tr g).take k).countP (Tma.cls .ub) = 0 :=
  take_noUb_of (fun f h => by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | ub fl => exact ⟨fl, rfl⟩
    | wait l q ok a sc => cases ok <;> simp [Tma.cls, Tma.kindOf] at h
    | _ => simp [Tma.cls, Tma.kindOf] at h) hX he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

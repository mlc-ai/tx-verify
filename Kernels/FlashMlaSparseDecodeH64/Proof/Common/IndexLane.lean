-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane

@[expose] public section

/-! # The index warp's polls and arrivals are its role's

The index-warp instance of `Common/RoleLane.lean`: a lane of warp 7 synchronizes only at pcs of
the index code (`ix_inRole`), so its prefix counts of successful polls and of arrivals on an
object are the index warp's ledger's (`ix_okPolls`, `ix_arrivals`), before which no event is
undefined behaviour (`ix_take_noUb`). For the index warp's trace-level exports, which import this
file privately. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat} {f : Event}

/-- **A lane of warp 7 synchronizes only at pcs of the index code.** -/
theorem ix_inRole (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 7) (hf : X.get (g, j) = some f)
    (hk : PollCommit f) : Index.inRole f = true := by
  obtain ⟨σ, h, hev, h0, h1, h2, hid⟩ := lane_role hp hX hFw hf hk
  cases h with
  | index d n _ _ _ hr =>
    rcases hr with hr | ⟨hx, -⟩
    · simp only [Index.inRole, decide_eq_true_eq]
      omega
    · obtain ⟨-, hk'⟩ : Index.Ev P L g d f := hev
      unfold Index.EvK at hk'
      rw [hx] at hk'
      exact (exit_not_sync hk' hk).elim
  | idle s n => exact absurd rfl (hid s n)
  | _ => exfalso; omega

/-- **A lane of warp 7's successful polls on `l` are the index warp's ledger's.** -/
theorem ix_okPolls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 7) (k : Nat) (l : Loc) :
    okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (Index.cls (.acq l)) :=
  count_role (fun _ _ hj hk => ix_inRole hp hX hFw hw hj hk) (fun _ => okPoll_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc =>
        cases ok <;> simp [Index.cls, Index.kindOf, sourceWaitSuccess, eq_comm]
      | _ => simp [Index.cls, Index.kindOf, sourceWaitSuccess]) k

/-- **A lane of warp 7's arrivals on `l` are the index warp's ledger's.** -/
theorem ix_arrivals (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g = 7) (k : Nat) (l : Loc) :
    arrivals l ((X.tr g).take k) = ((X.tr g).take k).countP (Index.cls (.arrive l)) :=
  count_role (fun _ _ hj hk => ix_inRole hp hX hFw hw hj hk) (fun _ => arrives_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc => cases ok <;> simp [Index.cls, Index.kindOf, sourceArrive]
      | _ => simp [Index.cls, Index.kindOf, sourceArrive, eq_comm]) k

/-- **No event before a thread's event is undefined behaviour** (it would be the thread's last). -/
theorem ix_take_noUb {k : Nat} {e : Event} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, k) = some e) : ((X.tr g).take k).countP (Index.cls .ub) = 0 :=
  take_noUb_of (fun f h => by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | ub fl => exact ⟨fl, rfl⟩
    | wait l q ok a sc => cases ok <;> simp [Index.cls, Index.kindOf] at h
    | _ => simp [Index.cls, Index.kindOf] at h) hX he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

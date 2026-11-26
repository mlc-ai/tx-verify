-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane

@[expose] public section

/-! # Warpgroup 2's polls and arrivals are its role's

The warpgroup-2 instance of `Common/RoleLane.lean`: a lane of warps 8–11 synchronizes only at pcs
of warpgroup 2's code (`wg2_inRole`), so its prefix counts of successful polls and of arrivals on
an object are warpgroup 2's ledger's (`wg2_okPolls`, `wg2_arrivals`), before which no event is
undefined behaviour (`wg2_take_noUb`). For warpgroup 2's trace-level exports, which import this
file privately. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat} {f : Event}

/-- **A lane of warps 8–11 synchronizes only at pcs of warpgroup 2's code.** -/
theorem wg2_inRole (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) (hf : X.get (g, j) = some f)
    (hk : PollCommit f) : Dequant.inRole f = true := by
  obtain ⟨σ, h, hev, h0, h1, h2, hid⟩ := lane_role hp hX hFw hf hk
  cases h with
  | dequant d n _ _ _ hr =>
    rcases hr with hr | ⟨hx, -⟩
    · simp only [Dequant.inRole, decide_eq_true_eq]
      omega
    · obtain ⟨-, hk'⟩ : Dequant.Ev L g d f := hev
      unfold Dequant.EvK at hk'
      rw [hx] at hk'
      exact (exit_not_sync hk' hk).elim
  | idle s n => exact absurd rfl (hid s n)
  | _ => exfalso; omega

/-- **A lane of warps 8–11's successful polls on `l` are warpgroup 2's ledger's.** -/
theorem wg2_okPolls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) (k : Nat) (l : Loc) :
    okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (Dequant.cls (.acq l)) :=
  count_role (fun _ _ hj hk => wg2_inRole hp hX hFw hw hj hk) (fun _ => okPoll_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc =>
        cases ok <;> simp [Dequant.cls, Dequant.kindOf, sourceWaitSuccess, eq_comm]
      | _ => simp [Dequant.cls, Dequant.kindOf, sourceWaitSuccess]) k

/-- **A lane of warps 8–11's arrivals on `l` are warpgroup 2's ledger's.** -/
theorem wg2_arrivals (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) (k : Nat) (l : Loc) :
    arrivals l ((X.tr g).take k) = ((X.tr g).take k).countP (Dequant.cls (.arrive l)) :=
  count_role (fun _ _ hj hk => wg2_inRole hp hX hFw hw hj hk) (fun _ => arrives_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc => cases ok <;> simp [Dequant.cls, Dequant.kindOf, sourceArrive]
      | _ => simp [Dequant.cls, Dequant.kindOf, sourceArrive, eq_comm]) k

/-- **No event before a thread's event is undefined behaviour** (it would be the thread's last). -/
theorem wg2_take_noUb {k : Nat} {e : Event} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, k) = some e) : ((X.tr g).take k).countP (Dequant.cls .ub) = 0 :=
  take_noUb_of (fun f h => by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | ub fl => exact ⟨fl, rfl⟩
    | wait l q ok a sc => cases ok <;> simp [Dequant.cls, Dequant.kindOf] at h
    | _ => simp [Dequant.cls, Dequant.kindOf] at h) hX he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

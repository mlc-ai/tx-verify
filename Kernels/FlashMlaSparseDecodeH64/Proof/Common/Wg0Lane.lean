-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane

@[expose] public section

/-! # Warpgroup 0's polls and arrivals are its role's

The warpgroup-0 instance of `Common/RoleLane.lean`: a lane of warps 0–3 synchronizes only at pcs
of warpgroup 0's code (`wg0_inRole`), so its prefix counts of successful polls and of arrivals on
an object are warpgroup 0's ledger's (`wg0_okPolls`, `wg0_arrivals`), before which no event is
undefined behaviour (`wg0_take_noUb`). For warpgroup 0's trace-level exports, which import this
file privately. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g j : Nat} {f : Event}

/-- **A lane of warps 0–3 synchronizes only at pcs of warpgroup 0's code.** -/
theorem wg0_inRole (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hf : X.get (g, j) = some f)
    (hk : PollCommit f) : Wg0.inRole f = true := by
  obtain ⟨σ, h, hev, h0, h1, h2, hid⟩ := lane_role hp hX hFw hf hk
  cases h with
  | wg0 d n _ _ _ hr =>
    rcases hr with hr | ⟨hx, -⟩
    · simp only [Wg0.inRole, decide_eq_true_eq]
      omega
    · obtain ⟨-, hk'⟩ : Wg0.Ev P L g (warpW L g) d f := hev
      unfold Wg0.EvK at hk'
      rw [hx] at hk'
      exact (exit_not_sync hk' hk).elim
  | idle s n => exact absurd rfl (hid s n)
  | _ => exfalso; omega

/-- **A lane of warps 0–3's successful polls on `l` are warpgroup 0's ledger's.** -/
theorem wg0_okPolls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (k : Nat) (l : Loc) :
    okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (Wg0.cls (.acq l)) :=
  count_role (fun _ _ hj hk => wg0_inRole hp hX hFw hw hj hk) (fun _ => okPoll_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc =>
        cases ok <;> simp [Wg0.cls, Wg0.kindOf, sourceWaitSuccess, eq_comm]
      | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf, sourceWaitSuccess]
      | _ => simp [Wg0.cls, Wg0.kindOf, sourceWaitSuccess]) k

/-- **A lane of warps 0–3's arrivals on `l` are warpgroup 0's ledger's.** -/
theorem wg0_arrivals (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (k : Nat) (l : Loc) :
    arrivals l ((X.tr g).take k) = ((X.tr g).take k).countP (Wg0.cls (.arrive l)) :=
  count_role (fun _ _ hj hk => wg0_inRole hp hX hFw hw hj hk) (fun _ => arrives_sync)
    (fun f => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | wait l' q ok a sc => cases ok <;> simp [Wg0.cls, Wg0.kindOf, sourceArrive]
      | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf, sourceArrive]
      | _ => simp [Wg0.cls, Wg0.kindOf, sourceArrive, eq_comm]) k

/-- **No event before a thread's event is undefined behaviour** (it would be the thread's last). -/
theorem wg0_take_noUb {k : Nat} {e : Event} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g, k) = some e) : ((X.tr g).take k).countP (Wg0.cls .ub) = 0 :=
  take_noUb_of (fun f h => by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | ub fl => exact ⟨fl, rfl⟩
    | wait l q ok a sc => cases ok <;> simp [Wg0.cls, Wg0.kindOf] at h
    | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf] at h
    | _ => simp [Wg0.cls, Wg0.kindOf] at h) hX he

/-- **A barrier event of a lane of warps 0–3** is the startup's (below pc 103) or at a pc of
warpgroup 0's code. -/
theorem wg0_barRole (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hf : X.get (g, j) = some f)
    (hb : Execution.isBar f = true) : f.pc < 103 ∨ Wg0.inRole f = true := by
  have hub : ∀ fl, f.kind ≠ .ub fl := by
    obtain ⟨pc, kd⟩ := f
    rintro fl hk
    simp only at hk
    subst hk
    simp [Execution.isBar] at hb
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw hf hub
  have h := state_role hJ hi
  rw [← hpc] at h
  have hwo : warp L g = warpOf L g := by
    simp only [warp, warpOf, tidOf_x_eq hp, tidOf_eq hp]
  cases h with
  | startup d n _ _ _ _ hr => exact .inl (by omega)
  | wg0 d n _ _ _ hr =>
    rcases hr with hr | ⟨hx, -⟩
    · simp only [Wg0.inRole, decide_eq_true_eq]
      exact .inr hr
    · obtain ⟨-, hk'⟩ : Wg0.Ev P L g (warpW L g) d f := hev
      unfold Wg0.EvK at hk'
      rw [hx] at hk'
      obtain ⟨pc, kd⟩ := f
      simp only at hk'
      subst hk'
      simp [Execution.isBar] at hb
  | idle s n _ hw' => exact absurd hw (by omega)
  | _ => exfalso; omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

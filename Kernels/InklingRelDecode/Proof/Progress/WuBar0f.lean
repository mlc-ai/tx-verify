-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuBar0e

@[expose] public section

/-!
# `BarTime.lag0f`: the last generation of barrier 0

The last `bar.sync 0` is at `c4`, in the epilogue's `bar3` and the exit role's `bar`. A state that
is not after it (`PostSite`) is timed at most `c4`, and strictly before `c4` unless it is a final
site. A thread that has not made a last-generation arrival is at no post site (`post_seen`: a post
site follows a final site, whose event is the arrival), so it has not exited and is timed at most
`c4`; if its machine stopped at its last event, the state of that event is not a final site (its
event would be the arrival), so it is timed strictly before `c4`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger PTX.Kernels.InklingRelDecode.Proof.BarOrd
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every state before the last `bar.sync 0` is timed at most `c4`**, strictly before it unless
it is a final site. -/
theorem c4_bound {L : Launch} {g : Nat} {Q : Params} {s : TSt}
    (hinv : (threadCode L g Q).inv s) (hto : tTo s = false) (hnp : ¬ PostSite s) :
    time g s ≤ c4 ∧ (¬ FinalSite s → time g s < c4) := by
  cases s with
  | d s0 =>
    cases s0 with
    | epi d =>
      obtain ⟨st, pr, o, sk⟩ := d
      cases st <;>
        simp [time_d, dcompT, epiT, Bound.Epi.siteRank, PostSite, FinalSite] at hnp ⊢ <;> wt_omega
    | dstart d =>
      obtain ⟨-, -, -, h4, -⟩ := dcomp_tbl hinv.2
      simp only [dPh, capB] at h4
      simp only [time_d]
      constructor <;> [skip; intro _] <;> wt_omega
    | pro d =>
      obtain ⟨-, -, -, h4, -⟩ := dcomp_tbl hinv.2
      simp only [dPh] at h4
      split at h4 <;> simp only [capB] at h4 <;> simp only [time_d] <;>
        (constructor <;> [skip; intro _]) <;> wt_omega
    | sm d =>
      obtain ⟨-, -, -, h4, -⟩ := dcomp_tbl hinv.2
      simp only [dPh] at h4
      simp only [time_d]
      split at h4 <;> simp only [capB] at h4 <;> (constructor <;> [skip; intro _]) <;> wt_omega
  | w s0 =>
    cases s0 with
    | worker w =>
      obtain ⟨site, P⟩ := w
      cases site <;>
        simp [time_w, wcompT, workerT, FinalSite, wTo, tTo] at hto ⊢ <;>
        (try split_ifs) <;> wt_omega
    | idle d =>
      obtain ⟨st, P⟩ := d
      cases st <;> simp [time_w, wcompT, idleT, FinalSite] <;> wt_omega
    | loader d P =>
      obtain ⟨-, -, -, h4, -⟩ := wcomp_tbl (t := 0) hinv.2 rfl (by omega) (fun _ => rfl)
        (fun h => by simp [wKind] at h) (fun P h => by rcases h with h | h | h <;> cases h)
      simp only [time_w]
      have : (wPh (.loader d P)).2 ≤ 3 := (w_ph_le _).2
      rcases (by omega : (wPh (.loader d P)).2 = 0 ∨ (wPh (.loader d P)).2 = 1 ∨
        (wPh (.loader d P)).2 = 2 ∨ (wPh (.loader d P)).2 = 3) with h | h | h | h <;>
        simp only [h, capB, mul_zero, add_zero] at h4 <;>
        (constructor <;> [skip; intro _]) <;> wt_omega
    | mma d P =>
      obtain ⟨-, -, -, h4, -⟩ := wcomp_tbl (t := 0) hinv.2 rfl (by omega) (fun _ => rfl)
        (fun h => by simp [wKind] at h) (fun P h => by rcases h with h | h | h <;> cases h)
      simp only [time_w]
      have : (wPh (.mma d P)).2 ≤ 3 := (w_ph_le _).2
      rcases (by omega : (wPh (.mma d P)).2 = 0 ∨ (wPh (.mma d P)).2 = 1 ∨
        (wPh (.mma d P)).2 = 2 ∨ (wPh (.mma d P)).2 = 3) with h | h | h | h <;>
        simp only [h, capB, mul_zero, add_zero] at h4 <;>
        (constructor <;> [skip; intro _]) <;> wt_omega
    | exit x =>
      obtain ⟨st, P⟩ := x
      cases st <;> simp [time_w, wcompT, exitT, PostSite, FinalSite] at hnp ⊢

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu

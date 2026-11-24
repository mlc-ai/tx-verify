-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.TmlFa4Fwd.Proof.Common.Roles
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AllocBefore
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Corr
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Soft
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Softmax and correction lanes exit after two barrier-2 events

A softmax or correction lane's `exit` is fired at its role's exit site (`soft_exit_site`,
`corr_exit_site`), where the role's reference counts two barrier-2 points before it (`bar1` and
`barEnd`: `exit_bar2_soft`, `exit_bar2_corr`), linked to the thread's ledger as in
`soft_tc_bar2`. So such a lane has made two barrier-2 events (`sc_exit_bar2`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem exit_bar2_soft (b l : Bool) (rb rp : Nat) :
    Softmax.passed (Softmax.ptsOf b .bar2) (.exit l) rb rp = 2 := by
  have h2 := (tc_bar2_all b).2
  simp only [Softmax.passed, h2.1, h2.2, Nat.mul_zero, Nat.add_zero]
  cases b <;> cases l <;> decide +kernel

theorem exit_bar2_corr (l : Bool) (r : Nat) :
    Correction.passed (Correction.ptsOf .bar2) (.exit l) r = 2 := by
  simp only [Correction.passed, ctc_bar2_all.2, Nat.mul_zero, Nat.add_zero]
  cases l <;> decide +kernel

set_option maxHeartbeats 8000000 in
theorem soft_exit_site {d : Softmax.D} {pc : Nat} (hev : Softmax.Ev p L g d ⟨pc, .exit⟩) :
    ∃ l, d.site = .exit l := by
  obtain ⟨s, v, kk, acc⟩ := d
  cases s
  case exit l => exact ⟨l, rfl⟩
  all_goals exfalso
  all_goals simp only [Softmax.Ev] at hev
  all_goals first
    | (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore, Softmax.Site.toE];
        done)
    | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 8000000 in
/-- **A softmax or correction lane exits after two barrier-2 events.** -/
theorem sc_exit_bar2 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {j pc : Nat}
    (he : X.get (g, j) = some ⟨pc, .exit⟩) (hw : Prologue.warpIndex L g < 12) :
    2 ≤ (X.tr g).countP (Execution.isBarId 2) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) he (by intro f hf; cases hf)
  have hle : ((X.tr g).take j).countP (Execution.isBarId 2) ≤
      (X.tr g).countP (Execution.isBarId 2) := (List.take_sublist _ _).countP_le
  rcases σ1 with s | ⟨i, d⟩
  · exact (start_noexit hJ hev).elim
  cases i with
  | softmax =>
    obtain ⟨l, hl⟩ := soft_exit_site hev.1
    have h8 := jr_soft hJ
    have hR : SmWarp.Ref p L (Prologue.warpIndex L g) g (SmWarp.sinj p L g d n) := by
      simpa only [JR_eq, h8, ite_true] using hJ
    obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, -⟩ := hR.2 (ub_zero hX he hσ)
    have h1 := hQ.cnt .bar2 rfl
    rw [hl, exit_bar2_soft] at h1
    have hc2 : c Softmax.Cnt.bar2 = 2 := h1
    have hn2 : n (.soft .bar2) = 2 := by rw [← hLk .bar2 rfl]; exact hc2
    have hj : ((X.tr g).take j).countP (Execution.isBarId 2) = 2 := by
      rw [← cls_soft_bar2 (by simpa [Prologue.warpIndex] using h8), count hσ]; exact hn2
    omega
  | correction =>
    obtain ⟨s0, v0, k0⟩ := d
    obtain ⟨l, hl⟩ := corr_exit_site (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,h⟩; cases h))
    have hw' := jr_corr hJ (Prologue.warpIndex_lt hp g)
    have hR := jr_corrRef hJ hw'
    obtain ⟨⟨r, ℓ, hQ⟩, -⟩ := (hR (ub_zero hX he hσ)).1
    have h1 := hQ.cnt .bar2 (by decide)
    change s0 = _ at hl
    simp only [Correction.Control.D.scheduler] at h1
    rw [hl, exit_bar2_corr] at h1
    have hj : ((X.tr g).take j).countP (Execution.isBarId 2) = 2 := by
      rw [← cls_corr_bar2 (L := L) (g := g), count hσ]; exact h1
    omega
  | mma =>
    exfalso
    simp only [JR_eq] at hJ
    unfold RefAll at hJ
    split_ifs at hJ <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref, SmWarp.Ref] <;>
      omega
  | _ =>
    exfalso
    simp only [JR_eq] at hJ
    unfold RefAll at hJ
    split_ifs at hJ <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref, SmWarp.Ref] <;>
      omega

end
end PTX.Kernels.TmlFa4Fwd.Proof

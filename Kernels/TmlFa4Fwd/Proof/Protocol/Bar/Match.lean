-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Soft
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Lemmas.Kernel.Safety.Schedule
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # ERR-BARRIER-MISMATCH

Every barrier event of a lane has the operands `schedB` of its ordinal among the lane's barrier
events: barrier 0 for the startup's (ordinal 0, every warp), the softmax warps' schedule `softB`
(warps 0 to 7), the correction warps' `corrB` (warps 8 to 11), and barrier 2 for all 416 threads
afterwards for the MMA warp (the output and loader warps make no barrier event after the
startup's). The schedule depends on the lane only through its warp index and the CTA's tile, so
two lanes of a warp have one schedule, and `Frame.noBarMismatch_of_schedule` gives the class. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The barrier schedule of lane `g`**: the operands of its `k`-th barrier event. -/
def schedB (p : Params) (L : Launch) (g k : Nat) : Nat × Option Nat × BarMode :=
  if Prologue.warpIndex L g < 8 then softB L g (tileS p L g) k
  else if Prologue.warpIndex L g = 12 ∨ Prologue.warpIndex L g = 13 ∨
      Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15 then
    if k = 0 then (0, none, .sync) else (2, some 416, .sync)
  else corrB L g (tileC p L g) k

theorem schedB_zero : schedB p L g 0 = (0, none, .sync) := by
  simp only [schedB, softB, corrB]
  split_ifs <;> rfl

/-- Two lanes of one warp have one schedule. -/
theorem schedB_warp (hp : Pre p L m) {h : Nat} (hs : SameWarp L g h) :
    schedB p L g = schedB p L h := by
  obtain ⟨⟨hg, hh, hc⟩, hw⟩ := hs
  have hS := tileS_warp (p := p) hc hw
  have hC := tileC_cta hp hg hh hc
  have hW : Prologue.warpIndex L g = Prologue.warpIndex L h := hw
  funext k
  simp only [schedB, softB, corrB, hS, hC, hW, Softmax.stg, Softmax.warpW, Softmax.nbW,
    Correction.nbOf, Correction.nb0W, Correction.nb1W, hw]

/-- The class of the barrier ordinal is `isBar`. -/
theorem cls_bar : cls L g (.mma .bar) = Execution.isBar := by
  funext e
  obtain ⟨pc, kind⟩ := e
  cases kind <;> rfl

/-! ### The roles that make no barrier event -/

set_option maxHeartbeats 4000000 in
theorem ld_nobar {w : Nat} {d : Loader.D} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (hev : Loader.Ev p L g w d ⟨pc, .bar id cnt mode⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first | exact (epi_nobar hev _ _ _ rfl).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try simp_all)

set_option maxHeartbeats 4000000 in
theorem mma_bar {d : Mma.D} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (hev : Mma.Ev p L g d ⟨pc, .bar id cnt mode⟩) : (id, cnt, mode) = (2, some 416, .sync) := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Mma.Ev] at hev
  all_goals first | exact (epi_nobar hev _ _ _ rfl).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  case bar1 | bar2 =>
    simp only [Kind.bar.injEq, Prod.mk.injEq] at hev ⊢
    exact hev
  all_goals contradiction

theorem start_barOps {s : Startup.D} {n : Cls → Nat} (hJ : JR p L g (.inl s, n)) {pc id : Nat}
    {cnt : Option Nat} {mode : BarMode} (hev : Startup.Ev L g s ⟨pc, .bar id cnt mode⟩) :
    (id, cnt, mode) = (0, none, .sync) := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site
  case bar =>
    simp only [Startup.Ev, Kind.bar.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    rfl
  case enter r => exact absurd rfl (jr_start_site hJ r)
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
  all_goals simp only [Startup.Ev] at hev
  all_goals first
    | (cases hev; done)
    | (rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk)
    | (rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk)
    | (rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk)

/-! ### The class -/

set_option maxHeartbeats 4000000 in
/-- **Every barrier event of a lane has its ordinal's operands in the lane's schedule.** -/
theorem bar_sched (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k pc id : Nat}
    {cnt : Option Nat} {mode : BarMode} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    (id, cnt, mode) = schedB p L g (((X.tr g).take k).countP Execution.isBar) := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hg he
    (fun f h => by cases h)
  have hcnt : ((X.tr g).take k).countP Execution.isBar = n (.mma .bar) := by
    rw [← cls_bar (L := L) (g := g)]; exact count hσ _
  have hBT := bar_count hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ
  have h0 := ub_zero hX he hσ
  have hJ' : JR p L g (σ1, n) := hJ
  have hw16 := Prologue.warpIndex_lt hp g
  rw [hcnt]
  rcases σ1 with s | ⟨i, d⟩
  · simp only [BarT] at hBT
    rw [hBT, schedB_zero]
    exact start_barOps hJ' hev
  cases i with
  | epilogue => exact (epi_nobar hev _ _ _ rfl).elim
  | loader b => exact (ld_nobar hev).elim
  | stub r =>
    exfalso
    simp only [JR_eq] at hJ'
    split_ifs at hJ'
    · exact hJ'
    · unfold RefAll at hJ'
      split_ifs at hJ' <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]
  | mma =>
    rcases d with s | ⟨_, d⟩
    · exfalso
      rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
    · have h12 : Prologue.warpIndex L g = 12 := by
        simp only [JR_eq] at hJ'
        split_ifs at hJ' with h8
        · exact hJ'.elim
        · unfold RefAll at hJ'
          split_ifs at hJ' with h12 <;> simp_all [Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]
      simp only [BarT] at hBT
      have hne : n (.mma .bar) ≠ 0 := by omega
      simp only [schedB, h12, hne]
      simpa using mma_bar hev
  | correction =>
    have hw : ¬ Prologue.warpIndex L g < 8 ∧ ¬ (Prologue.warpIndex L g = 12 ∨
        Prologue.warpIndex L g = 13 ∨ Prologue.warpIndex L g = 14 ∨
        Prologue.warpIndex L g = 15) := by
      simp only [JR_eq] at hJ'
      split_ifs at hJ' with h8
      · exact hJ'.elim
      · unfold RefAll at hJ'
        split_ifs at hJ' <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref]
    have hR : CorrWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.correction, d⟩, n) := by
      simp only [JR_eq] at hJ'
      split_ifs at hJ' with h8
      · exact hJ'.elim
      · unfold RefAll at hJ'
        split_ifs at hJ' <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref]
    obtain ⟨hRc, hFc⟩ := hR h0
    have hL := corr_late hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ
    simp only [schedB, hw.1, hw.2, ite_false]
    exact corr_sched hRc hFc (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,h⟩; cases h)) hBT
        (hL h0)
  | softmax =>
    have h8 : Prologue.warpIndex L g < 8 := by
      simp only [JR_eq] at hJ'
      split_ifs at hJ' with h8
      · exact h8
      · unfold RefAll at hJ'
        split_ifs at hJ' <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]
    have hR : SmWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.softmax, d⟩, n) := by
      simpa only [JR_eq, h8, ite_true] using hJ'
    obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hFs⟩ := hR.2 h0
    have hL := soft_late hp hX hFw hg k _ (Frame.noUbBefore_of_get hX he) hσ
    simp only [schedB, h8, ite_true]
    exact soft_sched hQ hLk hFs hev.1 hBT (hL h0)

/-- **ERR-BARRIER-MISMATCH**: the lanes of a warp agree on every barrier event. -/
theorem noBarMismatch (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : ¬ BarMismatch L X :=
  Frame.noBarMismatch_of_schedule (schedB p L)
    (fun _ _ _ _ _ _ hg he => bar_sched hp hX hFw hg he)
    (fun _ _ hs => schedB_warp hp hs)

end
end PTX.Kernels.TmlFa4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Assumptions
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.AccBar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Done
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The warps of the Tensor Memory operations

MMAs and commits are warp 12's, loads and stores those of the softmax and correction warps (0 to
11). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **An MMA is warp 12's.** -/
theorem mma_warp (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue (g, k) d sp acc mask) : Prologue.warpIndex L g = 12 := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨d, n, -, hJ, -⟩ := mma_issue_state hp hX hFw he
  exact jr_mma hJ

/-- A commit's kind. -/
private def IsCommitK : Kind → Prop
  | .tc (.commit _) => True
  | _ => False

private theorem epi_nocommit {d : Epilogue.D} {pc : Nat} {k : Kind} (hk : IsCommitK k)
    (hev : Epilogue.Ev p L g d ⟨pc, k⟩) : False := by
  unfold Epilogue.Ev at hev
  split at hev <;> rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Epilogue.isStore, IsCommitK]

set_option maxHeartbeats 8000000 in
private theorem ld_nocommit {w : Nat} {d : Loader.D} {pc : Nat} {k : Kind} (hk : IsCommitK k)
    (hev : Loader.Ev p L g w d ⟨pc, k⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first | exact (epi_nocommit hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsCommitK]

set_option maxHeartbeats 8000000 in
private theorem soft_nocommit {d : Softmax.D} {pc : Nat} {k : Kind} (hk : IsCommitK k)
    (hev : Softmax.Ev p L g d ⟨pc, k⟩) : False := by
  obtain ⟨s, v, kk, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals first | exact (epi_nocommit hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsCommitK, Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 8000000 in
private theorem corr_nocommit {d : Correction.D} {pc : Nat} {k : Kind} (hk : IsCommitK k)
    (hev : Correction.Ev p L g d ⟨pc, k⟩) : False := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  all_goals first | exact (epi_nocommit hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsCommitK, Correction.rdOrUb]

/-- **The warps of a commit, a load and a store.** -/
private theorem tc_warp (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i pc : Nat} {k : Kind} (he : X.get (g, i) = some ⟨pc, k⟩)
    (hk : IsCommitK k ∨ IsLdSt k) :
    (IsCommitK k → Prologue.warpIndex L g = 12) ∧ (IsLdSt k → Prologue.warpIndex L g < 12) := by
  have hub : ∀ f, k ≠ .ub f := by rintro f rfl; rcases hk with h | h <;> exact h
  have hacc : IsLdSt k → IsAcc k := by
    intro h; revert h; cases k <;> (try cases ‹TcKind›) <;> simp [IsLdSt, IsAcc]
  have hx : IsCommitK k → IsLdSt k → False := by
    cases k <;> (try cases ‹TcKind›) <;> simp [IsLdSt, IsCommitK]
  obtain ⟨⟨σ1, n⟩, -, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) he hub
  rcases σ1 with s | ⟨i, d⟩
  · refine ⟨fun hc => ?_, fun hl => (start_noacc hJ (hacc hl) hev).elim⟩
    exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    cases k <;> (try cases ‹TcKind›) <;> simp only [IsCommitK] at hc
    cases site
    case enter r => exact jr_start_site hJ r rfl
    case sh j => fin_cases j <;> simp [TEv, Startup.Ev] at hev
    all_goals simp [TEv, Startup.Ev] at hev
  cases i with
  | softmax =>
    have := jr_soft hJ
    exact ⟨fun hc => (soft_nocommit hc hev.1).elim, fun _ => by omega⟩
  | correction =>
    have := jr_corr hJ (Prologue.warpIndex_lt hp g)
    refine ⟨fun hc => ?_, fun _ => by omega⟩
    exact (corr_nocommit hc
      (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,rfl⟩; exact hc))).elim
  | epilogue =>
    exact ⟨fun hc => (epi_nocommit hc hev).elim, fun hl => (epi_noacc (hacc hl) hev).elim⟩
  | loader b =>
    exact ⟨fun hc => (ld_nocommit hc hev).elim, fun hl => (ld_noacc (hacc hl) hev).elim⟩
  | stub r => exact (jr_stub hJ).elim
  | mma =>
    refine ⟨fun _ => jr_mma hJ, fun hl => ?_⟩
    exfalso
    rcases d with s | ⟨⟨⟩, d⟩
    · rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;>
        simp only at hk' <;> subst hk' <;> exact hl
    · exact mma_noldst (hev := hev) hl

/-- **A Tensor Memory load or store is a softmax or correction lane's.** -/
theorem ldst_warp (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k a : Nat} {vals : List Value} {sh : TcShape}
    (hi : X.TLd (g, k) a vals sh ∨ X.TSt (g, k) a vals sh) : Prologue.warpIndex L g < 12 := by
  rcases hi with ⟨pc, he⟩ | ⟨pc, he⟩
  · exact (tc_warp hp hX hFw he (.inr trivial)).2 trivial
  · exact (tc_warp hp hX hFw he (.inr trivial)).2 trivial

/-- **A commit is warp 12's.** -/
theorem commit_warp (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k : Nat} {s : TcCommit.Spec} (hi : X.Commit (g, k) s) :
    Prologue.warpIndex L g = 12 := by
  obtain ⟨pc, he⟩ := hi
  exact (tc_warp hp hX hFw he (.inl trivial)).1 trivial

end
end PTX.Kernels.TmlFa4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
import Lemmas.Kernel.Progress.TcColl
import Lemmas.Tmem.Tmem1Ready
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Tensor Memory resources drain

A resource operation that is not performed: if every lane of its warp made the collective, the
allocator performs it (`Tmem.One.entry_ready`); else some lane has not, and it is pending (an exit
short of a collective of its warp is ERR-ALIGNED-MISMATCH), which ranks below the obligation. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An open Tensor Memory obligation steps.** -/
theorem tmem_obl_steps (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X)
    (ho : Descent.Obl L X .tmem) : StepsAt p L m X .tmem := by
  have hX := hmax.1
  have hsafe := hs.2 X hX
  have hto := tmem1Ops hp hX (launchFollow hp hX)
  simp only [Descent.Obl, Tmem.Pair.Drained, not_forall] at ho
  obtain ⟨⟨g, k⟩, pc, grp, dst, act, he, hnc⟩ := ho
  have hg := Frame.lt_of_get hX he
  have hperf : ¬ Tmem.Pair.Performed L X (g, k) := fun h =>
    hnc (Tmem.One.covered_of_performed hX hto h)
  have hlast : k = (X.tr g).length - 1 := by
    have h1 := len_of_get he
    simp only at h1
    by_contra hne
    exact hperf (hX.tmemPairBlocking.performed he (by simp only; omega))
  have hlt0 : 0 < (X.tr g).length := by
    have h1 := len_of_get he
    simp only at h1; omega
  rw [hlast] at he hperf
  clear hlast hnc
  generalize hK : (X.tr g).length - 1 = k' at he hperf
  have hk : X.TcK (g, k') (((X.tr g).take k').countP isTcColl) := ⟨⟨_, he, rfl⟩, rfl⟩
  by_cases hall : ∀ h, h < L.threads → SameWarp L g h →
      ∃ j, X.TcK (h, j) (((X.tr g).take k').countP isTcColl)
  · rw [← hK] at he hperf hk hall
    obtain ⟨c, r, hR⟩ := Tmem.One.entry_ready hX hto
      ⟨hp.cluster.2.2, by rw [hp.cluster.1, Nat.mod_one]⟩
      (fun h => hsafe (by simp [Unsafe, h])) hg he hperf hk hall
    obtain ⟨Y, hY, hle, hsize, -⟩ := Step.entry_counted hX hR
      (wfStepAll.quiet hX Tmem.Pair.le_recordEntry rfl (Execution.noNewRead_of_tr rfl))
    exact .inl ⟨Y, hY, hle, hsize⟩
  · obtain ⟨h, hh, hsw, hnh⟩ : ∃ h, h < L.threads ∧ SameWarp L g h ∧
        ∀ j, ¬ X.TcK (h, j) (((X.tr g).take k').countP isTcColl) := by
      by_contra hcon
      push Not at hcon
      exact hall fun h hh hw => hcon h hh hw
    have hle : (X.tr h).countP isTcColl ≤ ((X.tr g).take k').countP isTcColl := by
      by_contra hlt
      obtain ⟨j, hj⟩ := Sched.tcK_of_lt (Nat.lt_of_not_le hlt)
      exact hnh j hj
    have hnx : ∀ j pc, X.get (h, j) ≠ some ⟨pc, .exit⟩ := by
      intro j pc hj
      have htc : ¬ AlignedMismatch L kernel X := fun h => hsafe (by simp [Unsafe, h])
      exact htc ⟨.tc, .inr ⟨(g, k'), (h, j), _, hsw, he, rfl, rfl, ⟨pc, hj⟩, hle⟩⟩
    have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlt0
    have hph := Sched.pending_of_noExit hX hg hne hh (Sched.cluster_of_sameWarp hsw) hnx
    exact .inr ⟨X, .thread h, hmax, hph, Sched.rank_thread_lt_tmem hph.1⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Top

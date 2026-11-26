-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.Tmem1ReadyG
public import Lemmas.Kernel.Progress.TcColl
public import Lemmas.Quiet.Base
public import Lemmas.Step.TmemPair

@[expose] public section

/-! # The Tensor Memory obligation steps, `cta_group::1`, under quiet extensions

A kernel whose paired Tensor Memory operations are those of one warp in group 1
(`Tmem.One.Tmem1Ops`) and that has no ERR-ALIGNED-MISMATCH steps at an open `.tmem` obligation
(`Sched.tmem_one_stepsQ`): the operation not covered is its lane's last event; if every lane of the
warp has made the collective, the allocator performs it (`Tmem.One.entry_readyG`), a quiet
extension; else a lane of the warp has not, it has not exited (an exit short of a collective of its
warp is a mismatch), so it is pending, which ranks below the obligation. -/

namespace PTX.Sched
open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {sel : Nat → Bool} {w : Nat}

/-- **An open Tensor Memory obligation steps**, for a `cta_group::1` kernel. -/
theorem tmem_one_stepsQ (hA : Assumption.WfQuiet sel L K mem0 A) (hmax : Maximal L K A mem0 X)
    (hto : Tmem.One.Tmem1Ops L X w) (hcg : L.clusterGridValid) (htc : ¬ AlignedMismatch L K X)
    (ho : Descent.Obl L X .tmem) : Steps M mem0 X .tmem := by
  have hX := hmax.1
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
    simp only at h1
    omega
  rw [hlast] at he hperf
  clear hlast hnc
  generalize hK : (X.tr g).length - 1 = k' at he hperf
  have hk : X.TcK (g, k') (((X.tr g).take k').countP isTcColl) := ⟨⟨_, he, rfl⟩, rfl⟩
  by_cases hall : ∀ h, h < L.threads → SameWarp L g h →
      ∃ j, X.TcK (h, j) (((X.tr g).take k').countP isTcColl)
  · rw [← hK] at he hperf hk hall
    obtain ⟨c, r, hR⟩ := Tmem.One.entry_readyG hX hto hcg htc hg he hperf hk hall
    obtain ⟨Y, hY, hle, hsize, -⟩ := Step.entry_counted hX hR
      (hA.quiet hX Tmem.Pair.le_recordEntry rfl (Execution.quietExt_of_tr rfl))
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
    have hnx : ∀ j pc, X.get (h, j) ≠ some ⟨pc, .exit⟩ := fun j pc hj =>
      htc ⟨.tc, .inr ⟨(g, k'), (h, j), _, hsw, he, rfl, rfl, ⟨pc, hj⟩, hle⟩⟩
    have hne : X.tr g ≠ [] := List.ne_nil_of_length_pos hlt0
    have hph := Sched.pending_of_noExit hX hg hne hh (Sched.cluster_of_sameWarp hsw) hnx
    exact .inr ⟨X, .thread h, hmax, hph, Sched.rank_thread_lt_tmem hph.1⟩

end PTX.Sched

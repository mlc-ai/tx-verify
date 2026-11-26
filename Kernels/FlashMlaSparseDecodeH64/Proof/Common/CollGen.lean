-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollEv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollList
public import Lemmas.Kernel.CountClosed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound

@[expose] public section

/-! # The collectives a state has made, from its pc

`ncT x σ`: the number of the lane's warp's collectives before the state's pc (`ncW`). It is the
number of warp collectives in the thread's prefix (`ncT_count`) when every step keeps it
(`ncT_step`: it grows by one exactly at a state at a collective). The role files prove the step
at their states; the facts of a lane that do not depend on its role are here: a state is at a
collective exactly when its pc is one of `collPcs` (`collAt_iff`), a collective event comes from
such a state, and an exit event is at the final `ret` (`exit_nc`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- **The collectives a state has made**: its warp's list entries below its pc. -/
def ncT (P : Params) (L : Launch) (x : Nat) (σ : (thread P L x).D) : Nat :=
  ncW (warpOf L x) ((thread P L x).pc σ)

/-- A state is at a warp collective exactly when its pc is one of `collPcs`. -/
theorem collAt_iff {σ : (thread P L x).D} :
    CollAt P L x σ ↔ (thread P L x).pc σ ∈ collPcs :=
  ⟨fun ⟨_, h, hc⟩ => collIns_pc h hc, fun h => collPcs_ins h⟩

theorem ncW_six (w : Nat) : ncW w 6 = 0 := by
  unfold ncW collList
  repeat' split
  all_goals decide

/-- No collective before the first state. -/
theorem ncT_init : ncT P L x (thread P L x).init = 0 := ncW_six _

/-- **The prefix count of warp collectives is `ncT`**, when every step on an event that is no
undefined behaviour keeps it. -/
theorem ncT_count (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X)
    (hstep : ∀ {k σ e σ'}, X.get (x, k) = some e →
      Frame.stateAt (thread P L) X x k = some (some σ) →
      (thread P L x).next σ e = some (some σ') →
      ncT P L x σ' = ncT P L x σ + if (thread P L x).pc σ ∈ collPcs then 1 else 0) :
    ∀ k σ, Frame.stateAt (thread P L) X x k = some (some σ) →
      ((X.tr x).take k).countP Sched.isWarpColl = ncT P L x σ := by
  refine Frame.count_closed (C := thread P L) Sched.isWarpColl (ncT P L x) ncT_init ?_
  intro k e σ σ' he hσ _ hn
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(x, k), e.pc, f, by
    rw [show X.get (x, k) = some e from he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hne
  have hc := coll_iff_pc hX (show X.get (x, k) = some e from he) hne
  rw [hstep he hσ hn]
  by_cases hcA : (thread P L x).pc σ ∈ collPcs
  · have : Sched.isWarpColl e = true := hc.mpr (hpc ▸ hcA)
    simp [hcA, this]
  · have : Sched.isWarpColl e ≠ true := fun h => hcA (hpc ▸ hc.mp h)
    simp [hcA, this]

/-- A collective event is fired from a state at a collective. -/
theorem coll_isP (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {σ : (thread P L x).D} {e : Event}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) (he : X.get (x, k) = some e)
    (hc : Sched.isWarpColl e = true) : CollAt P L x σ := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => by
    obtain ⟨pc, kd⟩ := e; simp only at hf; subst hf; simp [Sched.isWarpColl] at hc
  have hpc := Frame.event_pcU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hne
  exact collAt_iff.mpr (hpc ▸ coll_event_pc hX he hc)

theorem collList_lt (w : Nat) : ∀ c ∈ collList w, c < 2557 := by
  intro c hc
  unfold collList at hc
  repeat' split at hc
  all_goals (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; omega)

/-- Past the last collective every list entry is counted. -/
theorem ncW_big {w pc : Nat} (h : 2557 ≤ pc) : ncW w pc = (collList w).length := by
  unfold ncW
  rw [List.filter_eq_self.mpr]
  intro c hc
  have := collList_lt w c hc
  simp only [decide_eq_true_eq]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

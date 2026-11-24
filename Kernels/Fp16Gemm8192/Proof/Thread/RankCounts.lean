-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RankDefs
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # The rank counts of the input ring: the MMA commits to the empty barriers

The MMA thread commits to slot `s`'s empty barriers at each block of its trips. The commits
advance one block at a time, in round robin over the four slots, so along a thread's run the
per-slot counts are the round-robin shares of the total (`mma_counts`). The thread's site fixes
that total modulo the 128 blocks of a task. The loader's polls are in `LoaderTasks`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- The loader's successful polls on the four input empty barriers, summed by slot. -/
def lcount (L : Launch) (g : Nat) (es : List Event) : Nat :=
  ∑ s : Fin 4, okPolls (Loader.emptyOf L g s) es

theorem inputEmpty_eq (L : Launch) (g : Nat) (s : Fin 4) :
    inputEmpty L (g / L.block) s.val = Loader.emptyOf L g s :=
  (InputRing.emptyLoc_bar L _ s).symm

theorem loaderCount_eq (L : Launch) (g : Nat) (es : List Event) :
    loaderCount L g es = lcount L g es := by
  unfold loaderCount lcount
  exact Finset.sum_congr rfl fun s _ => congrArg (fun m => okPolls m es) (inputEmpty_eq L g s)

theorem lcount_snoc {L : Launch} {g : Nat} {pre : List Event} {e : Event} {r : Fin 4}
    (h : ∀ s : Fin 4, okPolls (Loader.emptyOf L g s) (pre ++ [e]) =
      okPolls (Loader.emptyOf L g s) pre + if r = s then 1 else 0) :
    lcount L g (pre ++ [e]) = lcount L g pre + 1 := by
  unfold lcount
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- A successful poll of slot `r`'s empty barrier adds one to the count of slot `r`. -/
theorem okPolls_snoc_ok {L : Launch} {g : Nat} {pre : List Event} {e : Event} {pc p : Nat}
    {acq : Bool} {sc : MbarScope} {r : Fin 4}
    (he : e = ⟨pc, .wait (Loader.emptyOf L g r) p true acq sc⟩) (s : Fin 4) :
    okPolls (Loader.emptyOf L g s) (pre ++ [e]) =
      okPolls (Loader.emptyOf L g s) pre + if r = s then 1 else 0 := by
  rw [okPolls_snoc, Loader.okPoll_wait_empty he]
  by_cases h : r = s <;> simp [h]

/-- The loader's site against its successful empty polls `N` (so far): the block it is at, and
at the end of a task, the count's position in the task. -/
def LoaderCond (l : Loader.D) (N : Nat) : Prop :=
  match l.site with
  | .wait b => N % 128 = l.q + b.val
  | .load b _ | .arrive b => 0 < N ∧ (N - 1) % 128 = l.q + b.val
  | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 128 ≤ N ∧ N % 128 = 0
  | .drain i => 128 ≤ N ∧ N % 128 = i.val
  | _ => True

set_option maxHeartbeats 8000000 in
/-- Round robin: after `K` commits of the MMA thread in all, slot `s` has had those with index
≡ `s` mod 4, and the thread's site fixes `K` modulo the task's 128 blocks (`Mma.Counts`). -/
theorem mma_counts {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es)
    {k : Nat} {m : Mma.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) (es.take k) =
      some (some (.inr (.mma m)))) :
    (∀ s : Fin 4, (es.take k).countP (commitsTo (inputEmpty L (g / L.block) s)) =
      (mmaCount L g (es.take k) + 3 - s) / 4) ∧
    (match m.site with
     | .full s | .mma s _ | .commit s => mmaCount L g (es.take k) % 128 = m.q + s.val ∧ m.q % 4 = 0
     | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack | .accWait =>
         mmaCount L g (es.take k) % 128 = 0
     | .accCommit => 128 ≤ mmaCount L g (es.take k) ∧ mmaCount L g (es.take k) % 128 = 0
     | _ => True) := by
  have hC : Mma.Counts L g m (es.take k) := threadCounts_run hpre hg htr k _ hσ
  simp only [mmaCount_eq]
  refine ⟨fun s => ?_, ?_⟩
  · rw [inputEmpty_emptyAt]
    exact hC.rank s
  · obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
    cases site <;> first | exact ⟨hC.cond, hC.q4⟩ | exact hC.cond | trivial

end
end PTX.Kernels.Fp16Gemm8192.Proof

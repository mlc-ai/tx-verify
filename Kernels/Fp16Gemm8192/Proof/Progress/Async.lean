-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Descent
public import Lemmas.Step.Drain
public import Lemmas.Step.MmaDrain
public import Lemmas.Step.TensorDrain
public import Lemmas.Flow.NotTcCp
public import Lemmas.Flow.NotTcShift
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotAsyncWait

@[expose] public section

/-! # Asynchronous obligations of a maximal execution

The kernel's assumptions constrain no execution (`prod_wfFree`), so every asynchronous stage
the model allows to complete has completed in a maximal execution (`Lemmas/Step/Drain`). A
maximal execution has no open CLC obligation (`clc_steps`), and no open MMA obligation when the
MMAs' operands have sources (`mma_steps`, `OperandSources`, which the input ring proves), and no
open tensor-load obligation when the loads' global sources are fixed (`tensor_steps`,
`TensorSources`). The kernel's code has no `tcgen05.cp`, `tcgen05.shift` and
`cp.async.mbarrier.arrive` (decided on the code), so no Tensor Core copy or shift and no arrive-on
is ever open (`no_cp`, `no_shift`, `arriveOn_steps`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A maximal execution has notified every target of every cancellation request. -/
theorem clc_steps (hmax : Maximal L kernel Prod mem0 X) (ho : Descent.Obl L X .clc) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X .clc :=
  (ho fun _ _ _ hi => Maximal.clc_notified prod_wfFree hmax hi).elim

/-- The kernel has no `tcgen05.cp` instruction. -/
theorem kernel_no_tcCp' : kernel.code.all (fun ins => !Flow.tcCpOp ins.op) = true := by
  decide +kernel

/-- The kernel has no `tcgen05.shift` instruction. -/
theorem kernel_no_tcShift : kernel.code.all (fun ins => !Flow.tcShiftOp ins.op) = true := by
  decide +kernel

/-- The kernel has no `cp.async.mbarrier.arrive` instruction. -/
theorem kernel_no_asyncArrive :
    kernel.code.all (fun ins => !Flow.asyncArriveOp ins.op) = true := by
  decide +kernel

/-- The kernel has no `cp.async` group wait instruction. -/
theorem kernel_no_asyncWait :
    kernel.code.all (fun ins => !Flow.asyncWaitOp ins.op) = true := by
  decide +kernel

/-- No event of a consistent execution is a `cp.async` group wait. -/
theorem no_asyncWait (hX : Consistent L kernel Prod mem0 X) {i : EvId} {pc n : Nat} :
    X.get i ≠ some ⟨pc, .asyncWait n⟩ :=
  fun he => Flow.no_kind_of_code hX Flow.asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => Flow.fires_asyncWait_op hf hk)
    kernel_no_asyncWait he ⟨n, rfl⟩

/-- No event of a consistent execution is a Tensor Core copy. -/
theorem no_cp (hX : Consistent L kernel Prod mem0 X) : ∀ e c, ¬ X.CpIssue e c :=
  fun _ c ⟨_, he⟩ => Flow.no_kind_of_code hX Flow.tcCpOp (fun k => ∃ c, k = .tc (.cp c))
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => Flow.fires_tcCp_op hf hk) kernel_no_tcCp' he
    ⟨c, rfl⟩

/-- No event of a consistent execution is a Tensor Core shift. -/
theorem no_shift (hX : Consistent L kernel Prod mem0 X) : ∀ e s, ¬ X.ShiftIssue e s :=
  fun _ s ⟨_, he⟩ => Flow.no_kind_of_code hX Flow.tcShiftOp (fun k => ∃ s, k = .tc (.shift s))
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => Flow.fires_tcShift_op hf hk)
    kernel_no_tcShift he ⟨s, rfl⟩

/-- No event of a consistent execution is a `cp.async.mbarrier.arrive`. -/
theorem no_asyncArrive (hX : Consistent L kernel Prod mem0 X) :
    ∀ e m noinc, ¬ X.AsyncArrive e m noinc :=
  fun _ m noinc ⟨_, he⟩ => Flow.no_kind_of_code hX Flow.asyncArriveOp
    (fun k => ∃ m noinc, k = .asyncArrive m noinc) (fun _ ⟨_, _, h⟩ => by cases h)
    (fun hf ⟨_, _, hk⟩ => Flow.fires_asyncArrive_op hf hk) kernel_no_asyncArrive he
    ⟨m, noinc, rfl⟩

/-- A maximal execution whose MMAs' operands have sources has completed every MMA; the kernel
issues no other Tensor Core operation that a commit tracks. -/
theorem mma_steps (hmax : Maximal L kernel Prod mem0 X) (hsg : SyncGuarded L kernel X)
    (hos : OperandSources L X 8192 8192)
      (ho : Descent.Obl L X .mma) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X .mma := by
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hi⟩ | ⟨c, hc⟩ | ⟨sh, hsh⟩
  · exact Maximal.mma_all_done prod_wfFree hmax hsg hos hi
  · exact (no_cp hmax.1 i c hc).elim
  · exact (no_shift hmax.1 i sh hsh).elim

/-- The kernel issues no `cp.async.mbarrier.arrive`, so no arrive-on obligation is open. -/
theorem arriveOn_steps (hmax : Maximal L kernel Prod mem0 X) (ho : Descent.Obl L X .arriveOn) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X .arriveOn :=
  (ho fun i m noinc ha => (no_asyncArrive hmax.1 i m noinc ha).elim).elim

/-- A maximal execution whose tensor loads' sources are fixed has completed every tensor load. -/
theorem tensor_steps (hmax : Maximal L kernel Prod mem0 X) (hts : TensorSources L mem0 X)
    (ho : Descent.Obl L X .tensor) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X .tensor :=
  (ho fun _ _ _ hi => Maximal.tensor_all_notified prod_wfFree hmax hts hi).elim

/-- The kernel issues no linear copy, so a safe maximal execution has no open copy obligation. -/
theorem bulk_steps (hmax : Maximal L kernel Prod mem0 X) (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (ho : Descent.Obl L X .bulk) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X .bulk := by
  refine (ho fun i s hb => ?_).elim
  obtain ⟨pc, he⟩ := hb
  have hg : i.1 < L.threads := Frame.lt_of_get hmax.1 he
  obtain ⟨d, hσ⟩ := Frame.state_of_noUb ht.sound hmax.1 ht.tracked hub he
  exact ((ht.ring_event hg he hσ).copy s rfl).elim

/-- A commit's delivery steps: when every MMA it tracks has started the delivery happened in a
maximal execution, otherwise a tracked MMA is an open MMA obligation of smaller rank. The
kernel issues no Tensor Core copy or shift. -/
theorem commit_steps (hmax : Maximal L kernel Prod mem0 X) (ho : Descent.Obl L X .commit) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X .commit := by
  classical
  by_cases hs : ∀ i, (∃ c, AsyncCopy.TracksMma X i c) → X.async.mmaStarted i = true
  · refine (ho fun i s rank m hi ht => ?_).elim
    exact Maximal.commit_notified_of_started prod_wfFree hmax hi ht fun x hx => hs x ⟨i, hx⟩
  · push Not at hs
    obtain ⟨x, ⟨c, hx⟩, hns⟩ := hs
    obtain ⟨-, -, hta, -⟩ := hx
    refine .inr ⟨X, .mma, hmax, fun hall => ?_, by simp [rank]⟩
    have hd := hall x hta
    have := hmax.1.tma.2.1.2 x hd
    rw [this] at hns
    exact hns rfl

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress

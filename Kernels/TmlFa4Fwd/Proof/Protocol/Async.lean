-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
public import Lemmas.Kernel.Progress.AsyncCp
public import Lemmas.Step.MmaVisible
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Target
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Info
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mbar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The asynchronous obligations from their sources

A maximal execution of the kernel steps at every open asynchronous obligation (`async_steps`), from
the sources of its asynchronous operations (`AsyncSources`): the global bytes of the TMA and
`cp.async` copies are initial and unwritten, and the MMAs' operands and the tensor stores' bytes
have ordered sources. The drain of the Tensor Memory resources is a premise. The rest is the
kernel's: no `clc`, `tcgen05.cp` or `tcgen05.shift` is issued, every arrive-on is of the
no-increment form, and a commit targets the barrier it names. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.Frame (MbarOf)

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The sources of the kernel's asynchronous operations.** -/
structure AsyncSources (L : Launch) (m : Mem0) (X : Execution) : Prop where
  /-- The TMA copies' global bytes. -/
  tensor : TensorSources L m X
  /-- The `cp.async` copies' global bytes. -/
  cp : Sched.CpSources m X
  /-- The MMAs' shared operand bytes. -/
  mma : OperandVisible L X
  /-- No MMA reads a Tensor Memory A cell its accumulator's MMAs write. -/
  apart : TcMma.ATmemApart X
  /-- The MMAs' output layouts are injective. -/
  layout : TcMma.LayoutInjective X
  /-- The tensor stores' bytes. -/
  store : Sched.StoreSources L X

/-- Every arrive-on is of the no-increment form. -/
theorem arrive_noinc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (i : EvId) (l : Loc) : ¬ X.AsyncArrive i l false := by
  rintro ⟨pc, he⟩
  obtain ⟨h, k⟩ := i
  have hm : MbarOf ⟨pc, .asyncArrive l false⟩ l := rfl
  have hni : ∀ c, (⟨pc, .asyncArrive l false⟩ : Event).kind ≠ .mbInit l c := fun _ h => by cases h
  have h16 := Prologue.warpIndex_lt hp h
  rcases show Prologue.warpIndex L h < 8 ∨
      (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) ∨ Prologue.warpIndex L h = 12 ∨
      Prologue.warpIndex L h = 13 ∨
      (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) by omega with
    hw | hw | hw | hw | hw
  · rcases soft_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk
  · rcases corr_mbar_use hp hX hFw hw.1 hw.2 he hm hni with ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;>
      cases hk
  · rcases mma_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk, _⟩ <;>
      cases hk
  · rcases epi_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, hk, _⟩ | ⟨_, _, hk, _⟩ <;> cases hk
  · rcases ld_mbar_use hp hX hFw hw he hm hni with ⟨_, _, _, _, _, hk⟩ | ⟨_, _, _, hk⟩ |
      ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, _, hk, _⟩ <;> cases hk

/-- **An open asynchronous obligation of a maximal execution steps**, from the operations'
sources. -/
theorem async_steps (hp : Pre p L m) (hmax : Maximal L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hsg : SyncGuarded L kernel X) (hS : AsyncSources L m X)
    {M : Sched.Timed kernel Assumptions.all L}
    (htm : Descent.Obl L X .tmem → Sched.Steps M m X .tmem) (o : Descent.Obligation)
    (hth : ∀ g, o ≠ .thread g) (ho : Descent.Obl L X o) : Sched.Steps M m X o := by
  have hX := hmax.1
  have hcp : ∀ e c, ¬ X.CpIssue e c := noCp_of_consistent kernel_noTcCp hX
  have hsh : ∀ e s, ¬ X.ShiftIssue e s := fun e s => no_shift hX
  cases o with
  | thread g => exact absurd rfl (hth g)
  | bulk => exact Sched.bulk_steps_cp Assumptions.wfStep hmax hS.cp ho
  | arriveOn =>
    exact Sched.arriveOn_steps_cp Assumptions.wfStep hmax hS.cp (arrive_noinc hp hX hFw) ho
  | mma =>
    refine (ho fun i hi => ?_).elim
    rcases hi with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
    · exact Maximal.mma_all_done_visible Assumptions.wfStep hmax hsg hS.mma hS.apart hS.layout hm
    · exact (hcp i c hc).elim
    · exact (hsh i s hs).elim
  | clc => exact (ho fun i s tg ⟨pc, he⟩ => (no_clc hp hX hFw i.1 i.2 pc s tg he).elim).elim
  | tensor => exact Sched.tensor_steps Assumptions.wfStep hmax hS.tensor ho
  | store => exact Sched.store_steps Assumptions.wfStep hmax hsg hS.store ho
  | commit =>
    refine Sched.commit_steps Assumptions.wfStep hmax (fun x i ht => ?_)
      (fun g j j' pc pc' sp sp' rank l he _ he' _ ht => ?_) ho
    · refine hX.tma.2.1.2 x ?_
      rcases ht.2.2.1 with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
      · exact Maximal.mma_all_done_visible Assumptions.wfStep hmax hsg hS.mma hS.apart hS.layout hm
      · exact (hcp x c hc).elim
      · exact (hsh x s hs).elim
    · obtain rfl := commit_rank_zero hp hX (i := (g, j')) he' ht
      obtain ⟨r, hr⟩ := commit_self hp hX he
      obtain rfl := commit_rank_zero hp hX (i := (g, j)) he hr
      exact ⟨_, hr⟩
  | tmem => exact htm ho

end PTX.Kernels.TmlFa4Fwd.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.NextEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Lemmas.Quiet.Progress.Drained

@[expose] public section

/-! # The quiet rows: a released lane at an ordinary instruction steps

In a maximal execution of a safe launch every lane has drained its selected tensor stores
(`Prog.drained`: `Maximal.drainedQ` with the stores' visible sources, `Prog.storeSources`), and
the execution facts of a released step hold (`Prog.nextEnv`). So a released pending lane whose
next event is at an instruction outside `Descent.NextKind.Rest` steps (`Prog.ordinary`,
`ordinary_steps`): every exit, fence, barrier, initialization, arrival, read, store, copy, MMA,
commit and Tensor Memory load of every role. The final `ret`'s row follows (`Prog.tail`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **Every lane has drained its selected tensor stores** in a maximal execution of a safe
launch. -/
theorem Prog.drained (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) (g : Nat) : TensorStore.Drained drainSel X g :=
  Maximal.drainedQ wfQuiet_all hmax (Prog.guarded hs hmax.1)
    (Prog.storeSources hpub hmax.1 (follow_of hp X hmax.1) (Sched.safe_noUb (hs.2 X hmax.1)))
    drainSel g

/-- **A released pending lane whose next event is at an instruction outside `Rest` steps.** -/
theorem Prog.ordinary (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) {g : Nat} {e : Event}
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins → (Descent.opKind ins.op).Rest = false) :
    Sched.Steps (timed P L) m X (.thread g) :=
  ordinary_steps hp (Prog.nextEnv hp hs hmax) (follow_of hp X hmax.1) hpd hrel hn hub hk
    fun _ _ _ => Prog.drained hp hpub hs hmax g

private theorem code3611_exit :
    ∀ ins, kernel.code[3611]? = some ins → (Descent.opKind ins.op).Rest = false := by
  intro ins h
  have : kernel.code[3611]?.map (fun i => (Descent.opKind i.op).Rest) = some false := by
    decide +kernel
  rw [h] at this
  simpa using this

/-- **The final `ret`'s quiet row.** -/
theorem Prog.tail (hp : Pre P L m) (hpub : Prog.StorePub P L m) (X : Execution) :
    NextRow.Quiet P L m X fun _ pc => pc = 3611 :=
  fun hs hmax _ _ hpd hrel hn hub h _ =>
    Prog.ordinary hp hpub hs hmax hpd hrel hn hub (h ▸ code3611_exit)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

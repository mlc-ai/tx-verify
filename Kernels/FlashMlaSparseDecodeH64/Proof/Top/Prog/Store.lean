-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Guard
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Classes
public import Lemmas.Quiet.Progress.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WriteBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out

@[expose] public section

/-! # Progress class: the tensor stores' drain

An issued output store that is not fully done steps (`Sched.store_stepsQ`) when the stores'
sources are fixed (`Sched.StoreSources`, `Prog.storeSources`): every tensor store of the program
is a valid tile write without a reduction (`tensorStoreForm`), each byte it reads has a covering
write ordered before the read (the stores' publication, `Prog.storePub`, from warpgroup 0's
output facts, `Prog.outRows`), and every such
write has a byte there (`wbyte_of_write`). Synchronization is guarded by safety (`Prog.guarded`)
and the assumptions' constraints survive the quiet extension (`wfQuiet_all`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The tensor stores' sources are fixed** in a consistent followed execution. -/
theorem Prog.storeSources (hpub : Prog.StorePub P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    Sched.StoreSources L X := by
  intro i a s hi
  obtain ⟨hv, -, hred⟩ := tensorStoreForm hX hi
  exact ⟨hv, hred, fun slot loc hd =>
    ⟨hpub X hX hFw hnu i a s hi slot loc hd, fun _ _ _ hw hc _ => wbyte_of_write hX hw hc⟩⟩

/-- **Warpgroup 0's output trace facts** (`OutRows`): its exports `wg0_outIssue`,
`wg0_outStage`, `wg0_outExit`. -/
theorem Prog.outRows (hp : Pre P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    OutRows P L X where
  issue hi := wg0_outIssue hp hX hFw hnu hi
  stage hy hw hc he hcnt := wg0_outStage hp hX hFw hnu hy hw hc he hcnt
  exit hw he := by
    have := wg0_outExit hp hX hFw hw he
    simp only [outOrd]
    omega

/-- **The output stores' publication** (`out_pub`), from the barrier rows and warpgroup 0's
output facts. -/
theorem Prog.storePub (hp : Pre P L m)
    (hB : ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X → BarRows P L X) :
    Prog.StorePub P L m :=
  fun X hX hFw hnu _ _ _ hi slot _ _ =>
    out_pub hp hX (hB X hX hFw) (Prog.outRows hp hX hFw hnu) hi slot

/-- **An open store obligation steps.** -/
theorem Prog.store (hpub : Prog.StorePub P L m) : Prog.AsyncSteps P L m [.store] := by
  intro hs X hmax hFw o ho hob
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho
  exact Sched.store_stepsQ wfQuiet_all hmax (Prog.guarded hs hmax.1)
    (Prog.storeSources hpub hmax.1 hFw (Sched.safe_noUb (hs.2 X hmax.1))) hob

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

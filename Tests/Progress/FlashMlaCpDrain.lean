-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.Step.CpDrain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part030

@[expose] public section

/-! # `Maximal.cp_doneQ` at FlashMLA's copies

FlashMLA's MMA lane issues 16 `tcgen05.cp.cta_group::1.128x256b` copies, at pcs 1936 to 1980
(`cp_sites`), each of `4096` source bytes on one CTA (`cp_bytes`). The kernel's assumptions satisfy
`WfQuiet` (`Proof.wfQuiet_all`), so a maximal execution whose pending copies have sources
(`CpSourcesT`, what the kernel's Q tiles give) has completed every copy (`cp_done`), and its MMA
obligation steps (`mma_steps`). -/

namespace PTX.Tests.FlashMlaCpDrain
open PTX PTX.Kernels.FlashMlaSparseDecodeH64

/-- The copy sites of FlashMLA. -/
def cpPcs : List Nat :=
  [1936, 1939, 1942, 1945, 1948, 1951, 1954, 1957, 1959, 1962, 1965, 1968, 1971, 1974, 1977, 1980]

/-- **Every copy site holds a `cta_group::1.128x256b` copy without decompression.** -/
theorem cp_sites : ∀ pc ∈ cpPcs, ∃ ta sd,
    kernel.code[pc]? = some { guard := none, op := .tcCp .one .s128x256b ta sd none } := by
  intro pc hpc
  simp only [cpPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact ⟨_, _, Flow.code_1936⟩
  · exact ⟨_, _, Flow.code_1939⟩
  · exact ⟨_, _, Flow.code_1942⟩
  · exact ⟨_, _, Flow.code_1945⟩
  · exact ⟨_, _, Flow.code_1948⟩
  · exact ⟨_, _, Flow.code_1951⟩
  · exact ⟨_, _, Flow.code_1954⟩
  · exact ⟨_, _, Flow.code_1957⟩
  · exact ⟨_, _, Flow.code_1959⟩
  · exact ⟨_, _, Flow.code_1962⟩
  · exact ⟨_, _, Flow.code_1965⟩
  · exact ⟨_, _, Flow.code_1968⟩
  · exact ⟨_, _, Flow.code_1971⟩
  · exact ⟨_, _, Flow.code_1974⟩
  · exact ⟨_, _, Flow.code_1977⟩
  · exact ⟨_, _, Flow.code_1980⟩

/-- A one-CTA `128x256b` copy reads `4096` source bytes: the size of `CpSourcesT`'s byte index. -/
theorem cp_bytes {c : TcCopy.Spec} (hs : c.shape = .s128x256b) (hc : c.ctas.length = 1) :
    c.ctas.length * c.shape.sourceBytes = 4096 := by
  rw [hc, hs]
  decide

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A maximal execution of FlashMLA has completed every copy** whose pending bytes have
sources. -/
theorem cp_done (hmax : Maximal L kernel Assumptions.all mem0 X) (hsg : SyncGuarded L kernel X)
    (hcs : CpSourcesT L Assumptions.all X) {i : EvId} {c : TcCopy.Spec} (hi : X.CpIssue i c) :
    X.async.mmaDone i = true :=
  Maximal.cp_doneQ Proof.wfQuiet_all hmax hsg hcs hi

/-- **FlashMLA's MMA obligation steps**, given its operand and copy sources (FlashMLA issues no
`tcgen05.shift`). -/
theorem mma_steps {M : Sched.Timed kernel Assumptions.all L}
    (hmax : Maximal L kernel Assumptions.all mem0 X) (hsg : SyncGuarded L kernel X)
    (hos : OperandSourcesT L X) (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    (hcs : CpSourcesT L Assumptions.all X) (hsh : ∀ e s, ¬ X.ShiftIssue e s)
    (ho : Descent.Obl L X .mma) : Sched.Steps M mem0 X .mma :=
  Sched.mma_steps_cpQ Proof.wfQuiet_all hmax hsg hos hap hinj hcs hsh ho

end PTX.Tests.FlashMlaCpDrain

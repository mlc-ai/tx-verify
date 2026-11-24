-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Progress.Plain

@[expose] public section

/-!
# Progress test: `griddepcontrol.wait` under EXT-GRIDDEP-SINGLE (checklist rows F1, F2)

Under EXT-GRIDDEP-SINGLE no prerequisite grid is in flight, so `griddepcontrol.wait` has nothing
to wait for: THREAD-MISC makes it a local step to the next instruction. There is no deadlocking
program with this instruction; the test proves the opposite statement for the smallest program,
`griddepcontrol.wait; exit` in one thread: the execution in which the thread exits is possible
and complete. If the instruction became blocking without a witness, the build breaks here.
-/

namespace PTX.Tests.Progress
open PTX

noncomputable section

namespace GridDep

def L1 : Launch := { grid := 1, block := 1, params := fun _ => none }

def gridDepK : Kernel :=
  { name := "griddep", params := [], code := [{ op := .misc (.gridDep true) }, { op := .exit }] }

def tr : Nat → List Event
  | 0 => [⟨1, .exit⟩]
  | _ => []

def X : Execution := plain tr (fun _ _ => none) (fun _ => (.bits 8 0, 0))

theorem kinds : PlainKinds X := by
  rintro ⟨g, n⟩ pc k h
  rcases g with _ | g <;> rcases n with _ | n <;> simp [Execution.get, X, plain, tr] at h
  exact .inr (.inr h.2.symm)

/-- F1: `griddepcontrol.wait; exit` has a complete possible execution: the wait returns at once. -/
theorem gridDep_wait_returns (mem0 : Mem0) :
    Consistent L1 gridDepK [] mem0 X ∧ Complete L1 X := by
  have hthr : ∀ g < L1.threads, Produces gridDepK [] L1 g (tr g) := by
    intro g hg
    rcases g with _ | g
    · exact ⟨none, run_tau rfl (.last .refl ⟨.exit, rfl, rfl, rfl⟩)⟩
    · exact absurd hg (by simp [L1, Launch.threads])
  refine ⟨consistent_plain kinds (by decide) hthr ?_ ?_ ?_ ?_, complete_plain kinds ?_⟩
  · intro g hg
    rcases g with _ | g
    · exact absurd hg (by simp [L1, Launch.threads])
    · rfl
  · intro e a bs hr
    obtain ⟨⟨g, n⟩, rfl, ⟨pc, h⟩ | ⟨new, pc, h⟩⟩ :=
      Execution.NoTma.memReads_thread plain_emptyAsync hr <;>
    rcases g with _ | g <;> rcases n with _ | n <;> simp [Execution.get, plain, tr] at h
  · exact noFuture_plain kinds (by simp)
  · refine hidden_plain kinds ?_
    rintro ⟨g, n⟩ ⟨g', n'⟩ a bs a' bs' ⟨pc, hr⟩
    rcases g with _ | g <;> rcases n with _ | n <;> simp [Execution.get, plain, tr] at hr
  · intro g hg
    rcases g with _ | g
    · exact ⟨1, rfl⟩
    · exact absurd hg (by simp [L1, Launch.threads])

end GridDep

end

end PTX.Tests.Progress

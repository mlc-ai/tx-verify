-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The next event at the softmax closing barrier and at a kernel return -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingProgress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The abstract states immediately before the kernel's return instruction. -/
def ReturnSite : Machine.ThreadD → Prop
  | .mma d => d.site = .exit
  | .tma d => d.site = .exit
  | .idle s => s = .exit
  | .done => True
  | _ => False

theorem return_code {d : Machine.ThreadD} (hsite : ReturnSite d) :
    kernel.code[(Machine.code P L g).pc d]? = some ⟨none, .ret⟩ := by
  cases d <;> try exact hsite.elim
  case mma q =>
    change q.site = .exit at hsite
    change kernel.code[q.site.pc]? = _
    rw [hsite]
    exact Flow.code_exit_0
  case tma q =>
    change q.site = .exit at hsite
    change kernel.code[q.site.pc]? = _
    rw [hsite]
    exact Flow.code_exit_0
  case idle s =>
    change s = .exit at hsite
    subst s
    exact Flow.code_exit_0
  case done => exact Flow.code_exit_0

/-- A pending lane at a return site can issue its exit. -/
theorem return_event {d : Machine.ThreadD}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hsite : ReturnSite d) :
    ∃ t t1, Run kernel Assumptions.all L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1 ∧
      EStep kernel Assumptions.all L g t1 ⟨t1.pc, .exit⟩ none := by
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, ins, hLocal, _, _, hCode, hOut⟩ := Frame.end_at hs hp.1 hRun hd
  obtain rfl := Option.some.inj (hCode.symm.trans (return_code hsite))
  exact ⟨t, t1, hRun, hLocal, .exit, hOut, rfl, rfl⟩

/-- A non-initial tail state already has a thread event in its prefix. -/
theorem nonempty_tail {d : Machine.ThreadD}
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hne : d ≠ .prologue .shfl0) : X.tr g ≠ [] := by
  intro he
  rw [he, List.length_nil, Frame.stateAt_zero] at hd
  apply hne
  exact (Option.some.inj (Option.some.inj hd)).symm

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingProgress

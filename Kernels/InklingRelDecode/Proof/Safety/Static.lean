-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.All
public import Lemmas.Flow.WaitLoopPcs

@[expose] public section

/-!
# Branches of `Unsafe` decided by the program text

Facts about the decoded program that need no execution: the `tcgen05` instructions agree on their
CTA group (`TcGroupUniform`), no assumption of the kernel but the read-only input assumption
declares an execution undefined, every `mbarrier.try_wait` heads a canonical spin, and the kernel
has no cluster launch control request and no tensor store (`Interface.no_clc`, `no_tensorStore`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The `tcgen05` instructions of the kernel agree on their CTA group.** -/
theorem tc_group_uniform : kernel.TcGroupUniform := kernel_groupUniform

/-! ### The kernel's assumptions declare no execution undefined -/

/-- **No assumption of the kernel declares an execution undefined**, given that the read-only
input assumption does not (`All.lean`, `no_inputReadOnly_ub`): every other one has no `ub`. -/
theorem no_assumption_ub (hin : ¬ Assumptions.inputReadOnly.ub L mem0 X) :
    ¬ ∃ a ∈ asms, a.ub L mem0 X := by
  rintro ⟨a, ha, hu⟩
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact (show False from hu)
    | exact hin hu

/-! ### Every poll is a canonical spin -/

/-- The poll at `pc` is a canonical spin (shape A or B) of the kernel: its loop shape has an exit
and its predicate is read nowhere but by the loop's branch. -/
def spinOk (pc : Nat) : Bool :=
  (kernel.spinExit? pc).isSome &&
    (match kernel.pollDst pc with
      | some p => kernel.spinPred p
      | none => false)

/-- **Each of the kernel's polls is a canonical spin**: all six are shape B,
`mbarrier.try_wait` followed by `@!complete bra.uni` back to the poll. -/
theorem kernel_spins : waitPcs.all spinOk = true := by decide +kernel

theorem canonical_of_spinOk {pc : Nat} (h : spinOk pc = true) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  unfold spinOk at h
  cases hs : kernel.spinExit? pc with
  | none => simp [hs] at h
  | some ex =>
    cases hp : kernel.pollDst pc with
    | none => simp [hs, hp] at h
    | some p =>
      simp only [hs, hp, Option.isSome_some, Bool.true_and] at h
      exact ⟨ex, hs, p, hp, h⟩

/-- **Every poll fires from a canonical spin**: a poll event fires from a listed poll of the
code (`SyncSites.waitPcs`), each of which heads a canonical spin (DEP-CANONICAL-SPIN). -/
theorem poll_spins (hX : Consistent L kernel asms mem0 X) {e : EvId} {pc : Nat} {m : Loc}
    {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get e = some ⟨pc, .wait m p ok acq sc⟩) : ∃ exit, kernel.CanonicalSpin pc exit := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
    · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
      have hop' : isWaitOp ins.op = true := by rw [hop]; rfl
      have hmem := OpPcsFast.mem kernel_wait_pcs hc hop'
      have hall := List.all_eq_true.mp kernel_spins _ hmem
      exact canonical_of_spinOk hall
    · push Not at hw
      exact absurd rfl (Flow.fires_notWait (Flow.eventTmpl_notWait hw) hf m p ok acq sc)

/-- **No poll breaks the canonical shape.** -/
theorem no_pollShapeUnsafe (hX : Consistent L kernel asms mem0 X) :
    ¬ PollShapeUnsafe kernel X := by
  rintro ⟨e, pc, m, q, ok, acq, sc, he, hns, -⟩
  exact hns (poll_spins hX he)

end
end PTX.Kernels.InklingRelDecode.Proof.Safety

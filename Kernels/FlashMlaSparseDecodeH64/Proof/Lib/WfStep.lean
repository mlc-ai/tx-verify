-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Quiet.StoreDrain
public import Lemmas.Step.CommitOrderExtend
public import Lemmas.Kernel.PlainStep

@[expose] public section

/-! # The assumptions' constraints on the extensions of the progress layer

The kernel's assumptions do not satisfy `Assumption.WfStep`: the store drain (`storeDrain`) fails
when an exit is appended to a thread whose output stores still read their source, and the
read-only `ld.global.nc` constraint (`ncReadOnly`) reads `Execution.initial`, which `Execution.le`
does not fix. They satisfy `Assumption.WfQuiet` (`wfQuiet_all`): the numeric and site rules
constrain no execution, the commit order survives in-order extensions, the read-only constraint
survives extensions without a new read and with the initial bytes, and the drain survives
extensions without a new exit. An exit keeps all of them when its thread's selected stores have
finished reading (`wf_snoc_exit`), the premise of `Descent.released_stepsQ`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The stores whose source reads must finish before their thread exits. -/
abbrev drainSel : Nat → Bool := Assumptions.storeDrain.storeReadsBeforeExit

/-- **The assumptions' constraints survive every quiet extension that performs its commit
arrive-ons in order.** -/
theorem wfQuiet_all : Assumption.WfQuiet (fun _ => true) L kernel mem0 Assumptions.all := by
  intro X Y hX hle hord hq a ha
  have hold := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hold
    | exact TensorStore.ReadsDrainedBeforeExit.quietExt hold hle hq
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hold hX.tcCommit hle hord
    | (intro e pc acc bs he hs
       simpa only [Execution.initialByte, hq.initial] using
         hold e pc acc bs (hq.noRead e _ he rfl) hs)

/-- **Appending an event that is no `ld.global.nc` read keeps the constraints** when, if it is an
exit, the thread's selected stores have finished reading their source. -/
theorem wf_snoc (hX : Consistent L kernel Assumptions.all mem0 X) {g : Nat} {e : Event}
    {r : Nat → Option AsyncCopy.Ref} (hnc : ∀ a bs, e.kind ≠ .nc a bs)
    (hd : e.kind = .exit → TensorStore.Drained drainSel X g) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.snoc g e r) := by
  intro a ha
  have hold := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hold
    | exact hold.snoc fun hk i hi hs => hd hk i hi hs
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hold hX.tcCommit le_snoc
        (Execution.notifiedInOrder_of_eq (sel := fun _ => true) rfl)
    | (intro f pc' acc bs he hs
       rw [snoc_get] at he
       split_ifs at he
       · cases he
         exact (hnc acc bs rfl).elim
       · exact hold f pc' acc bs he hs)

/-- **Appending an exit keeps the constraints** when the thread's selected stores have finished
reading their source. -/
theorem wf_snoc_exit (hX : Consistent L kernel Assumptions.all mem0 X) {g pc : Nat}
    {r : Nat → Option AsyncCopy.Ref} (hd : TensorStore.Drained drainSel X g) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.snoc g ⟨pc, .exit⟩ r) :=
  wf_snoc hX (fun _ _ h => by cases h) fun _ => hd

/-- **Appending a weak read keeps the constraints**: the read-only constraint is about the
`ld.global.nc` reads, and the others do not look at reads. -/
theorem wf_snoc_read (hX : Consistent L kernel Assumptions.all mem0 X) {g pc : Nat} {a : Acc}
    {bs : List (Option Byte)} {r : Nat → Option AsyncCopy.Ref} :
    ∀ q ∈ Assumptions.all, q.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r) :=
  wf_snoc hX (fun _ _ h => by cases h) fun h => by cases h

/-- **Appending an `ld.global.nc` read of the launch content keeps the constraints.** -/
theorem wf_snoc_nc (hX : Consistent L kernel Assumptions.all mem0 X) {g pc : Nat} {a : Acc} :
    ∀ q ∈ Assumptions.all,
      q.wf L mem0 (X.snoc g ⟨pc, .nc a (X.launchBytes mem0 a)⟩ (fun _ => none)) := by
  intro q hq
  have hold := hX.asm q hq
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hold
    | exact hold.snoc fun hk => by cases hk
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hold hX.tcCommit le_snoc
        (Execution.notifiedInOrder_of_eq (sel := fun _ => true) rfl)
    | (intro f pc' acc bs he hs
       rw [snoc_get] at he
       split_ifs at he
       · obtain ⟨rfl, rfl⟩ := Kind.nc.inj (congrArg Event.kind (Option.some.inj he))
         refine ⟨by simp [Execution.launchBytes], fun k hk c hc => ?_⟩
         simp [Execution.launchBytes, List.getElem?_range hk, hc]
         rfl
       · exact hold f pc' acc bs he hs)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.MmaVisible
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Step.MmaDrainTmemA

@[expose] public section

/-! # MMA completion from visible operands under quiet extensions

`Lemmas/Step/MmaVisible.lean` under `Assumption.WfQuiet`. -/

namespace PTX
open AsyncCopy MmaSources
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

/-- **A maximal execution has completed every MMA** when the shared operand bytes of each MMA that
has not read its operands have visible writes. -/
theorem Maximal.mma_all_done_visibleQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandVisible L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X)
    {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) : X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false =>
    have hAsm : ∀ i values ra rb, X.le (X.finishMma i values ra rb) →
        ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb) :=
      fun _ _ _ _ hle => hA.quiet hmax.1 hle rfl (Execution.quietExt_of_tr rfl)
    obtain ⟨m, ⟨d', s', a', m', hissue, hdone⟩, hmin⟩ := Proof.ProgressDescent.exists_minimal_of
      (p := fun m => ∃ d s acc mask, X.MmaIssue (i.1, m) d s acc mask ∧
        X.async.mmaDone (i.1, m) = false) id ⟨i.2, d, sp, acc, mask, hi, hn⟩
    have hready : TcMma.CompletionReady L X (i.1, m) := by
      intro p hp
      obtain ⟨hthread, hlt, -, ⟨pd, ps, pa, pmask, -, -, -, -, hpissue, -⟩, -⟩ :=
        TcMma.completionPrecedes_iff.mp hp
      cases hv : X.async.mmaDone p with
      | true => rfl
      | false =>
        have hid : p = (i.1, p.2) := Prod.ext hthread rfl
        have := hmin p.2 ⟨pd, ps, pa, pmask, hid ▸ hpissue, hid ▸ hv⟩
        simp only [id] at this hlt
        omega
    refine (hmax.not_grows ?_).elim
    cases ho : X.async.mmaOperands (i.1, m) with
    | none => exact unstarted_mma_visible hAsm hmax.1 hsg hos hap hinj hissue ho hready
    | some ops =>
      exact started_mma_inOrderQ hA hmax.1
        (by simp only [Snapshot.mmaStarted, ho, Option.isSome_some]) hdone hready

end

end PTX

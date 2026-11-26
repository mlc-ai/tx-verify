-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.Step.CpDrain
public import Lemmas.Quiet.Step.MmaVisible

@[expose] public section

/-! # The MMA obligation steps for visible operands

`Sched.mma_steps_cpQ` with the operand premise `OperandVisible` (some write of each operand byte is
ordered before the read) in place of `OperandSourcesT`: an open MMA obligation of a kernel that
issues `tcgen05.cp` (with sources) and no `tcgen05.shift` steps. -/

namespace PTX
open AsyncCopy MmaSources

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

namespace Sched

variable {M : Timed K A L}

/-- **An open MMA obligation steps**, for a kernel that issues `tcgen05.cp` (with sources) and no
`tcgen05.shift`, whose MMAs' operand bytes have visible writes. -/
theorem mma_steps_cpV (hA : Assumption.WfQuiet sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hsg : SyncGuarded L K X) (hos : OperandVisible L X)
    (hap : TcMma.ATmemApart X) (hinj : TcMma.LayoutInjective X) (hcs : CpSourcesT L A X)
    (hsh : ∀ e s, ¬ X.ShiftIssue e s)
    (ho : Descent.Obl L X .mma) : Steps M mem0 X .mma := by
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
  · exact Maximal.mma_all_done_visibleQ hA hmax hsg hos hap hinj hm
  · exact Maximal.cp_doneQ hA hmax hsg hcs hc
  · exact (hsh i s hs).elim

end Sched

end
end PTX

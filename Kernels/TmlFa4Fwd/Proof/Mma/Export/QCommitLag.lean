-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitLag
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's release of the second Q stage in the time table

`qE_commit_early`: the MMA warp's lane that wins its elections, with no commit to the second Q
stage's empty barrier (24), is before band M's end of the slot after its rounds; it exits after
the commit (`qE_total`, `mma_exit_commits`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (commitAt)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The tile's commit to the second Q stage's empty barrier. -/
theorem qE_total (R : Nat) : commitAt 100 R 24 = 1 := by
  simp [commitAt, Mma.pq]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
  (hwin : ∀ j pc mk inst ld, X.get (g, j) = some ⟨pc, .elect mk inst ld⟩ → ld = laneOf L g)
  {R : Nat} (hR : MmaRounds p L g R)
include hp hX hFw hub hg hw hwin hR

/-- A lane with no commit to the second Q stage's empty barrier. -/
theorem qE_commit_early (ha : (X.tr g).countP (commitsTo (obj L g 24)) ≤ 0) :
    Sched.threadTime (Progress.timed p L) X g < Progress.clk p (R + 1) 512 := by
  have hend := qE_total R
  refine mma_commit_early hp hX hFw hub hg hw hwin hR ?_ (by omega) ?_ ha
  · exact Progress.primeBase_le_clk p _ _
  · intro q r h1 h2 h3 h4 hc
    refine pipeT_succ_lt h1 ?_
    split
    · omega
    · have : r ≤ R := by
        rcases Nat.lt_or_ge q 60 with h6 | h6
        · exact (h3 ⟨by omega, h6⟩).le
        · exact (h4 h6).le
      omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof

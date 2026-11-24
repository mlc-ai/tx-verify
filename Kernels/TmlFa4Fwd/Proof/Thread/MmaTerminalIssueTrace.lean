-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open Thread

theorem TerminalOutputIssues.ofTrace {l : Launch} {X Y : Execution} {g : Nat}
    (issues : TerminalOutputIssues l X g) (tr : Y.tr = X.tr) : TerminalOutputIssues l Y g := by
  intro s
  obtain ⟨i,j,hw,ev⟩ := issues s
  refine ⟨i,j,hw,?_⟩
  simpa only [Scores.TerminalOutputCommit,FirstOutputCommit,SecondOutputCommit,Execution.get,tr]
    using ev

end PTX.Kernels.TmlFa4Fwd.Mma

-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The commit sites of the code

Every `tcgen05.commit` of the decoded program is at pc 1982, 2105 or 2148 (the MMA lane's commits
to `bar_q_utccp`, `qk_done` and `sv_done`): a static scan evaluated once (`commitSites`), so a
commit event of a consistent execution is at one of them (`commit_pcs`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

set_option maxRecDepth 100000 in
private theorem commitSites : OpPcsFast kernel.code commitOp [1982, 2105, 2148] = true := by
  decide +kernel

/-- **The commit sites**: a commit event of a consistent execution is at pc 1982, 2105 or 2148. -/
theorem commit_pcs (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat}
    {sp : TcCommit.Spec} (he : X.get i = some ⟨pc, .tc (.commit sp)⟩) :
    pc ∈ [1982, 2105, 2148] := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · cases h : commitOp ins.op
    · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) hf sp rfl).elim
    · exact OpPcsFast.mem commitSites hc h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

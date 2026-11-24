-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingProgress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RegisterRequestTrace
import Lemmas.Step.RegIssue

public section

/-! # Counted register requests at the warpgroup hand-off -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- A released lane at hand-off can issue the first register request of its warpgroup. -/
theorem prologue_handoff_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {w : Fin 3}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue (.handoff w)))) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn := ClosingProgress.nonempty_tail hState (by simp)
  have hNo := RegisterRequestTrace.no_request_at_prologue hX (hs g hp.1).machine hp.1 hState
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, _, hTau, _, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  obtain rfl := Option.some.inj (hc.symm.trans (RegisterRequestTrace.handoff_code w))
  let p := RegisterRequestTrace.payload w.val
  have hv : SetMaxNReg.validCount p.2 = true := RegisterRequestTrace.payload_valid w
  change out kernel Assumptions.all L g u = .ev (SetMaxNReg.tmpl u p.1 p.2) at hout
  simp only [SetMaxNReg.tmpl, hv, ↓reduceIte] at hout
  exact PTX.Step.reg_issue_counted_extension_of_started hX hp.1 hn hrel.ready hNo hRun hTau
    (pc := u.pc) (inc := p.1) (n := p.2) (inst := 0) (o := some (PTX.next u))
    ⟨_, hout, 0, rfl, rfl⟩ (Interface.all_wf_snoc_of_not_nc hX nofun nofun)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

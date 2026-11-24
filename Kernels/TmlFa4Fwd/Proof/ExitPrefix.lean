-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Mma

noncomputable section

/-- The shared return path of the MMA and output warps contributes at most its terminal event. -/
theorem sharedExitPrefixBound {l : Launch} {g warp : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : s.pc = 3099) (hf : s.fault = none)
    (hRole : warp = 12 ∨ warp = 13) (hWarp : s.regs 1062 = some (b32 warp)) :
    countedUntil 9206 vs ≤ 1 := by
  have hModel {t : TState} (hs : t.pc ∈ [3099, 3100, 7742, 7743, 7744, 9205]) :
      out kernel Assumptions.all l g t = out kernel [] l g t := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    apply epilogue_out_all_eq_nil
    unfold EpiloguePc
    omega
  obtain ⟨u, hr, _, hOut⟩ := finishSchedulerOfWarpWith l g s hModel hp hf hRole hWarp
  rcases advanceWalkLocals hr hw with he | ⟨tail, _, hPrefix, hWalk⟩
  · subst es
    simp [zeroCountNoEvents hw]
  · apply (hPrefix 9206).trans
    have hn : Stops kernel Assumptions.all l g u := ⟨_, hOut⟩
    cases hWalk with
    | stop => simp [countedUntil]
    | tau ht _ => exact (not_tau_of_stops hn ht).elim
    | ev he _ =>
      obtain ⟨m, hm, hf⟩ := he
      have hT : m = .exit := Out.ev.inj (hm.symm.trans hOut)
      subst m
      cases hf.2
    | @last u e he =>
      by_cases hPc : u.pc < 9206
      · simpa [countedUntil, visit_pc, visit_ev, hPc] using
          (List.countP_le_length (p := Event.counts) (l := [e]))
      · simp [countedUntil, visit_pc, hPc]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue

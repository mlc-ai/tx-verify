-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Abi
public import Kernels.TmlFa4Fwd.Proof.PrologueBroadcast
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section

/-- All roles first reach the full-warp shared-base broadcast with their ABI registers loaded. -/
theorem firstBroadcastWith {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m) (g : Nat) :
    ∃ t, Next kernel A l g {} t (broadcastTemplate t 2535 (b32 l.sharedBase)) ∧
      At t 25 (abiFacts p l) := by
  obtain ⟨t, hrun, ht⟩ := startWith (A := A) hpre g
  have hmem : (1665, b32 l.sharedBase) ∈ abiFacts p l := by simp [abiFacts]
  have hreg := holds_mem ht.2.2.2.2 hmem
  exact ⟨t, ⟨run_rtg hrun, startupOut (.inl (by rw [ht.1]; decide))
    (sharedBroadcastOut hpre.block ht.1 ht.2.2.2.1 hreg)⟩, ht⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue

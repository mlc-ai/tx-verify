-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
public import Kernels.TmlFa4Fwd.Proof.ProloguePrefetch
public import Kernels.TmlFa4Fwd.Proof.PrologueElect
public import Lemmas.Protocol.ElectCount
public import Lemmas.Step.WarpElect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof

noncomputable section

theorem warp0FirstElection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 0) (hlen : 3 ≤ (X.tr g).length) :
    ∃ t u o, Run kernel Assumptions.all l g
      ({} : TState) ((X.tr g).take 3) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop 3) o ∧
      At u 46 [(1062, b32 0), (2535, b32 l.sharedBase)] ∧ Next kernel Assumptions.all l g t u
        (.elect (2 ^ 32 - 1) (electedState l g u (electSite 0))) := by
  obtain ⟨e₀, e₁, e₂, he⟩ := broadcastTraceSplit hlen
  obtain ⟨t, o, hPc, hFault, hBase, hW, _, hAbi, hSub, hAcc, hRun, hPrefix⟩ :=
    broadcastPrefixRun hp hX g hg he
  have hQ := holds_mem hAbi (by simp [abiFacts] :
    (7291, .ptr 64 false (.param (param 9)) 0) ∈ abiFacts p l)
  have hO := holds_mem hAbi (by simp [abiFacts] :
    (7290, .ptr 64 false (.param (param 10)) 0) ∈ abiFacts p l)
  have hB := holds_mem hAbi (by simp [abiFacts] :
    (7289, .ptr 64 false (.param (param 11)) 0) ∈ abiFacts p l)
  rw [hw] at hW
  obtain ⟨u, hu, hupc, huf, hus, hua, huRegs⟩ :=
    warp0PrefetchWith (A := Assumptions.all) hp g t hPc hFault hSub hAcc hW hQ hO hB
  have hTake : (X.tr g).take 3 = [e₀, e₁, e₂] := by
    conv_lhs => rw [he]
    rfl
  refine ⟨t, u, o, hTake ▸ hPrefix, hRun, ⟨hupc, hus, hua, huf, ?_⟩, run_rtg hu,
    startupOut (.inl (by rw [hupc]; decide)) (electOut 0 hupc huf)⟩
  exact ⟨(huRegs 1062 (by decide)).trans hW, (huRegs 2535 (by decide)).trans hBase, trivial⟩

theorem warp0LaneWitness {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g lane : Nat} (hg : g < l.threads) (hw : warpIndex l g = 0) (hlane : lane < 32) :
    ∃ h, SameWarp l g h ∧ laneOf l h = lane := by
  let h := g / 512 * 512 + lane
  have hw' : g % 512 / 32 = 0 := by simpa [warpIndex, hp.block] using hw
  rw [Launch.threads, hp.block] at hg
  have hh : h < l.grid * 512 := by dsimp [h]; omega
  have hc : h / 512 = g / 512 := by dsimp [h]; omega
  have ht : h % 512 = lane := by dsimp [h]; omega
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · simp only [SameCta, Launch.threads, hp.block]
    exact ⟨hg, hh, hc.symm⟩
  · rw [hp.block, ht, hw', Nat.div_eq_of_lt hlane]
  · rw [laneOf, hp.block, ht, Nat.mod_eq_of_lt hlane]

end
end PTX.Kernels.TmlFa4Fwd.Prologue

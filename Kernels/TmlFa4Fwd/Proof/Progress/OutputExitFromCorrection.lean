-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OutputRoleExit
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionReadyOfExit
public import Kernels.TmlFa4Fwd.Proof.Thread.Machine

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread

/-- The active output warp exits once its CTA's correction lanes have exited. -/
theorem outputExitsOfCorrectionExits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hRole : roleOf l g = .output)
    (hCuQ : DrainCuQProtected p X)
    (hActive : g/l.block < tilePrefix p p.batch * p.heads)
    (hCorrection : ∀ lane < l.threads, roleOf l lane = .correction →
      lane/l.block = g/l.block → Exited X lane) : Exited X g := by
  have hw : warpIndex l g = 13 := by
    dsimp only [roleOf] at hRole
    split_ifs at hRole
    assumption
  apply outputExitsOfPublishedCohorts hp hMax hg hw hCuQ hActive
  intro stage row hRow
  let lane := Output.sourceLane l (g,0) row
  have hCta : lane/l.block = g/l.block := by
    dsimp only [lane,Output.sourceLane,Prod.fst]
    rw [hp.block]
    omega
  have hOffset : lane % l.block = 256 + row := by
    dsimp only [lane,Output.sourceLane,Prod.fst]
    rw [hp.block]
    omega
  have hLane : lane < l.threads := by
    have hG : g/l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    exact (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).1 (hCta ▸ hG)
  have hLo : 8 ≤ warpIndex l lane := by
    unfold warpIndex
    omega
  have hHi : warpIndex l lane < 12 := by
    unfold warpIndex
    omega
  have hCorrectionRole : roleOf l lane = .correction := by
    simp [roleOf,Nat.not_lt_of_ge hLo,hHi]
  exact correctionReadyOfActiveExit hp hMax.1 hLo hHi (hCta ▸ hActive)
    (hCorrection lane hLane hCorrectionRole hCta) stage

end PTX.Kernels.TmlFa4Fwd.Progress

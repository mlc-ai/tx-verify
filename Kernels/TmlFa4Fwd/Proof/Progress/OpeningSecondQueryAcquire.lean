-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningQK
public import Kernels.TmlFa4Fwd.Proof.Progress.FirstQueryReadyPhase
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondQueryProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.SecondQueryReadyPhase
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier Prologue Epilogue Thread.Output

/-- The opening Q1 object has completed its sole query packet for the selected request. -/
theorem openingSecondQueryReadyPhaseOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads) :
    let log := X.objects (queryObject l cta 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  by_cases hSome : ∃ r ∈ X.objects (queryObject l cta 1), r.reply.waited = some true
  · obtain ⟨r,hr,hSuccess⟩ := hSome
    exact Protocol.Query.secondQueryReadyOfPriorSuccess hp hMax.1 hr hSuccess
  · let loader := cta*l.block+448
    have hCta : loader/l.block = cta := by dsimp [loader]; rw [hp.block]; omega
    have hWarp : warpIndex l loader = 14 := by
      simp only [warpIndex,loader,hp.block]
      omega
    have hg : loader < l.threads := by simp only [Launch.threads,loader,hp.block]; omega
    exact hCta ▸ selectedSecondQueryReadyPhaseOfMaximal hp hMax hFrame hg hWarp hb
      (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSome)

end PTX.Kernels.TmlFa4Fwd.Progress

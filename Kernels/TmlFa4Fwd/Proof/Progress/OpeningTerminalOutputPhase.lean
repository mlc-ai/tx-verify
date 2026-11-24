-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTerminalOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalOutputPhase
import Kernels.TmlFa4Fwd.Proof.Progress.Async
import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputNotification

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.MBarrier Prologue Epilogue

/-- In a selected one-visit CTA every correction lane can observe the completed output stage. -/
theorem singleVisitTerminalOutputPhaseOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) (stage : Fin 2) :
    let log := X.objects (Thread.outputCompletionObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  let g := cta*l.block+384
  have hLane : 384 < l.block := by rw [hp.block]; decide
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hLane
  obtain ⟨hCta,hLocal⟩ := NamedBar.lane_cta (c := cta)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  change g/l.block = cta at hCta
  have hw : warpIndex l g = 12 := by unfold warpIndex g; rw [hLocal]
  have hIssues := (singleVisitTerminalPvAndOutputIssuesOfMaximal hp hMax hFrame hg hw hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle)).2
  obtain ⟨r,hr,hArr⟩ := Thread.terminalOutputNotification hMax.1 hIssues stage
    (mmaAndCommitsDrained hp hMax hFrame).2
  rw [hCta] at hr
  exact Protocol.Output.terminalOutputPhaseOfNotification hp hMax.1 stage hr hArr

end PTX.Kernels.TmlFa4Fwd.Progress

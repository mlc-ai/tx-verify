-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedSumTail
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityDenominatorProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- The actual repeated-visit counter selects the next head or loop exit.
The denominator cut advances locally while its recorded trace end stays fixed. -/
theorem repeatedLoopOfDenominatorCursor {l : Launch} {X : Execution} {g : Nat}
    (mode : Repeated) (maximum : Option ℝ) (mass : ℝ) (word : Nat) (hWord : word < 2^32)
    (phase biasPhase scorePhase : Bool) (c : OpeningTripCursor l X g mode.sumEnd [(7257,fl mass)])
    (hMax : c.ready.regs 7256 = some (scoreValue maximum))
    (hCounter : c.ready.regs (scoreLoopSite mode.loop).word = some (b32 word))
    (hPhase : c.ready.regs 7258 = some (b32 phase.toNat))
    (hBiasPhase : mode = .biased → c.ready.regs 7250 = some (b32 biasPhase.toNat))
    (hScorePhase : c.ready.regs 7253 = some (b32 scorePhase.toNat)) :
    let site := scoreLoopSite mode.loop
    let nextWord := (word+1)%2^32
    let pc := if nextWord ≠ site.sentinel then site.head else site.increment+4
    let facts := [(site.word,b32 nextWord),(roundPriorMaxReg mode.loop,scoreValue maximum),
        (7256,scoreValue maximum),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
      tailPhaseWords (!biasPhase) (!scorePhase) mode.loop
    ∃ after : OpeningTripCursor l X g pc facts,
      after.pos = c.pos ∧ after.ending = c.ending ∧
      (mode = .biased → after.ready.regs 7249 = c.ready.regs 7249) ∧
      ∀ r ∈ loopResident mode.loop, after.ready.regs r = c.ready.regs r := by
  dsimp only
  obtain ⟨u,hAt,hStep,hBlock⟩ := repeatedLoopOfDenominatorLocal mode maximum mass word hWord
    phase biasPhase scorePhase (c.checkpoint.mono trivial) c.checkpoint.2.2.2.2.1
    hMax hCounter hPhase hBiasPhase hScorePhase
  refine ⟨⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hAt,c.recorded,
    c.remaining,c.localSteps.trans hStep⟩,rfl,rfl,hBlock,?_⟩
  have hLo : (scoreLoopSite mode.loop).head ≤ c.ready.pc := by
    rw [c.checkpoint.1]
    cases mode <;> decide
  have hSub : c.ready.sub ≤ 3 := by rw [c.checkpoint.2.1]; decide
  have hEnd : u.pc ≤ threshold mode.loop false := by
    rw [hAt.1]
    split <;> cases mode <;> decide
  exact scoreTraceKeepsResidents mode.loop (TraceReach.of_local hStep) hLo hEnd hSub

end PTX.Kernels.TmlFa4Fwd.Softmax

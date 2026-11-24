-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedSum
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRoundLoopTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof
open scoped BigOperators

def Repeated.loop : Repeated → ScoreLoop
  | .biased => .biased
  | .unbiased => .plain

variable {l : Launch}

/-- Advance the actual control tail from the reduced mass without executing
another collective or reading from the lane's future trace. -/
theorem repeatedLoopOfDenominatorLocal {g : Nat} {t : TState} (r : Repeated) (mx : Option ℝ)
    (mass : ℝ) (word : Nat) (hw : word < 2^32) (phase biasPhase scorePhase : Bool)
    (ht : At t r.sumEnd []) (hMass : t.regs 7257 = some (fl mass))
    (hMax : t.regs 7256 = some (scoreValue mx))
    (hCounter : t.regs (scoreLoopSite r.loop).word = some (b32 word))
    (hPhase : t.regs 7258 = some (b32 phase.toNat))
    (hBiasPhase : r = .biased → t.regs 7250 = some (b32 biasPhase.toNat))
    (hScorePhase : t.regs 7253 = some (b32 scorePhase.toNat)) :
    let site := scoreLoopSite r.loop
    let nextWord := (word+1)%2^32
    ∃ u, At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
      ([(site.word,b32 nextWord),(roundPriorMaxReg r.loop,scoreValue mx),(7256,scoreValue mx),
        (7257,fl mass),(7258,b32 (!phase).toNat)] ++
        tailPhaseWords (!biasPhase) (!scorePhase) r.loop) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (r = .biased → u.regs 7249 = t.regs 7249) := by
  let site := scoreLoopSite r.loop
  cases r
  case biased =>
    obtain ⟨u,hu,hGo,hBlock⟩ := repeatedLoopTailCarriesStateLocal .biased phase biasPhase scorePhase
      word hw mx mass
      (ht.mono ⟨hBiasPhase rfl,
        hScorePhase,hCounter,hMax,hMass,hPhase,trivial⟩)
    exact ⟨u,hu,hGo,fun _ => hBlock⟩
  case unbiased =>
    let facts := [(site.word,b32 word),(7256,scoreValue mx),(7257,fl mass),(7258,b32 phase.toNat)]
    have hStart : At t 7599 ((7253,b32 scorePhase.toNat)::facts) :=
      ht.mono ⟨hScorePhase,hCounter,hMax,hMass,hPhase,trivial⟩
    obtain ⟨v,hLocal,hv⟩ := (plainSumTailToCreditToggle (l := l) (g := g) scorePhase
      facts (by
        intro item hItem
        simp only [facts,site,Repeated.loop,scoreLoopSite,List.mem_cons,List.not_mem_nil,
          or_false] at hItem
        rcases hItem with rfl | rfl | rfl | rfl <;> dsimp only <;> decide)).apply hStart
    obtain ⟨u,hu,hGo,_⟩ := repeatedLoopTailCarriesStateLocal .plain phase biasPhase (!scorePhase)
      word hw mx mass
      (hv.mono hv.2.2.2.2)
    exact ⟨u,hu,(run_rtg hLocal).trans hGo,nofun⟩

/-- From the returned correction acknowledgement, the true local reduction
and loop tail carry the next denominator, reference, and phase together. -/
theorem repeatedSumAndLoopTailLocal {g : Nat} {t : TState} (r : Repeated) (weights : Nat → ℝ)
    (old alpha : ℝ) (mx : Option ℝ) (word : Nat) (hw : word < 2^32)
    (phase biasPhase scorePhase : Bool) (ht : At t r.sumStart [])
    (hWeights : RepeatedWeights r t weights) (hOld : t.regs 7257 = some (fl old))
    {alphaWord : Value} (hAlpha : t.regs r.alphaReg = some alphaWord)
    (hAlphaValue : valFloat .f32 alphaWord = .ok alpha) (hMax : t.regs 7256 = some (scoreValue mx))
    (hCounter : t.regs (scoreLoopSite r.loop).word = some (b32 word))
    (hPhase : t.regs 7258 = some (b32 phase.toNat))
    (hBiasPhase : r = .biased → t.regs 7250 = some (b32 biasPhase.toNat))
    (hScorePhase : t.regs 7253 = some (b32 scorePhase.toNat)) :
    let site := scoreLoopSite r.loop
    let nextWord := (word+1)%2^32
    let mass := old*alpha+∑ i ∈ Finset.range 128, weights i
    ∃ u, At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
      ([(site.word,b32 nextWord),(roundPriorMaxReg r.loop,scoreValue mx),(7256,scoreValue mx),
        (7257,fl mass),(7258,b32 (!phase).toNat)] ++
        tailPhaseWords (!biasPhase) (!scorePhase) r.loop) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (r = .biased → u.regs 7249 = t.regs 7249) := by
  obtain ⟨s,hs,hTail,hFrame⟩ := repeatedRowSumLocalOfWordWithFrame (l := l) (g := g) r weights
    old alpha ht hOld hAlpha hAlphaValue hWeights
  let mass := old*alpha+∑ i ∈ Finset.range 128, weights i
  let site := scoreLoopSite r.loop
  have hMax' := (hFrame 7256 (by decide)).trans hMax
  have hCounter' := (hFrame site.word (by cases r <;> decide)).trans hCounter
  have hPhase' := (hFrame 7258 (by decide)).trans hPhase
  have hScorePhase' := (hFrame 7253 (by decide)).trans hScorePhase
  obtain ⟨u,hu,hGo,hBlock⟩ := repeatedLoopOfDenominatorLocal r mx mass word hw phase
    biasPhase scorePhase (hs.mono trivial) hs.2.2.2.2.1 hMax' hCounter' hPhase'
    (fun h => (hFrame 7250 (by decide)).trans (hBiasPhase h)) hScorePhase'
  exact ⟨u,hu,hTail.trans hGo,fun h => (hBlock h).trans (hFrame 7249 (by decide))⟩

end PTX.Kernels.TmlFa4Fwd.Softmax

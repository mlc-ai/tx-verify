-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedRound
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalNumerics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Numeric Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (warp : Fin 8)
    {g j b h row blocks visited : Nat} (hWarp : warp.val = warpIndex l g) {t : TState}
    (old : Option ℝ) (nextBlock floor : Nat) (phase biasPhase scorePhase : Bool)
    (refs : Nat → Option ℝ) (sums : Nat → ℝ)
    (hPrefix : SoftmaxSumPrefix p b h row blocks visited refs sums) (hVisited : 0 < visited)
    (hReference : refs (visited-1) = old.map (abiFloat p.scaleLog2Bits * ·))
    (ht : At t (biasBodyStart true+4*biasBodyPairs true) [])
    (hLogits : ∀ i ∈ biasBodyItems true,
      let score := fun c => maskedLogit p b h row (visitKey blocks visited c)
      t.regs i.result = some (.pair (scoreValue (score (2*(i.qk-7367))))
        (scoreValue (score (2*(i.qk-7367)+1)))))
    (hPrior : Holds t.regs
      [(7251,scoreValue old),(7257,fl (sums (visited-1))),(7249,b32 nextBlock),(1361,b32 floor),
        (7258,b32 phase.toNat),(1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
        (1230,fl (-abiFloat p.scaleLog2Bits)),(7132,b32 p.scaleLog2Bits)]) (word : Nat)
    (hWord : word < 2^32)
    (hControl : Holds t.regs
      [(7250,b32 biasPhase.toNat),(7253,b32 scorePhase.toNat),(7248,b32 word)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp warp hWarp old nextBlock floor phase biasPhase scorePhase refs sums hPrefix hVisited
    hReference ht hLogits hPrior word hWord hControl hRun

/-- The biased round extends the denominator and publishes P from the same coefficient and
exactly the same visited block. The carried previous state supplies the old denominator. -/
theorem biasedDenominatorVisitOfLogitsWithPath :
    let stage := stageOf warp
    let scale := abiFloat p.scaleLog2Bits
    ∃ u endPos candidate mass bar,
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      let weights := fun col => shiftedWeight p b h row (visitKey blocks visited col)
        (ref.getD 0)
      let events := Repeated.probabilityEvents .biased l g stage weights
      let site := scoreLoopSite .biased
      let nextWord := (word+1)%2^32
      j+2+events.length < endPos ∧
      SoftmaxSumPrefix p b h row blocks (visited+1)
        (Function.update refs visited ref) (Function.update sums visited mass) ∧
      X.get (g,j) = some ⟨5682,.wr (statsAcc l g warp 0) (alphaWord scale old candidate).toBytes⟩ ∧
      (∀ k : Fin events.length, X.get (g,j+2+k.val) = events[k.val]?) ∧
      At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
        ([(site.word,b32 nextWord),(roundPriorMaxReg .biased,scoreValue chosen),
          (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
          tailPhaseWords (!biasPhase) (!scorePhase) .biased) ∧
      X.get (g,j+2+events.length+1) =
        some ⟨probabilityWaitPc .biased true+1,.warpBar (2^32-1) bar⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (endPos-j)) u ∧
      ((X.tr g).take endPos).countP earlyProbabilityMark =
        ((X.tr g).take j).countP earlyProbabilityMark + 1 ∧
      u.regs 7249 = some (b32 nextBlock) := by
  obtain ⟨candidate,u,endPos,bar,hCandidate,hStore,_,hEvents,hBar,hBefore,hAt,hTail,hPath,hEarly,
    hBlock⟩ :=
    biasedRoundFromLogitsWithPath hp warp hWarp old (sums (visited-1)) nextBlock floor
      phase biasPhase scorePhase ht hLogits hPrior word hWord hControl hRun
  have hCandidateZero :=
    ((hCandidate (scoreReal candidate)).mp le_rfl).2 0 (by decide)
  let scale := abiFloat p.scaleLog2Bits
  let ref := (chosenReference scale old candidate).map (scale * ·)
  let mass := sums (visited-1)*maskedRescale (old.map (scale * ·)) ref +
    (2 : ℝ)^(-ref.getD 0)*maskedBlockSum (p.keyCount b row) blocks visited (weight p b h row)
  have hR : u.regs 7257 = some (fl mass) := by
    exact holds_mem hAt.2.2.2.2 (by simp [mass,ref,scale])
  have hNext := appendRepeatedSum hPrefix hVisited old candidate hCandidateZero mass
    (by simp only [mass,hReference]; rfl) hR
  exact ⟨u,endPos,candidate,mass,bar,hBefore,hNext.1,hStore,hEvents,hAt,hBar,hTail,hPath,hEarly,
    hBlock⟩

end

end PTX.Kernels.TmlFa4Fwd.Softmax

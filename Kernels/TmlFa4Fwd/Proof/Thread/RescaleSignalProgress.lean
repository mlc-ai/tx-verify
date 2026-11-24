-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalCreditProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleSignal
import all Kernels.TmlFa4Fwd.Proof.CorrectionRescaleSignal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue

/-- A reached correction lane posts both rescale credits, retaining the
lane's recorded prefix and continuation for the next stage or loop latch. -/
theorem rescaleSignalsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (rescaleSignalPc stage) F)
    (hCredit : (outputCreditReg stage,b32 (creditLoc l g stage).addr) ∈ F)
    (hReuse : (rescaleReuseReg stage,b32 (rescaleReuseLoc l g stage).addr) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ rescaleCountReg stage ∧
      pair.1 ≠ rescaleSignalDst stage ∧ pair.1 ≠ rescaleSignalDst stage+1) :
    X.Arrive (g,c.pos) (creditLoc l g stage) 0 1 true .cta ∧
      X.Arrive (g,c.pos+1) (rescaleReuseLoc l g stage) 0 1 true .cta ∧
      ∃ d : OpeningTripCursor l X g (rescaleSignalPc stage+3) F, d.pos = c.pos+2 := by
  let s := next (setReg c.ready (rescaleCountReg stage) (b32 1))
  have hMove : run kernel [] l g 1 c.ready = some s := by
    apply run_local (rescaleCountCode stage) rfl c.checkpoint
    rw [execLocalA_nil,execLocal_move rfl]
    simp [execMove,readValue,readBits,Value.bytes,b32,bind,Except.bind,pure,Except.pure,
      DType.width,s,truncBits]
  have hModel : out kernel Assumptions.all l g c.ready = out kernel [] l g c.ready :=
    rescaleSignalCore stage (off := 0) (by decide) (by simpa using c.checkpoint.1)
      (by simpa using rescaleCountCode stage) rfl
  have hRun : run kernel Assumptions.all l g 1 c.ready = some s := by
    simpa only [run,tauStep,hModel] using hMove
  let G := (rescaleCountReg stage,b32 1)::F
  let a : OpeningTripCursor l X g (rescaleSignalPc stage+1) G :=
    ⟨c.pos,c.before,s,c.ending,c.positive,c.bounded,c.released,
      c.checkpoint.set (fun pair hm => (hFresh pair hm).1),c.recorded,c.remaining,
      c.localSteps.trans (run_rtg hRun)⟩
  have hf {pair} (hm : pair ∈ G) :
      pair.1 ≠ rescaleSignalDst stage ∧ pair.1 ≠ rescaleSignalDst stage+1 := by
    rcases List.mem_cons.mp hm with rfl | h
    · fin_cases stage <;> decide
    · exact (hFresh pair h).2
  have hBound := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  have hCreditOut := correctionReleaseOut (l := l) (g := g) (off := 0) a.checkpoint
    (rescaleSignalCore stage (by decide) a.checkpoint.1 (rescaleCreditCode stage) rfl)
    (rescaleCreditCode stage) (holds_mem a.checkpoint.2.2.2.2 (List.mem_cons_of_mem _ hCredit))
    a.checkpoint.2.2.2.2.1 (by unfold creditLoc; simp only; omega)
    (by unfold creditLoc; simp only; omega)
  obtain ⟨hA,b,hB⟩ := unitArrivalOfMaximal hMax hg a hCreditOut (fun _ hm => (hf hm).1)
  have hReuseOut := correctionReleaseOut (l := l) (g := g) (off := 0) b.checkpoint
    (rescaleSignalCore stage (by decide) b.checkpoint.1 (rescaleReuseCode stage) rfl)
    (rescaleReuseCode stage) (holds_mem b.checkpoint.2.2.2.2 (List.mem_cons_of_mem _ hReuse))
    b.checkpoint.2.2.2.2.1 (by unfold rescaleReuseLoc; simp only; omega)
    (by unfold rescaleReuseLoc; simp only; omega)
  obtain ⟨hR,d,hD⟩ := unitArrivalOfMaximal hMax hg b hReuseOut (fun _ hm => (hf hm).2)
  refine ⟨⟨_,hA⟩,⟨_,hB ▸ hR⟩,⟨d.pos,d.before,d.ready,d.ending,d.positive,d.bounded,d.released,
    d.checkpoint.mono d.checkpoint.2.2.2.2.2,d.recorded,d.remaining,d.localSteps⟩,?_⟩
  rw [hD,hB]

end PTX.Kernels.TmlFa4Fwd.Correction

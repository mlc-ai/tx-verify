-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityStores
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOpeningProbability
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningProbabilityTail
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue

/-- The 128 softmax lanes and 128 correction lanes complete each active CTA's
opening joint probability and rescale phase. -/
theorem openingMainProbabilityAdvancedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {cta batch : Nat} (hc : cta < l.grid) (stage : Fin 2)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads) :
    let log := X.objects (Thread.Scores.probabilityObject l cta stage 0)
    ∃ s, MBarrier.stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  classical
  let lane (j : Fin 256) := if j.val < 128 then 128*stage.val+j.val else 128+j.val
  let thread (j : Fin 256) := cta*l.block+lane j
  have hCredit (j : Fin 256) : ∃ i, Thread.Scores.ProbabilityCredit l X
      (thread j,i) cta stage 0 := by
    have hStage := stage.isLt
    have hj := j.isLt
    have hl : lane j < l.block := by
      rw [hp.block]
      dsimp [lane]
      split <;> omega
    have hg : thread j < l.threads := NamedBar.cta_thread_lt hc hl
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hl
    change thread j/l.block = cta at hOwner
    change thread j%l.block = lane j at hLocal
    by_cases hSoftmax : j.val < 128
    · have hRole : warpIndex l (thread j)/4 = stage.val := by
        rw [warpIndex,hLocal]
        simp only [lane,ite_eq_left hSoftmax]
        omega
      obtain ⟨i,hCredit⟩ := openingProbabilityCreditOfMaximal hp hMax hFrame hg stage hRole
        hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
      exact ⟨i,hOwner ▸ hCredit⟩
    · have hRole : 8 ≤ warpIndex l (thread j) ∧ warpIndex l (thread j) < 12 := by
        rw [warpIndex,hLocal]
        simp only [lane,ite_eq_right hSoftmax]
        omega
      obtain ⟨i,hCredit⟩ := Correction.openingJointProbabilityCreditOfMaximal hp hMax hg
        hRole.1 hRole.2 stage
      exact ⟨i,hOwner ▸ hCredit⟩
  choose idx hIssued using hCredit
  let credits (j : Fin 256) : EvId := (thread j,idx j)
  have hDistinct : Function.Injective credits := by
    intro a b hEq
    have hLane := congrArg Prod.fst hEq
    change cta*l.block+lane a = cta*l.block+lane b at hLane
    apply Fin.ext
    have hStage := stage.isLt
    dsimp only [lane] at hLane
    split_ifs at hLane <;> omega
  have hCuQ : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  exact Protocol.Scores.probabilityAdvancedOfCredits hp hMax.1 stage 0 credits
    hDistinct hIssued
    (fun _ => Protocol.Scores.jointProbabilityHistoryNoFaultOfCuQ hp hMax.1 hCuQ stage)

end PTX.Kernels.TmlFa4Fwd.Progress

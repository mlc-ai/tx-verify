-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleVisit
public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleSetup
import Kernels.TmlFa4Fwd.Flow.Code.Part131

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The counter changes across a pair of visits, while both sets of physical addresses remain. -/
def rescaleLoopFacts (F : Nat → List (Nat × Value)) (blocks lane : Nat) : List (Nat × Value) :=
  (7278, remainingRescaleWord blocks) :: F lane

private theorem rescaleCountCore {l : Launch} {g : Nat} {t : TState}
    (hLo : 8444 ≤ t.pc) (hHi : t.pc < 8446) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hPc : t.pc = 8444 ∨ t.pc = 8445 := by omega
  rcases hPc with h | h
  · apply Assumptions.out_all_eq_nil _ _ _ (h.symm ▸ Flow.code_8444) rfl
    all_goals rw [h]; decide
  · apply Assumptions.out_all_eq_nil _ _ _ (h.symm ▸ Flow.code_8445) rfl
    all_goals rw [h]; decide

/-- The two counter instructions and the conditional branch preserve a lane's
tile registers and select the next rescale or finalization rendezvous. -/
theorem rescaleCountSteps {l : Launch} {thread blocks : Nat} {t : TState}
    {F : List (Nat × Value)} (hBlocks : 2 ≤ blocks) (hBound : blocks < 2^31)
    (ht : At t 8444 ((7278,remainingRescaleWord blocks)::F))
    (hFresh : ∀ r ∈ F.map Prod.fst, r ≠ 7278 ∧ r ≠ 735) :
    ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l thread) t v ∧
      At v (if 2 < blocks then 8006 else 8447) ((7278,remainingRescaleWord (blocks-1))::F) := by
  obtain ⟨s, hs, hS⟩ := rescaleNextCount l thread hBlocks hBound t
    (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  have hFallthrough : ((kernel.code.drop 8444).take 1).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hWrite : ((kernel.code.drop 8444).take 2).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    have hStart : (kernel.code.drop 8444).take 2 =
        [⟨none, .int ⟨.add, .int .s 32, false, [some 7278], [.reg 7278, .imm 1]⟩⟩,
         ⟨none, .int ⟨.setp .ne none, .int .b 32, false, [some 735],
           [.reg 7278, .imm (-1)]⟩⟩] := by
      set_option maxRecDepth 100000 in kernel_rfl
    rw [hStart]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    constructor <;> apply List.all_eq_true.mpr <;> intro r hr
    · have hNe := (hFresh r hr).1
      change !([(7278 : Nat)].contains r) = true
      simpa using hNe
    · have hNe := (hFresh r hr).2
      change !([(735 : Nat)].contains r) = true
      simpa using hNe
  have hAll := schedulerLocalTransport (lo := 8444) (len := 2) hFallthrough (fun hlo hhi =>
    rescaleCountCore hlo (by omega)) hs ht.1.ge (show t.pc + 2 ≤ 8444 + 2 by rw [ht.1])
  have hFrame := holdsSchedulerFrame ht.2.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWrite hFallthrough hs ht.1.ge (by rw [ht.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At s 8446 (((7278,remainingRescaleWord (blocks-1))::F)) :=
    hS.mono ⟨hS.2.2.2.2.2.1, hFrame⟩
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := thread)
    Flow.code_8446 (decide (2 < blocks)) hAt hS.2.2.2.2.1 (by simp)
  have hModel : tauStep kernel Assumptions.all l thread s = tauStep kernel [] l thread s := by
    exact Assumptions.tauStep_all_eq_nil (by rw [hAt.1]; decide) (hAt.1.symm ▸ Flow.code_8446) rfl
  have hvAll : run kernel Assumptions.all l thread 1 s = some v := by
    simpa only [run, hModel] using hv
  exact ⟨v, (run_rtg hAll).trans (run_rtg hvAll),
    by simpa only [decide_eq_true_eq, Nat.reduceAdd] using hV⟩

/-- Both publication inputs for a concrete pair of visits. The second read cursor depends
on the first stage's observed ballot, because a taken rescale emits extra TMEM events. -/
structure RescaleRoundInputs (l : Launch) (X : Execution) (g : Nat) (pos : Nat → Nat)
    (alpha : Fin 2 → Nat → ℝ) (old : Fin 2 → Nat → Fin 8 → Nat → ℝ) : Prop where
  bound : ∀ stage, ∀ lane < 32, alpha stage lane ≤ 1
  first : ∀ lane < 32, RescaleVisitInputs l X (warpLane l g lane) (pos lane) 0
    (alpha 0 lane) (old 0 lane)
  second : ∀ (word : Nat → BitVec 32),
    (∀ lane < 32, RescaleVisit l X (warpLane l g lane) (pos lane)
      0 (alpha 0 lane) (old 0 lane) (word lane)) →
    ∀ lane < 32, RescaleVisitInputs l X (warpLane l g lane)
      (pos lane + 3 + rescaleBodyEvents (word lane) + 2) 1 (alpha 1 lane) (old 1 lane)

end
end PTX.Kernels.TmlFa4Fwd.Correction

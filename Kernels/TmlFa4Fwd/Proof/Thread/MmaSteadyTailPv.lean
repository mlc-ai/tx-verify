-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailEntry
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalPvProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheBroadcasts
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondScoreIssue
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
import Kernels.TmlFa4Fwd.Flow.Code.Part040

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

def steadyTerminalPvFrame (l : Launch) (visit : Nat) : List (Nat × Value) :=
  [(2612,b32 (valueDescriptorLow l (2*visit+1))),(2615,b32 (l.sharedBase+104)),
   (2618,b32 (l.sharedBase+120)),(7205,b32 (visit%2)),(7206,b32 (if 0<visit then 1 else 0)),
   (1194,b32 (l.sharedBase+8*(readyStage (2*visit+1)).val)),
   (2535,b32 l.sharedBase),(6495,b32 (l.sharedBase+144))]

private def firstTailSteadyDescriptors (l : Launch) (visit : Nat) : List (Nat × Value) :=
  [(2626,b32 64),(2625,b32 (valueDescriptorLow l (2*visit+1))),
    (6495,b32 (l.sharedBase+144))] ++ steadyTailValueFrame l visit

private theorem firstTailSteadyDescriptorSetup {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) {visit : Nat} {t : TState}
    (ht : At t 2551 ((6495,b32 (l.sharedBase+144))::steadyTailValueFrame l visit)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2558 (firstTailSteadyDescriptors l visit) := by
  have ht' : At t 2551 [(7207,b32 (kvSlot (2*visit+1))),(2535,b32 l.sharedBase)] :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl,holds_lookup ht.2.2.2.2 rfl,trivial⟩
  obtain ⟨u,hr,hu⟩ := valueDescriptorLocalWithProbabilityFrame hp g false (2*visit+1) none t ht'
  obtain ⟨hPath,hKeep⟩ := activeDrainLocalKeep ht (by decide) (by decide) (by
    change ((kernel.code.drop 2551).take 7).all
      (fun ins => [6495,2609,1194,7207,7208,7205,7206,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hr
  exact ⟨u,hPath,hu.mono ⟨hu.2.2.2.2.1,hu.2.2.2.2.2.1,hKeep⟩⟩

private theorem steadyTerminalRegisters (l : Launch) (visit : Nat) :
    (steadyTerminalPvFrame l visit).map Prod.fst = (terminalPvFrame l).map Prod.fst := by
  simp only [steadyTerminalPvFrame,terminalPvFrame,List.map_cons,List.map_nil]

private theorem steadyTerminalExtra (l : Launch) (visit : Nat) (which : Fin 2) :
    let block : Fin 4 := if which = 0 then 2 else 3
    ∀ pair ∈ steadyTerminalPvFrame l visit, pair.1 ≠ (pvSite block).b-2 ∧
      pair.1 ≠ (pvSite block).b ∧ pair.1 ≠ (waitSite (pvTailWait block)).result := by
  intro block pair hPair
  have hOld := terminalPvExtra l which
  have hMem := List.mem_map_of_mem (f := Prod.fst) hPair
  rw [steadyTerminalRegisters] at hMem
  obtain ⟨old,hOldMem,hEq⟩ := List.mem_map.mp hMem
  rw [← hEq]
  exact hOld old hOldMem

end
end PTX.Kernels.TmlFa4Fwd.Mma

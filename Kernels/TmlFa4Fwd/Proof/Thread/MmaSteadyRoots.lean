-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQRegisters

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

/-- The immutable launch and score ABI carried across every full QK/PV visit. -/
def steadyQkScalars (l : Launch) : List (Nat × Value) :=
  [(1062,b32 12),(2574,b32 0),(2602,b32 128),(9632,b32 0x8200490),
    (1188,b32 (l.sharedBase+80))]

/-- A complete visit restores both Q banks to the same phase for the next visit. -/
def steadyIterationRoots (l : Launch) : List (Nat × Value) :=
  steadyQkScalars l ++ qDescriptorFacts l 1

def steadyIterationRootRegs : List Nat :=
  [1062,2574,2602,9632,1188,9624,9625,9626,9627,9628,9629,9630,9631]

theorem steadyIterationRoots_regs (l : Launch) :
    (steadyIterationRoots l).map Prod.fst = steadyIterationRootRegs := by
  simp only [steadyIterationRoots,steadyQkScalars,qDescriptorFacts,steadyIterationRootRegs,
    List.map_append,List.map_map,List.map_cons,List.map_nil]
  rfl

/-- An instruction audit on a register superset applies to a retained subframe. -/
theorem knownRegisterFrameAudit {code : List Instr} {F : List (Nat × Value)} {regs : List Nat}
    (hFrame : ∀ pair ∈ F, pair.1 ∈ regs)
    (hAudit : code.all (fun ins => regs.all fun r => !(writesRegs ins.op).contains r) = true) :
    code.all (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true := by
  apply List.all_eq_true.mpr
  intro ins hi
  apply List.all_eq_true.mpr
  intro r hr
  obtain ⟨p,hP,rfl⟩ := List.mem_map.mp hr
  exact List.all_eq_true.mp (List.all_eq_true.mp hAudit ins hi) _ (hFrame p hP)

theorem steadyIterationRoots_valid (l : Launch) (pair : Nat × Value)
    (h : pair ∈ steadyIterationRoots l) : pair.1 ∈ steadyIterationRootRegs := by
  rw [← steadyIterationRoots_regs l]
  exact List.mem_map_of_mem (f := Prod.fst) h

end PTX.Kernels.TmlFa4Fwd.Mma

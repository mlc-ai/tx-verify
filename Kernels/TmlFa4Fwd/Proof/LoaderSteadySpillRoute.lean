-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandSave
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part025

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The two-spill loop joins the packet's straight-line setup. -/
def steadySpillExit (value : Bool) : Nat := pointerSavePc (steadySpillSite value) + 4

def steadySpillSentinel (value : Bool) : Nat := if value then 780 else 779

def steadySpillNext (value more : Bool) : Nat :=
  if more then steadySpillFirst value - 1 else steadySpillExit value

set_option maxRecDepth 100000 in
/-- A live steady lane either prepares the upper pointer slot or enters the packet setup. -/
theorem steadySpillRoute {l : Launch} {g : Nat} {s : TState} {F : List (Nat × Value)}
    (value more : Bool)
    (hFrame : ∀ operand : Bool,
      ((kernel.code.drop (pointerSavePc (steadySpillSite operand) + 1)).take 3).all
        (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hs : At s (pointerSavePc (steadySpillSite value) + 1)
      ((steadySpillPred value, .pred more) :: F)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      At u (steadySpillNext value more)
        ([((recurringSaveInputs (steadySpillSite value)).slot, b64 1),
          (steadySpillSentinel value, .pred false)] ++ F) := by
  let start := pointerSavePc (steadySpillSite value) + 1
  let slotReg := (recurringSaveInputs (steadySpillSite value)).slot
  let extra := [(slotReg, b64 1), (steadySpillSentinel value, .pred false)]
  have hCore : Seg kernel [] l g 3 start [(steadySpillPred value, .pred more)]
      (steadySpillNext value more) extra := by
    cases value <;> cases more <;> intro t ht <;>
      simp only [start, steadySpillPred, steadySpillSite, steadySpillNext, steadySpillFirst,
        steadySpillExit, steadySpillSentinel, extra, slotReg, recurringSaveInputs, pointerSavePc,
        recurringScratchWord, Bool.false_eq_true, ↓reduceIte] at ht ⊢ <;> seg_fp ht using rfl
  obtain ⟨u, hu, hU⟩ := hCore s (hs.mono ⟨hs.2.2.2.2.1, trivial⟩)
  obtain ⟨huA, huF⟩ := loaderLinear (regs := F.map Prod.fst)
    (by cases value <;> decide) (by cases value <;> decide) hs.1
    (hFrame value) (by cases value <;> kernel_rfl) hu
  exact ⟨u, huA, hU.mono ((holds_append ..).mpr ⟨hU.2.2.2.2,
    holdsSchedulerFrame hs.2.2.2.2.2 huF (fun _ hm => List.mem_map_of_mem hm)⟩)⟩

set_option maxRecDepth 100000 in
/-- The actual lower-slot return re-enters the scratch read with slot one. -/
theorem steadySpillSecond {l : Launch} {g : Nat} {s : TState} {F : List (Nat × Value)}
    (value : Bool)
    (hFrame : ∀ operand : Bool, ((kernel.code.drop (steadySpillFirst operand - 1)).take 1).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hs : At s (steadySpillNext value true)
      ([((recurringSaveInputs (steadySpillSite value)).slot, b64 1),
        (steadySpillSentinel value, .pred false)] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 1 s = some u ∧
      At u (steadySpillFirst value) (steadySpillFacts value 1 false ++ F) := by
  let start := steadySpillFirst value - 1
  let slotReg := (recurringSaveInputs (steadySpillSite value)).slot
  have hCore : Seg kernel [] l g 1 start [(steadySpillSentinel value, .pred false)]
      (steadySpillFirst value) [(steadySpillPred value, .pred false)] := by
    cases value
    · intro t ht
      let u := next (setReg t 12 (.pred false))
      refine ⟨u, ?_, (ht.mono (G := []) trivial).set (by simp)⟩
      have hReg : t.regs 779 = some (.pred false) := ht.2.2.2.2.1
      refine run_local Flow.code_1435 rfl ht ?_
      rw [execLocalA_nil]
      simp [execLocal, Op.rule, MoveInstr.rule, execMove, readPred, readReg,
        hReg, u, bind, Except.bind, pure, Except.pure]
    · intro t ht
      let u := next (setReg t 13 (.pred false))
      refine ⟨u, ?_, (ht.mono (G := []) trivial).set (by simp)⟩
      have hReg : t.regs 780 = some (.pred false) := ht.2.2.2.2.1
      refine run_local Flow.code_1616 rfl ht ?_
      rw [execLocalA_nil]
      simp [execLocal, Op.rule, MoveInstr.rule, execMove, readPred, readReg,
        hReg, u, bind, Except.bind, pure, Except.pure]
  obtain ⟨u, hu, hU⟩ := hCore s (hs.mono ⟨hs.2.2.2.2.2.1, trivial⟩)
  have hAudit : ((kernel.code.drop start).take 1).all
      (fun ins => (slotReg :: F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) =
        true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hSlot : ((kernel.code.drop start).take 1).all
        (fun ins => !(writesRegs ins.op).contains slotReg) = true := by cases value <;> kernel_rfl
    exact Bool.and_eq_true_iff.mpr
      ⟨List.all_eq_true.mp hSlot _ hm, List.all_eq_true.mp (hFrame value) _ hm⟩
  obtain ⟨huA, huF⟩ := loaderLinear (regs := slotReg :: F.map Prod.fst)
    (by cases value <;> decide) (by cases value <;> decide) hs.1 hAudit rfl hu
  exact ⟨u, huA, hU.mono ⟨(huF slotReg (by simp)).trans hs.2.2.2.2.1, hU.2.2.2.2.1,
    holdsSchedulerFrame hs.2.2.2.2.2.2 huF
      (fun _ hm => .tail slotReg (List.mem_map_of_mem hm))⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader

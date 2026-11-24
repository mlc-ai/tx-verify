-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyProbabilityColumn
import Lemmas.Order.WaitOrderEnables

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.TcMma
open PTX.Kernels.TmlFa4Fwd.Mma (pvOperands pvSite pvFragment kvStart sharedDescriptor)

/-- The latest successful V ready identifies the canonical PV operand pair. -/
theorem PvInstruction.operandsOfLatestValueReadyUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index d use : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec}
    {accum : Bool} {mask : List Nat}
    (hPv : PvInstruction X (g,index) block step d op accum mask)
    (hUse : Mma.LatestValueReadyUse l X g index use) :
    op = pvOperands l g block step use := by
  obtain ⟨actual,hActual,hB,hShape⟩ := Mma.valueFragmentUse hp hX hPv
  rw [hActual.unique hUse] at hB
  obtain ⟨hDesc,hLow,hHigh⟩ := hShape
  obtain ⟨hA,hCollector,_⟩ := hPv.fixedOperandFields hX
  have hTmem := hPv.probabilityAddress hp hX
  cases op with
  | mk desc a b lo hi tmem collector =>
    dsimp only at hDesc hB hA hLow hHigh hTmem hCollector ⊢
    subst desc a b lo hi tmem collector
    rfl

/-- A preceding PV on the same uninterrupted fragment run has the same V ready. -/
theorem Mma.LatestValueReadyUse.beforeFragment {l : Launch} {X : Execution}
    {g index prior use d : Nat} {block : Fin 4} {step : Fin 8}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hUse : Mma.LatestValueReadyUse l X g index use)
    (hPrior : PvInstruction X (g,prior) block step d op accum mask) (hLt : prior < index)
    (hNoReady : ∀ {j slot parity}, prior < j → j < index →
      ¬ Mma.ReadyPoll l X g j slot parity true .cta) :
    Mma.LatestValueReadyUse l X g prior use := by
  obtain ⟨wait,hPoll,hRank,hOdd,hBefore,hOnly⟩ := hUse
  have hWait : wait < prior := by
    rcases lt_trichotomy wait prior with h | rfl | h
    · exact h
    · obtain ⟨e,he,hKind⟩ := hPoll
      have hEq := Option.some.inj (he.symm.trans hPrior.decoded)
      cases hEq
      cases hKind
    · exact (hNoReady h hBefore.2.1 hPoll).elim
  exact ⟨wait,hPoll,hRank,hOdd,⟨rfl,hWait,len_of_get hPrior.decoded⟩,
    fun j slot parity hj hk => hOnly j slot parity hj (hk.trans hLt)⟩

end PTX.Kernels.TmlFa4Fwd.Thread

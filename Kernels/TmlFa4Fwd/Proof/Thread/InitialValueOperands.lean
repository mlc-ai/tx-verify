-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueRoute
public import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma (initialMmaTrace RoleShape pvSite pvPc pvEnable pvCode
  pvCutCode pvWalkCut pvRoleAfterEvent normalBeforeLaterEvent pvWalkEvent mmaCutStep
  secondOutputCommitLeader electSite pvElection electTemplate electStateFrame sameLeader
  out_eq_core waitSite)
open Mma.Observation (readyObject)

noncomputable section

def firstPvBlock (steady : Bool) (stage : Fin 2) : Fin 4 :=
  ⟨if steady then stage.val else stage.val + 2, by cases steady <;> simp <;> omega⟩

/-- Locate the next observed event in a cut, before the retained later event. -/
theorem nextBeforeRecorded {X : Execution} {g pos later : Nat} {e target : Event}
    {pre tail : List Event} (ht : X.get (g,later) = some target) (hPos : pos ≤ later)
    (hSplit : (X.tr g).drop pos = pre ++ e :: tail)
    (hEarlier : target ∉ pre) (hNe : e ≠ target) :
    let j := pos + pre.length
    X.get (g,j) = some e ∧ j < later ∧ (X.tr g).drop (j + 1) = tail := by
  dsimp only
  have hRest : (X.tr g).drop (pos + pre.length) = e :: tail := by
    rw [← List.drop_drop, hSplit, List.drop_append_length]
  refine ⟨?_, ?_, ?_⟩
  · change (X.tr g)[pos + pre.length]? = some e
    have h : ((X.tr g).drop (pos + pre.length))[0]? = some e := by rw [hRest]; rfl
    simpa only [List.getElem?_drop, Nat.zero_add, Nat.add_zero] using h
  · have hLookup : ((X.tr g).drop pos)[later - pos]? = some target := by
      rwa [List.getElem?_drop, Nat.add_sub_of_le hPos]
    by_contra! h
    rcases Nat.lt_or_eq_of_le h with hLt | hEq
    · rw [hSplit, List.getElem?_append_left (by omega)] at hLookup
      exact hEarlier (List.mem_of_getElem? hLookup)
    · have hEqual : later = pos + pre.length := hEq
      have hTarget : ((X.tr g).drop (pos + pre.length))[0]? = some target := by
        rwa [List.getElem?_drop, Nat.add_zero, ← hEqual]
      rw [hRest] at hTarget
      exact hNe (Option.some.inj hTarget)
  · rw [← List.drop_drop, hRest]
    rfl

/-- A PV issue at its decoded stage and fragment, on the selected initial V route. -/
def InitialValueFragment (X : Execution) (issue : EvId) (steady : Bool)
    (stage : Fin 2) (fragment : Fin 8) (dst : Nat) (op : TcMma.OperandSpec)
    (accum : Bool) (mask : List Nat) : Prop :=
  X.get issue = some ⟨pvPc (firstPvBlock steady stage) fragment, .tc (.mma dst op accum mask)⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread

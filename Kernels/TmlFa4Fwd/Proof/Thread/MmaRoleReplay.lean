-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
public import Lemmas.Flow.WarpUniform
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

set_option maxRecDepth 100000 in
private theorem afterRoleFloor :
    (kernel.code.drop 2768).all (fun i => staysPastEvent 2768 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterRoleSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2768 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

/-- A frame proven on returning MMA-role steps holds at the physical source of the specified
trace record. The replay uses its exact prefix index, even when the same event repeats. -/
theorem mmaRoleReplayAt {l : Launch} {X : Execution} {g : Nat}
    (Inv : Nat → TState → Prop)
    (hStep : ∀ {s u : TState} {ev : Option Event} {pos : Nat},
      1907 ≤ s.pc → s.pc < 2768 →
      (RoleShape s ∧ s.regs 1062 = some (b32 12)) → Inv pos s →
      WStep kernel Assumptions.all l g s ev u →
      (∀ e, ev = some e → X.get (g,pos) = some e) → Inv (pos+ev.toList.length) u)
    {s : TState} {base : Nat} {visits : List Visit}
    (hBounds : 1907 ≤ s.pc ∧ s.pc < 2768)
    (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hInit : Inv base s)
    (hw : Walk kernel Assumptions.all l g s ((X.tr g).drop base) visits)
    {index : Nat} {e : Event} (hBase : base ≤ index) (he : X.get (g,index) = some e)
    (hEarly : e.pc < 2768) :
    ∃ t u, Inv index t ∧ EStep kernel Assumptions.all l g t e u := by
  generalize hz : (X.tr g).drop base = events at hw
  have hGet : events[index-base]? = some e := by
    rw [← hz,List.getElem?_drop,Nat.add_sub_of_le hBase]
    exact he
  clear he
  generalize hRemaining : index-base = remaining at hGet
  have hIndex : base+remaining = index := by rw [← hRemaining]; omega
  clear hBase
  clear hRemaining
  subst index
  induction hw generalizing base remaining with
  | stop => simp at hGet
  | @tau s u events visits ht hw ih =>
    have hFrame := hStep (pos := base) hBounds.1 hBounds.2 hShape hInit (.inl ⟨rfl,ht⟩)
      (fun _ h => by cases h)
    obtain ⟨hNew,hShape⟩ := mmaCutStep hBounds.1 hBounds.2 (.inl ⟨rfl,ht⟩) hShape
    rcases hNew with hIn | ⟨hExit,_⟩
    · exact ih hIn hShape hFrame hz remaining hGet
    · simp only [List.mem_singleton] at hExit
      exact (Nat.not_le_of_lt hEarly (eventTailEvents afterRoleFloor afterRoleSegments
        hw (by omega) e (List.mem_of_getElem? hGet))).elim
  | @ev s u first events visits hf hw ih =>
    cases remaining with
    | zero =>
      obtain rfl := Option.some.inj hGet
      exact ⟨s,some u,hInit,hf⟩
    | succ remaining =>
      have hActual : X.get (g,base) = some first := by
        change (X.tr g)[base]? = _
        rw [← Nat.add_zero base,← List.getElem?_drop,hz,List.getElem?_cons_zero]
      have hFrame := hStep (pos := base) hBounds.1 hBounds.2 hShape hInit (.inr ⟨first,rfl,hf⟩)
        (fun _ h => Option.some.inj h ▸ hActual)
      obtain ⟨hNew,hShape⟩ := mmaCutStep hBounds.1 hBounds.2 (.inr ⟨first,rfl,hf⟩) hShape
      rcases hNew with hIn | ⟨hExit,_⟩
      · have hDrop : (X.tr g).drop (base+1) = events := by
          rw [← List.drop_drop,hz]
          rfl
        rw [show base+(remaining+1) = base+1+remaining by omega]
        exact ih hIn hShape hFrame hDrop remaining hGet
      · simp only [List.mem_singleton] at hExit
        exact (Nat.not_le_of_lt hEarly (eventTailEvents afterRoleFloor afterRoleSegments
          hw (by omega) e (List.mem_of_getElem? (show events[remaining]? = some e from hGet)))).elim
  | @last s first hf =>
    obtain rfl := List.mem_singleton.mp (List.mem_of_getElem? hGet)
    cases remaining with
    | zero => exact ⟨s,none,hInit,hf⟩
    | succ _ => simp at hGet

end PTX.Kernels.TmlFa4Fwd.Thread

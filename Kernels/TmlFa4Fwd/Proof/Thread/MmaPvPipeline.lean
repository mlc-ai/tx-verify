-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
public import Core.Tc.TcPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Lemmas.Flow.ElectActor
import Lemmas.Order.OrderBaseCausality
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The CTA's stable full-warp election makes all its tensor MMA instructions single-issuer. -/
theorem mmaIssueSameThread {i j : EvId} {d d' : Nat} {op op' : TcMma.OperandSpec}
    {acc accum' : Bool} {mask mask' : List Nat} (hi : X.MmaIssue i d op acc mask)
    (hj : X.MmaIssue j d' op' accum' mask') (hCta : i.1/l.block = j.1/l.block) : i.1 = j.1 := by
  obtain ⟨hw,rank,_,_,_,he,hLane⟩ := mmaIssueElection hp hX hi
  obtain ⟨hw',rank',_,_,_,he',hLane'⟩ := mmaIssueElection hp hX hj
  obtain ⟨_,hi⟩ := hi
  obtain ⟨_,hj⟩ := hj
  have hSame : SameWarp l i.1 j.1 :=
    ⟨⟨event_thread_lt hX hi,event_thread_lt hX hj,hCta⟩,hw.trans hw'.symm⟩
  exact selected_elect_thread_unique hX.elect (e := (i.1,rank)) (f := (j.1,rank'))
    he he' hSame hLane hLane'

/-- Distinct MMA issues that target the same accumulator are pipeline-ordered within a CTA. -/
theorem mmaDestinationPipeline {i j : EvId} {d d' : Nat} {op op' : TcMma.OperandSpec}
    {acc accum' : Bool} {mask mask' : List Nat} (hi : X.MmaIssue i d op acc mask)
    (hj : X.MmaIssue j d' op' accum' mask') (hCta : i.1/l.block = j.1/l.block) (hNe : i ≠ j)
    (hAcc : TcMma.SameAccumulator d op d' op') :
    TcMma.Pipelined l X .dWrite i .dWrite j ∨ TcMma.Pipelined l X .dWrite j .dWrite i := by
  have hLane := mmaIssueSameThread hp hX hi hj hCta
  obtain ⟨site,hiGet⟩ := hi
  obtain ⟨site',hjGet⟩ := hj
  have hWarp : SameWarp l i.1 j.1 :=
    ⟨⟨event_thread_lt hX hiGet,event_thread_lt hX hjGet,hCta⟩,by rw [hLane]⟩
  rcases lt_trichotomy i.2 j.2 with hLt | hEq | hLt
  · have ho := po_of_not_access hLane hLt (len_of_get hjGet) (by rw [hjGet]; rfl)
    exact .inl ⟨hWarp,.inl (.single (.inl ho)),d,op,acc,mask,d',op',accum',mask',
      ⟨site,hiGet⟩,⟨site',hjGet⟩,hAcc⟩
  · exact (hNe (Prod.ext hLane hEq)).elim
  · have ho := po_of_not_access hLane.symm hLt (len_of_get hiGet) (by rw [hiGet]; rfl)
    have hWarp' : SameWarp l j.1 i.1 :=
      ⟨⟨event_thread_lt hX hjGet,event_thread_lt hX hiGet,hCta.symm⟩,by rw [hLane]⟩
    obtain ⟨hd,hm,hn,hLo,hHi⟩ := hAcc
    exact .inr ⟨hWarp',.inl (.single (.inl ho)),d',op',accum',mask',d,op,acc,mask,
      ⟨site',hjGet⟩,⟨site,hiGet⟩,hd.symm,hm.symm,hn.symm,hLo.symm,hHi.symm⟩

end PTX.Kernels.TmlFa4Fwd.Thread

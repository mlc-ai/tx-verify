-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
public import Lemmas.Tmem.AccessCp
public import Lemmas.Flow.Regs
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DeallocSite
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Observe
import Kernels.InklingRelDecode.Proof.Common.Export.EpiPoll
import Kernels.InklingRelDecode.Proof.Mma.Export.CommitOrder
import Kernels.InklingRelDecode.Proof.Mma.Export.FinalCount
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Handoff
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
public import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
import Lemmas.Protocol.ObservedSync
import Lemmas.Protocol.UnitNotifyWait
import Lemmas.Protocol.ClusterTrace
import Lemmas.Tcgen05.TcProgramOrder

/-! # Every MMA is done before every deallocation of its CTA

The deallocation's lane polled `o_final` successfully (pc 2565) before it. The poll observes the
CTA's one final commit (pc 2553, by the MMA warp's leader), which tracks every MMA of the lane
before it; the lane's MMAs are before the commit since the lane, which reached its final
rendezvous after the MMA, issued the commit after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Frame PTX.Sched PTX.MbarRing PTX.AsyncCopy PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}


/-- **A successful poll of `o_final` observes the final commit of the CTA's MMA leader.** -/
public theorem poll_observes (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {h jw l q ac sc}
    (hpoll : X.get (h,jw) = some ⟨2565,.wait l q true ac sc⟩) :
    ∃ ic spi rank, X.get (Protocol.KV.leader L X (h / L.block) 7, ic) =
        some ⟨2553,.tc (.commit spi)⟩ ∧
      TcCommit.target spi rank = some (Protocol.OFinal.obj L (h / L.block)) ∧
      rank ∈ X.tcNotified (Protocol.KV.leader L X (h / L.block) 7, ic) ∧
      AsyncCopy.WaitObserves X (.async (Protocol.KV.leader L X (h / L.block) 7, ic)
        (.tcNotify rank)) (h,jw) (Protocol.OFinal.obj L (h / L.block)) true .cta := by
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Protocol.OFinal.final_wait rows (lt_of_get hX hpoll) hpoll
  have hq := Protocol.OFinal.wait_first hp hX hf rows hpoll
  have o := Protocol.OFinal.history (c := h / L.block) hp hX hf rows init
  obtain ⟨ic,pc',sp,rank,hget,hm,ht,-,wit⟩ := o.observes_witness hX
    (Protocol.OFinal.final_reach (h := h) hp hX hf rows init) hpoll (u := 0) hq
  obtain ⟨hrank,hwo⟩ := Witness.waitObserves_tcNotify wit hpoll
  obtain ⟨rfl,-,-,-⟩ := Protocol.OFinal.commit_info rows (lt_of_get hX hget) hget ht
  exact ⟨ic,sp,rank,hget,ht,hrank,hwo⟩


/-- **The MMA's issue pc is one of the sixteen.** -/
private theorem issue_pc {pc : Nat}
    (h : (∃ j : Fin 8, pc = Lib.qkIssue j) ∨ ∃ j : Fin 8, pc = Lib.pvIssue j) :
    pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498,2530,2533,2535,2537,2539,2541,2543,2545] := by
  rcases h with ⟨j,h⟩ | ⟨j,h⟩ <;> subst h <;> fin_cases j <;> decide

/-- **An MMA is done before every event that follows a successful poll of `o_final` of its CTA.**
The poll observes the CTA's final commit, which follows every MMA of the lane. -/
public theorem mma_done_final (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    {y0 i0 pc0 dd sp acc mask} (he : X.get (y0,i0) = some ⟨pc0,.tc (.mma dd sp acc mask)⟩)
    (shape : (∃ j : Fin 8, pc0 = Lib.qkIssue j) ∨ ∃ j : Fin 8, pc0 = Lib.pvIssue j)
    {h jw l q ac sc} (hpoll : X.get (h,jw) = some ⟨2565,.wait l q true ac sc⟩)
    (hc : h / L.block = y0 / L.block) {e : EvId} (po : baseCausality L X (h,jw) e) :
    DoneBefore L X (y0,i0) e := by
  have issue := issue_pc shape
  obtain ⟨lead,-⟩ := mma_leader hp hX hf he
  have hg : y0 < L.threads := lt_of_get hX he
  obtain ⟨ic,spi,rank,hgc,hti,hrk,hobs⟩ := poll_observes hp hX hf rows init hpoll
  rw [hc, lead] at hgc hrk hobs
  rw [hc] at hti
  have hj := Mma.Export.mma_before_final hp hX hf (fun h => Protocol.Shared.role_bytes hp hX h)
    hgc he issue
  have htr : TracksMma X (y0,i0) (y0,ic) := ⟨rfl,hj,.inl ⟨dd,sp,acc,mask,pc0,he⟩,spi,2553,hgc⟩
  refine .inl ⟨(h,jw),.cta,⟨_,_,⟨(y0,ic),spi,rank,rfl,htr,⟨2553,hgc⟩,hti,hrk⟩,hobs⟩,?_,po⟩
  have hh' : h < L.threads := lt_of_get hX hpoll
  refine ⟨⟨hg,hh',?_⟩,hh',hg,hc⟩
  show L.clusterOfCta (y0 / L.block) = L.clusterOfCta (h / L.block)
  rw [hc]

/-- **`AsyncDoneDealloc`**: every MMA is done before every deallocation of its CTA. -/
public theorem async_done (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) :
    Tmem.AccessCp.AsyncDoneDealloc L X := by
  intro i d pc a n grp dst hi hd hc
  obtain ⟨y0,i0⟩ := i
  obtain ⟨h,kd⟩ := d
  obtain ⟨dd,sp,acc,mask,pc0,he⟩ : ∃ dd sp acc mask pc0,
      X.get (y0,i0) = some ⟨pc0,.tc (.mma dd sp acc mask)⟩ := by
    rcases hi with ⟨dd,sp,acc,mask,pc0,he⟩ | ⟨c,hc'⟩
    · exact ⟨dd,sp,acc,mask,pc0,he⟩
    · exact (Lib.no_cp hX _ c hc').elim
  obtain ⟨lh,pc2851,u',pch,hu',hh,fh,ord⟩ := dealloc_site hp hX hf base hd
  have len : kd < (X.tr h).length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨-,-,-,b,hcol⟩ := Mma.Export.columns hp hX hf base he
  subst pc2851
  obtain ⟨jw,l,q,ac,sc,hjw,hpoll⟩ := Export.epilogue_event_poll hp hX hf hd (fun _ => nofun)
    (by omega) (by omega)
  exact mma_done_final hp hX hf rows init he (by
      rcases hcol with ⟨j,h,-⟩ | ⟨j,h,-⟩
      · exact .inl ⟨j,h⟩
      · exact .inr ⟨j,h⟩) hpoll hc
    (.single (.inl (po_of_source_not_access rfl hjw len (by rw [hpoll]; rfl))))

end PTX.Kernels.InklingRelDecode.Proof.Tmem

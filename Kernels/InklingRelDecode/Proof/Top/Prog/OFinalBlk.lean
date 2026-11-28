-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
public import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Observe
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Lag
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Lemmas.Protocol.NotifyBlocker
import Lemmas.Protocol.UnitReachBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal
open PTX PTX.Flow PTX.Sched PTX.MbarRing MbarRow

theorem wait_blk {Q L m X g l q sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hu : ¬HasUb X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (init : Mbar.InitRows L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨2565,.wait l q false true sc⟩) :
    WaitBlk (schedule Q L) X g l q := by
  obtain ⟨Y,hY,pref,get⟩ := hn
  obtain ⟨rfl,rfl,-,-⟩ := final_wait (rows Y hY) (Frame.lt_of_get hY get) get
  have hn : NextEv L kernel Assumptions.all m X g _ := ⟨Y,hY,pref,get⟩
  let c := g/L.block
  have hg := hn.lt
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  have hf := followed X hX
  have hz := wait_first hp hY (followed Y hY) (rows Y hY) get
  rw [pref] at hz
  change okPolls (obj L c) (X.tr g)=0 at hz
  have o := history (c := c) hp hX hf (rows X hX) init
  have live := Mbar.next_published hp hX hn (by decide) (11 : Fin 12)
  obtain ⟨st,hst⟩ := Unit.final_of_init hX o.init o.noInval live
  refine ⟨st,hst,fun parity => ?_⟩
  have reach := final_reach (c := c) (h := g) hp hX hf (rows X hX) init
  obtain ⟨phase,short | missing⟩ := o.blocker hX reach (fault_free hp hX hf (rows X hX) init)
    (fun he addr => ⟨0,target_zero hp hX hf he addr⟩) hst (by rw [hz]; exact parity)
    (Nat.zero_le _)
  · obtain ⟨_,clock⟩ := lag hp hX followed rows (.of_noUb hu) hc
    have hy := KV.leader_warp (X := X) hp hc (by decide : 7<8)
    exact clock.blk hX hu hg ⟨sc,hn⟩ (poll_floor hp hf (by decide) hn).1 rfl hy.1
      (congrArg L.clusterOfCta hy.2.1) (by omega)
  · exact .inl ⟨.commit,.inl rfl,missing⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal

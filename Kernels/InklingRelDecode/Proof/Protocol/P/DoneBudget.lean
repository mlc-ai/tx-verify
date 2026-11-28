-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarHistory
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Mma.Export.DoneCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.Coll
import Kernels.InklingRelDecode.Proof.Lib.ShuffleCredit
import Kernels.InklingRelDecode.Proof.Lib.IssueCount
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
import Lemmas.Protocol.NotifyBlocker
import Lemmas.Protocol.PollLe

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.P
open PTX PTX.Flow PTX.Sched PTX.MbarRing Scalar

/-- A done commit of the elected lane is the notification at the PV site. -/
theorem done_receipt {Q L m X c y k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (followed : Follow Q L X)
    (rows : MbarRows Q L X) (hy : y<L.threads) (atK : (X.tr y)[k]?=some e)
    (kind : commitsTo (Object.done.loc L c) e) :
    ∃ sp, X.get (y,k)=some ⟨2548,.tc (.commit sp)⟩ := by
  obtain ⟨sp,kd,addr⟩ := Notify.commit_of_commitsTo kind
  obtain ⟨pc,knd⟩ := e
  cases kd
  have target := OFinal.target_zero hp hX followed atK addr
  obtain ⟨_,use⟩ := uses rows hy atK ⟨0,target⟩
  cases use with
  | init bad => cases bad
  | doneWait _ _ h => obtain ⟨_,bad⟩ := h; cases bad
  | doneCommit pc _ _ => cases pc; exact ⟨_,atK⟩

/-- A peer waiting for probabilities still owes the broadcast for its next PV round.
The elected lane can have committed at most one output per completed PV broadcast. -/
theorem done_count {Q L m X c g s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (words : RoleBytes L X) (wait : Waiting L m X (.prob s) c g) :
    (X.tr (KV.leader L X c 7)).countP (commitsTo (Object.done.loc L c))≤
      pollRound 2510 (X.tr g) := by
  obtain ⟨q,sc,hn⟩ := wait
  have hg := hn.lt
  obtain ⟨Y,hY,pre,event⟩ := id hn
  obtain ⟨cta,use⟩ := uses (rows Y hY) hg event rfl
  have warp : g%L.block/32=7 := by
    cases use with
    | init bad | probArrive _ _ bad => cases bad
    | probWait _ hw _ => exact hw
  have hc : c<L.grid := cta ▸ Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  let y := KV.leader L X c 7
  have hw : SameWarp L g y := ⟨⟨hg,hy,cta.trans cy.symm⟩,warp.trans wy.symm⟩
  have peer := Mma.Export.poll_shuffles hp hY (followed Y hY) warp event (by simp) (.inr rfl)
  change ((Y.tr g).take _).countP Execution.isShfl =
    1+min (pollRound 2510 ((Y.tr g).take _)+2) (Lib.blocksOf Q L (g/L.block))+
      pollRound 2510 ((Y.tr g).take _) at peer
  rw [pre,cta] at peer
  apply Lib.count_le_tags (fun k => pollRound 2510 ((X.tr y).take k)-1)
  · intro k e atK kind
    obtain ⟨sp,get⟩ := done_receipt hp hX (followed X hX) (rows X hX) hy atK kind
    have ⟨pos,clock⟩ := Mma.Export.done_shuffles (g := y) hp hX (followed X hX) wy get
    have le := Lib.shuffle_credit hX hw hn get
    change y/L.block=c at cy
    rw [cy] at clock
    change ((X.tr y).take k).countP Execution.isShfl≤_ at le
    omega
  · intro k j e f ekh ek ejh ej eq
    obtain ⟨sp,get⟩ := done_receipt hp hX (followed X hX) (rows X hX) hy ekh ek
    obtain ⟨sp',get'⟩ := done_receipt hp hX (followed X hX) (rows X hX) hy ejh ej
    have pos := (Mma.Export.done_shuffles (g := y) hp hX (followed X hX) wy get).1
    have pos' := (Mma.Export.done_shuffles (g := y) hp hX (followed X hX) wy get').1
    exact Mma.Export.done_unique (g := y) hp hX (followed X hX) words wy get get'
      (by change _-1=_-1 at eq; omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.P

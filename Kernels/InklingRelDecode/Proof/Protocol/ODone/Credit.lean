-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.CreditDef
public import Kernels.InklingRelDecode.Proof.Protocol.P.Ahead
public import Kernels.InklingRelDecode.Proof.Protocol.P.DoneBudget
import Kernels.InklingRelDecode.Proof.Mma.Export.DoneCredit
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
import Kernels.InklingRelDecode.Proof.Lib.IssueCount
import Lemmas.Protocol.NotifyBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.ODone
open PTX PTX.Flow PTX.Sched PTX.MbarRing Scalar

/-- A data lane waiting on the output slot has polled all but the last one of the elected
lane's commits: each commit needs its PV polls, and every PV poll needs a publication of lane
zero, which follows the lane's own output poll of the previous round. -/
theorem done_credit {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (init : Mbar.InitRows L X) (words : RoleBytes L X) (safe : ¬Race L X)
    (free : ∀ l, ∀ r ∈ X.objects l, r.fault=none) :
    Credit L m X .done := by
  intro c g wait
  obtain ⟨q,sc,hn⟩ := wait
  have hg := hn.lt
  obtain ⟨Y,hY,pre,get⟩ := id hn
  have get' : Y.get (g,((X.tr g).length))=some
      ⟨2239,.wait (Object.done.loc L c) q false true sc⟩ := get
  obtain ⟨cta,use⟩ := uses (rows Y hY) hg get' rfl
  have lane : g%L.block/32<4 := by
    cases use with
    | init bad => cases bad
    | doneWait _ lane _ => exact lane
    | doneCommit _ _ bad => obtain ⟨_,kd,_⟩ := bad; cases kd
  have hc : c<L.grid := cta ▸ Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  generalize KV.leader L X c 7=y at hy cy wy ⊢
  have count := Scalar.count (rows X hX) hg Object.done (X.tr g).length
  simp only [MbarRow.roundAt,List.take_length,Object.pc] at count
  rw [cta] at count
  apply Lib.count_le_tags (fun k => pollRound 2510 ((X.tr y).take k)-1)
  · intro k e atK kind
    obtain ⟨sp,get⟩ := P.done_receipt hp hX (followed X hX) (rows X hX) hy atK kind
    obtain ⟨pos,_⟩ := Mma.Export.done_shuffles hp hX (followed X hX) wy get
    have ahead := P.peers_ahead (g := g) hp hX (followed X hX) (rows X hX) init safe free get
      (fun _ => nofun) (show Export.afterInit 2548=true by decide) pos (by omega) (by rw [cta,cy])
    have visits : Object.done.visits (pollRound 2239 (X.tr g))=pollRound 2239 (X.tr g) := by
      simp [Object.visits,Object.width,Object.index]
    rw [←count] at visits
    omega
  · intro k j e f ekh ek ejh ej eq
    obtain ⟨sp,get⟩ := P.done_receipt hp hX (followed X hX) (rows X hX) hy ekh ek
    obtain ⟨sp',get'⟩ := P.done_receipt hp hX (followed X hX) (rows X hX) hy ejh ej
    have pos := (Mma.Export.done_shuffles hp hX (followed X hX) wy get).1
    have pos' := (Mma.Export.done_shuffles hp hX (followed X hX) wy get').1
    exact Mma.Export.done_unique hp hX (followed X hX) words wy get get'
      (by change _-1=_-1 at eq; omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.ODone

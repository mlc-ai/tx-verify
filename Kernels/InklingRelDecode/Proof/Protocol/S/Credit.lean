-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.CreditDef
public import Kernels.InklingRelDecode.Proof.Protocol.P.Ahead
import Kernels.InklingRelDecode.Proof.Mma.Export.ScoreCredit
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
import Kernels.InklingRelDecode.Proof.Lib.IssueCount
import Lemmas.Protocol.NotifyBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.S
open PTX PTX.Flow PTX.Sched PTX.MbarRing Scalar

/-- A data lane waiting on a score slot has polled all but the last two scores of the elected
lane's commits to that slot: each commit needs two more PV polls than its ready ordinal has
rounds behind, and every PV poll needs a publication of lane zero. -/
theorem score_credit {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (init : Mbar.InitRows L X) (words : RoleBytes L X) (safe : ¬Race L X)
    (free : ∀ l, ∀ r ∈ X.objects l, r.fault=none) (s : Fin 2) :
    Credit L m X (.score s) := by
  intro c g wait
  obtain ⟨q,sc,hn⟩ := wait
  have hg := hn.lt
  obtain ⟨Y,hY,pre,get⟩ := id hn
  have get' : Y.get (g,((X.tr g).length))=some
      ⟨1257,.wait ((Object.score s).loc L c) q false true sc⟩ := get
  obtain ⟨cta,use⟩ := uses (rows Y hY) hg get' rfl
  have lane : g%L.block/32<4 := by
    cases use with
    | init bad => cases bad
    | scoreWait _ lane _ => exact lane
    | scoreCommit _ _ bad => obtain ⟨_,kd,_⟩ := bad; cases kd
  have hc : c<L.grid := cta ▸ Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  generalize KV.leader L X c 7=y at hy cy wy ⊢
  have count := Scalar.count (rows X hX) hg (Object.score s) (X.tr g).length
  simp only [MbarRow.roundAt,List.take_length,Object.pc] at count
  rw [cta] at count
  have receipt {k e} (atK : (X.tr y)[k]?=some e) (kind : commitsTo ((Object.score s).loc L c) e) :
      ∃ sp, X.get (y,k)=some ⟨2499,.tc (.commit sp)⟩ ∧
        s.val=(pollRound 2462 ((X.tr y).take k)-1)%2 := by
    obtain ⟨sp,kd,addr⟩ := Notify.commit_of_commitsTo kind
    obtain ⟨pc,knd⟩ := e
    cases kd
    have target := OFinal.target_zero hp hX (followed X hX) atK addr
    obtain ⟨_,use⟩ := uses (rows X hX) hy atK ⟨0,target⟩
    cases use with
    | init bad => cases bad
    | scoreWait _ _ h => obtain ⟨_,bad⟩ := h; cases bad
    | scoreCommit pc _ _ => cases pc; exact ⟨_,atK,rfl⟩
  apply Lib.count_le_tags (fun k => (pollRound 2462 ((X.tr y).take k)-1)/2)
  · intro k e atK kind
    obtain ⟨sp,get,slot⟩ := receipt atK kind
    obtain ⟨pos,le,pv⟩ := Mma.Export.score_polls hp hX (followed X hX) wy get
    have visits : (Object.score s).visits (pollRound 1257 (X.tr g))=
        (pollRound 1257 (X.tr g)+2-1-s.val)/2 := rfl
    rw [←count] at visits
    by_cases small : pollRound 2462 ((X.tr y).take k)≤2
    · omega
    · have ahead := P.peers_ahead (g := g) hp hX (followed X hX) (rows X hX) init safe free get
        (fun _ => nofun) (show Export.afterInit 2499=true by decide) (by omega) (by omega)
        (by rw [cta,cy])
      omega
  · intro k j e f ekh ek ejh ej eq
    obtain ⟨sp,get,slot⟩ := receipt ekh ek
    obtain ⟨sp',get',slot'⟩ := receipt ejh ej
    have pos := (Mma.Export.score_polls hp hX (followed X hX) wy get).1
    have pos' := (Mma.Export.score_polls hp hX (followed X hX) wy get').1
    exact Mma.Export.score_unique (g := y) hp hX (followed X hX) words wy get get'
      (by change (_-1)/2=(_-1)/2 at eq; omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.S

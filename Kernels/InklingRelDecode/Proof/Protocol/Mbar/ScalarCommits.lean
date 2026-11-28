-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarHistory
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
import Kernels.InklingRelDecode.Proof.Mma.Export.ScoreCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.DoneCredit
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
import Kernels.InklingRelDecode.Proof.Protocol.P.DoneBudget
import Kernels.InklingRelDecode.Proof.Lib.IssueCount
import Lemmas.Protocol.NotifyBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing MbarRow

theorem take_event {α : Type} {l : List α} {i k : Nat} {e : α} (h : (l.take i)[k]?=some e) :
    k < i ∧ l[k]? = some e := by
  rw [List.getElem?_take] at h
  split at h
  · exact ⟨by assumption,h⟩
  · cases h

theorem score_receipt {Q L m X c s y k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (hy : y<L.threads) (atK : (X.tr y)[k]?=some e)
    (kind : commitsTo ((Object.score s).loc L c) e) :
    ∃ sp, X.get (y,k)=some ⟨2499,.tc (.commit sp)⟩ ∧
      s.val=(pollRound 2462 ((X.tr y).take k)-1)%2 := by
  obtain ⟨sp,kd,addr⟩ := Notify.commit_of_commitsTo kind
  obtain ⟨pc,knd⟩ := e
  cases kd
  have target := OFinal.target_zero hp hX hf atK addr
  obtain ⟨_,use⟩ := uses rows hy atK ⟨0,target⟩
  cases use with
  | init bad => cases bad
  | scoreWait _ _ h => obtain ⟨_,bad⟩ := h; cases bad
  | scoreCommit pc _ _ => cases pc; exact ⟨_,atK,rfl⟩

/-- A score commit has at most as many earlier commits to its slot as the elected lane has
successful probability polls on that slot: each earlier commit is a block two or more behind. -/
theorem score_commits {Q L m X c s y i pc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (words : RoleBytes L X) (hy : y<L.threads) (warp : y%L.block/32=7) (cta : y/L.block=c)
    (get : X.get (y,i)=some ⟨pc,.tc (.commit sp)⟩) (obj : sp.mbar=(Object.score s).loc L c) :
    ((X.tr y).take i).countP (commitsTo ((Object.score s).loc L c))≤
      okPolls ((Object.prob s).loc L c) ((X.tr y).take i) := by
  obtain ⟨_,get2,slot⟩ := score_receipt (c := c) (s := s) hp hX hf rows hy
    get (by simp [commitsTo,obj])
  obtain rfl : pc=2499 := congrArg Event.pc (Option.some.inj (get.symm.trans get2))
  obtain ⟨pos,_,pv⟩ := Mma.Export.score_polls hp hX hf warp get
  dsimp only at slot
  have count := Scalar.count rows hy (Object.prob s) i
  simp only [roundAt,Object.pc,cta] at count
  rw [count,pv]
  have bound : ((X.tr y).take i).countP (commitsTo ((Object.score s).loc L c))≤
      (pollRound 2462 ((X.tr y).take i)-1)/2 := by
    apply Lib.count_le_tags (fun k => (pollRound 2462 (((X.tr y).take i).take k)-1)/2)
    · intro k e atK kind
      obtain ⟨ki,atK'⟩ := take_event atK
      obtain ⟨sp',get',sl⟩ := score_receipt hp hX hf rows hy atK' kind
      obtain ⟨pos',_,_⟩ := Mma.Export.score_polls hp hX hf warp get'
      rw [List.take_take,Nat.min_eq_left ki.le]
      have le := countP_take_mono (okPollAt 2462) (X.tr y) ki.le
      have ne : pollRound 2462 ((X.tr y).take k)≠pollRound 2462 ((X.tr y).take i) := by
        intro eq
        exact absurd (Mma.Export.score_unique hp hX hf words warp get' get eq) (by omega)
      change pollRound 2462 _≤pollRound 2462 _ at le
      omega
    · intro k j e f ekh ek ejh ej eq
      obtain ⟨ki,ek'⟩ := take_event ekh
      obtain ⟨ji,ej'⟩ := take_event ejh
      obtain ⟨_,get1,s1⟩ := score_receipt hp hX hf rows hy ek' ek
      obtain ⟨_,get2,s2⟩ := score_receipt hp hX hf rows hy ej' ej
      obtain ⟨p1,_,_⟩ := Mma.Export.score_polls hp hX hf warp get1
      obtain ⟨p2,_,_⟩ := Mma.Export.score_polls hp hX hf warp get2
      rw [List.take_take,List.take_take,Nat.min_eq_left ki.le,Nat.min_eq_left ji.le] at eq
      exact Mma.Export.score_unique hp hX hf words warp get1 get2 (by omega)
  have : s.val=(pollRound 2462 ((X.tr y).take i)-1)%2 := slot
  change _≤(pollRound 2462 ((X.tr y).take i)-2+2-1-s.val)/2
  omega

/-- A done commit has strictly fewer earlier done commits than the elected lane has PV polls. -/
theorem done_commits {Q L m X c y i pc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (words : RoleBytes L X) (hy : y<L.threads) (warp : y%L.block/32=7)
    (get : X.get (y,i)=some ⟨pc,.tc (.commit sp)⟩) (obj : sp.mbar=Object.done.loc L c) :
    ((X.tr y).take i).countP (commitsTo (Object.done.loc L c))+1≤
      pollRound 2510 ((X.tr y).take i) := by
  obtain ⟨_,get2⟩ := P.done_receipt (c := c) hp hX hf rows hy get (by simp [commitsTo,obj])
  obtain rfl : pc=2548 := congrArg Event.pc (Option.some.inj (get.symm.trans get2))
  obtain ⟨pos,_⟩ := Mma.Export.done_shuffles hp hX hf warp get
  have bound : ((X.tr y).take i).countP (commitsTo (Object.done.loc L c))≤
      pollRound 2510 ((X.tr y).take i)-1 := by
    apply Lib.count_le_tags (fun k => pollRound 2510 (((X.tr y).take i).take k)-1)
    · intro k e atK kind
      obtain ⟨ki,atK'⟩ := take_event atK
      obtain ⟨sp',get'⟩ := P.done_receipt hp hX hf rows hy atK' kind
      obtain ⟨pos',_⟩ := Mma.Export.done_shuffles hp hX hf warp get'
      rw [List.take_take,Nat.min_eq_left ki.le]
      have le := countP_take_mono (okPollAt 2510) (X.tr y) ki.le
      have ne : pollRound 2510 ((X.tr y).take k)≠pollRound 2510 ((X.tr y).take i) := by
        intro eq
        exact absurd (Mma.Export.done_unique hp hX hf words warp get' get eq) (by omega)
      change pollRound 2510 _≤pollRound 2510 _ at le
      omega
    · intro k j e f ekh ek ejh ej eq
      obtain ⟨ki,ek'⟩ := take_event ekh
      obtain ⟨ji,ej'⟩ := take_event ejh
      obtain ⟨_,get1⟩ := P.done_receipt hp hX hf rows hy ek' ek
      obtain ⟨_,get2⟩ := P.done_receipt hp hX hf rows hy ej' ej
      obtain ⟨p1,_⟩ := Mma.Export.done_shuffles hp hX hf warp get1
      obtain ⟨p2,_⟩ := Mma.Export.done_shuffles hp hX hf warp get2
      rw [List.take_take,List.take_take,Nat.min_eq_left ki.le,Nat.min_eq_left ji.le] at eq
      exact Mma.Export.done_unique hp hX hf words warp get1 get2 (by omega)
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar

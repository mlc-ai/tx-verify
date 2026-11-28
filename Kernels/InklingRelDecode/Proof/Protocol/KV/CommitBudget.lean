-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.PollCount
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Mma.Export.EmptyCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Lemmas.Protocol.NotifyBlocker
import Lemmas.Protocol.CountNth

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow MbarRow

theorem slot_of_commit {Q L m X g j p sp c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,j)=some ⟨p,.tc (.commit sp)⟩) (obj : sp.mbar=Ring.empty.obj L c s) :
    p=2546 ∧ g/L.block=c ∧ (pollRound 2510 ((X.tr g).take j)-1)%3=s.val := by
  have warp := Mma.Export.commit_warp hp hX hf he
  obtain ⟨off,rfl,kinds⟩ := Mma.Export.commit hp hX hf warp he
  obtain ⟨_,cta,addr⟩ := Loc.mk.inj obj
  change L.sharedBase+off=L.sharedBase+Iface.kvEmpty s at addr
  have eq := Nat.add_left_cancel addr
  have bound := s.isLt
  rcases kinds with ⟨_,rfl⟩|⟨pc,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
  all_goals simp only [Iface.kvEmpty,Iface.sReady,Iface.oDone,Iface.oFinal] at eq
  all_goals first | exact ⟨pc,cta,by omega⟩ | omega

/-- Each used empty-slot commit spends a distinct earlier ready poll of the same slot. -/
theorem commit_budget {Q L m X g k sp c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨2546,.tc (.commit sp)⟩) (obj : sp.mbar=Ring.empty.obj L c s) :
    ((X.tr g).take k).countP (commitsTo sp.mbar)+1 ≤
      okPolls (Ring.ready.obj L c s) ((X.tr g).take k) := by
  classical
  have warp := Mma.Export.commit_warp hp hX hf he
  obtain ⟨_,rfl,_⟩ := slot_of_commit hp hX hf he obj
  let pv (j : Nat) := pollRound 2510 ((X.tr g).take j)
  let ready (j : Nat) := pollRound 2462 ((X.tr g).take j)
  let l := sp.mbar
  let uses := (Finset.range (k+1)).filter fun j => ((X.tr g)[j]?).any (commitsTo l)
  have info {j : Nat} (hj : j ∈ uses) :
      (∃ a, X.get (g,j)=some ⟨2546,.tc (.commit a)⟩) ∧
      0 < pv j ∧ pv j≤ready k ∧ (pv j-1)%3=s.val := by
    obtain ⟨lt,kind⟩ := Finset.mem_filter.mp hj
    have jk := Finset.mem_range.mp lt
    cases get : (X.tr g)[j]? with
    | none => rw [get] at kind; cases kind
    | some ev =>
      rw [get] at kind
      obtain ⟨a,eq,addr⟩ := MbarRing.Notify.commit_of_commitsTo kind
      obtain ⟨p,kd⟩ := ev
      cases eq
      obtain ⟨rfl,_,slot⟩ := slot_of_commit hp hX hf get (addr.trans obj)
      obtain ⟨pos,spent⟩ := Mma.Export.empty_poll_bounds hp hX hf warp get
      have le := countP_take_mono (okPollAt 2462) (X.tr g) (show j≤k by omega)
      exact ⟨⟨_,get⟩,pos,spent.trans le,slot⟩
  have budget : uses.card ≤ (Finset.range (visits 0 (ready k) s)).card := by
    apply Finset.card_le_card_of_injOn (fun j => (pv j-1)/3)
    · intro j hj
      obtain ⟨_,pos,le,slot⟩ := info hj
      apply Finset.mem_range.mpr
      change (pv j-1)/3 < visits 0 (ready k) s
      unfold visits
      have := s.isLt
      omega
    · intro j hj v hv same
      obtain ⟨⟨_,first⟩,pos,_,slot⟩ := info hj
      obtain ⟨⟨_,last⟩,pos',_,slot'⟩ := info hv
      apply Mma.Export.empty_unique hp hX hf words warp first last
      change pv j=pv v
      change (pv j-1)/3=(pv v-1)/3 at same
      omega
  have cn := MbarRing.Slot.countP_take_card (X.tr g) (commitsTo l) (k+1)
  change _=uses.card at cn
  rw [←cn,countP_take_succ he (by simp [l,commitsTo]),Finset.card_range] at budget
  exact budget.trans_eq (poll_count (r := .ready) rows (Frame.lt_of_get hX he) warp s k).symm

/-- **The empty commits of a prefix spend distinct early ordinals**: those before `k` of
slot `s`, all of ordinal at most `T`, number at most the visits of the first `T` ordinals. -/
theorem commits_visits {Q L m X g k T c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (cta : g/L.block=c)
    (bound : ∀ j, j<k → ∀ sp, X.get (g,j)=some ⟨2546,.tc (.commit sp)⟩ →
      pollRound 2510 ((X.tr g).take j) ≤ T) :
    ((X.tr g).take k).countP (commitsTo (Ring.empty.obj L c s)) ≤ visits 0 T s := by
  classical
  subst cta
  let pv (j : Nat) := pollRound 2510 ((X.tr g).take j)
  let l := Ring.empty.obj L (g/L.block) s
  let uses := (Finset.range k).filter fun j => ((X.tr g)[j]?).any (commitsTo l)
  have info {j : Nat} (hj : j ∈ uses) :
      (∃ a, X.get (g,j)=some ⟨2546,.tc (.commit a)⟩) ∧
      0 < pv j ∧ pv j≤T ∧ (pv j-1)%3=s.val := by
    obtain ⟨lt,kind⟩ := Finset.mem_filter.mp hj
    have jk := Finset.mem_range.mp lt
    cases get : (X.tr g)[j]? with
    | none => rw [get] at kind; cases kind
    | some ev =>
      rw [get] at kind
      obtain ⟨a,eq,addr⟩ := MbarRing.Notify.commit_of_commitsTo kind
      obtain ⟨p,kd⟩ := ev
      cases eq
      obtain ⟨rfl,_,slot⟩ := slot_of_commit hp hX hf get addr
      obtain ⟨pos,_⟩ := Mma.Export.empty_poll_bounds hp hX hf warp get
      exact ⟨⟨_,get⟩,pos,bound j jk _ get,slot⟩
  have budget : uses.card ≤ (Finset.range (visits 0 T s)).card := by
    apply Finset.card_le_card_of_injOn (fun j => (pv j-1)/3)
    · intro j hj
      obtain ⟨_,pos,le,slot⟩ := info hj
      apply Finset.mem_range.mpr
      change (pv j-1)/3 < visits 0 T s
      unfold visits
      have := s.isLt
      omega
    · intro j hj v hv same
      obtain ⟨⟨_,first⟩,pos,_,slot⟩ := info hj
      obtain ⟨⟨_,last⟩,pos',_,slot'⟩ := info hv
      apply Mma.Export.empty_unique hp hX hf words warp first last
      change pv j=pv v
      change (pv j-1)/3=(pv v-1)/3 at same
      omega
  have cn := MbarRing.Slot.countP_take_card (X.tr g) (commitsTo l) k
  change _=uses.card at cn
  rw [cn]
  simpa using budget

/-- **An MMA read has a ready poll beyond its empty commits**: if all commits before it have
ordinal at most `T`, and the issue sits after the ready poll of ordinal `n ≥ T` of slot `s`. -/
theorem read_credit {Q L m X g k T n c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (rows : MbarRows Q L X) (hg : g<L.threads)
    (warp : g%L.block/32=7) (cta : g/L.block=c)
    (bound : ∀ j, j<k → ∀ sp, X.get (g,j)=some ⟨2546,.tc (.commit sp)⟩ →
      pollRound 2510 ((X.tr g).take j) ≤ T)
    (le : T ≤ n) (lt : n<pollRound 2462 ((X.tr g).take k)) (slot : n%3=s.val) :
    ((X.tr g).take k).countP (commitsTo (Ring.empty.obj L c s))+1 ≤
      okPolls (Ring.ready.obj L c s) ((X.tr g).take k) := by
  have commits := commits_visits (s := s) hp hX hf words warp cta bound
  subst cta
  have count := poll_count (r := .ready) rows hg warp s k
  change okPolls _ _ = visits 0 (pollRound 2462 ((X.tr g).take k)) s at count
  rw [count]
  unfold visits at commits ⊢
  have := s.isLt
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV

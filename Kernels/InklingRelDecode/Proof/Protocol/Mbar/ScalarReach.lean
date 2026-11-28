-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarHistory
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Protocol.ReachJoint
public import Kernels.InklingRelDecode.Proof.Lib.DepNode
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarCommits
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarArrivals
import Kernels.InklingRelDecode.Proof.Softmax.Export.ArrivalCredit
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing MbarRow

/-- The reuse paths of the three scalar channels of CTA `c` that end at a node: the elected
lane's polls of a probability slot reach the lane-zero arrivals, and lane zero's polls of a score
slot and of the output reach the elected lane's commits. -/
def Goals (L : Launch) (X : Execution) (c : Nat) (n : Lib.DepNode) : Prop :=
  (∀ s : Fin 2, Reach.UnitAt L kernel X ((Object.prob s).loc L c) 1 (fun _ => c*L.block) 0
    (KV.leader L X c 7) n) ∧
  (∀ s : Fin 2, Reach.NotifyAt L kernel X ((Object.score s).loc L c) (KV.leader L X c 7)
    ((Object.score s).loc L c) 0 (c*L.block) n) ∧
  Reach.NotifyAt L kernel X (Object.done.loc L c) (KV.leader L X c 7) (Object.done.loc L c) 0
    (c*L.block) n

theorem spin {L A m X} (hX : Consistent L kernel A m X) :
    ∀ w pc m' q acq sc, X.get w = some ⟨pc,.wait m' q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit :=
  fun _ _ _ _ _ _ he => (Lib.poll_site hX he).2

/-- Thread `h`'s poll `j` of slot `m` reaches lane zero's later publication `ka` of CTA `c`, when
`j + 1` is at most the lane zero's polls of the slot before it. -/
def ToArrival (L : Launch) (X : Execution) (c : Nat) (m : Loc) (h : Nat) : Prop :=
  ∀ {j ka l tx cnt rel sc}, X.get (c*L.block,ka)=some ⟨1013,.arrive l tx cnt rel sc⟩ →
    j+1≤okPolls m ((X.tr (c*L.block)).take ka) →
    Relation.TransGen (DepStep L kernel X) (.thread (h,Poll.nth X m h j),true)
      (.thread (c*L.block,ka),false)

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {c : Nat}

/-- **Lane zero's own polls reach its later publications.** -/
theorem ToArrival.zero (hX : Consistent L kernel Assumptions.all m X) {o : Loc} :
    ToArrival L X c o (c*L.block) := fun get enough =>
  .single (Reach.poll_guard (spin hX) (List.getElem?_eq_some_iff.mp get).1 enough)

/-- **A lane-zero arrival follows each earlier poll of the elected lane on its slot**: the poll
precedes the score commit two blocks later, whose notification the lane's score poll observes. -/
theorem prob_path (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hc : c<L.grid) {s : Fin 2} {ka pc tx cnt rel sc j}
    (get : X.get (c*L.block,ka)=some ⟨pc,.arrive ((Object.prob s).loc L c) tx cnt rel sc⟩)
    (hj : j<arrivals ((Object.prob s).loc L c) ((X.tr (c*L.block)).take ka))
    (ih : ∀ n' ∈ Reach.nodes L X, Relation.TransGen (DepStep L kernel X) n'
      (.thread (c*L.block,ka),false) → Goals L X c n') :
    Relation.TransGen (DepStep L kernel X)
      (.thread (KV.leader L X c 7,Poll.nth X ((Object.prob s).loc L c) (KV.leader L X c 7) j),true)
      (.thread (c*L.block,ka),false) := by
  have hz : c*L.block<L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cta : c*L.block/L.block=c := by simp [hp.block]
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  obtain ⟨rfl,slot,bound⟩ := arrival_ordinal rows hz get
  obtain ⟨_,pollsScore⟩ := Softmax.Export.arrival_polls hp hX hf get
  have count := Scalar.count rows hz (Object.score s) ka
  simp only [roundAt,Object.pc,cta] at count
  have len := (List.getElem?_eq_some_iff.mp get).1
  have total : okPolls ((Object.score s).loc L c) ((X.tr (c*L.block)).take ka)≤
      okPolls ((Object.score s).loc L c) (X.tr (c*L.block)) := by
    have mono := countP_take_mono (okPoll ((Object.score s).loc L c))
      (X.tr (c*L.block)) (show ka≤(X.tr (c*L.block)).length from len.le)
    rw [List.take_length] at mono
    exact mono
  have enough : j+1+1≤okPolls ((Object.score s).loc L c) ((X.tr (c*L.block)).take ka) := by
    rw [count]
    change j+1+1≤(pollRound 1257 ((X.tr (c*L.block)).take ka)+2-1-s.val)/2
    rw [pollsScore]
    omega
  have guard : DepStep L kernel X
      (.thread (c*L.block,Poll.nth X ((Object.score s).loc L c) (c*L.block) (j+1)),true)
      (.thread (c*L.block,ka),false) :=
    Reach.poll_guard (spin hX) len enough
  have note := Reach.notify_content hX (notification hp hX hf rows init (c := c) (.inl ⟨s,rfl⟩))
    (spin hX) (h := c*L.block) (J := j+1) (by omega) (Relation.TransGen.single guard)
    (fun n' hn' hlt => (ih n' hn' hlt).2.1 s)
  obtain ⟨hS,wit⟩ := note
  obtain ⟨⟨k,r,hk,hid,-,-⟩,pc',sp,getc,hm,ht,hcnt⟩ := Notify.Obj.S_rec
    (notification hp hX hf rows init (c := c) (.inl ⟨s,rfl⟩)) hS
  obtain ⟨_,_,_,_,mem⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
  have credit := score_commits hp hX hf rows words hy wy cy getc hm
  rw [hcnt] at credit
  have lenc := (List.getElem?_eq_some_iff.mp getc).1
  have before : DepStep L kernel X
      (.thread (KV.leader L X c 7,Poll.nth X ((Object.prob s).loc L c) (KV.leader L X c 7) j),
        true) (.thread (KV.leader L X c 7,Notify.cm X (KV.leader L X c 7)
          ((Object.score s).loc L c) (j+1)),false) :=
    Reach.poll_guard (spin hX) lenc (by omega)
  exact ((Relation.TransGen.single before).tail (Reach.commit_notify getc mem)).tail
    (DepStep.of_witness L wit) |>.tail guard

/-- **The commit of a probability slot's consumer**: the elected lane's later poll of the slot
observes lane zero's arrival, which follows lane zero's score or output poll. The path from the
elected lane's poll `j` of `m` to a notification node `n`, and the arrival it observes. -/
private theorem observe (hX : Consistent L kernel Assumptions.all m X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) {s : Fin 2} {j}
    {n}
    (path : Relation.TransGen (DepStep L kernel X)
      (.thread (KV.leader L X c 7,
        Poll.nth X ((Object.prob s).loc L c) (KV.leader L X c 7) j),true) n)
    (below : j<okPolls ((Object.prob s).loc L c) (X.tr (KV.leader L X c 7)))
    (ih : ∀ n' ∈ Reach.nodes L X, Relation.TransGen (DepStep L kernel X) n' n → Goals L X c n') :
    ∃ ka pc sc, X.get (c*L.block,ka)=some ⟨pc,.arrive ((Object.prob s).loc L c) 0 1 true sc⟩ ∧
      arrivals ((Object.prob s).loc L c) ((X.tr (c*L.block)).take ka)=j ∧
      Witness L X (.thread (c*L.block,ka))
        (KV.leader L X c 7,Poll.nth X ((Object.prob s).loc L c) (KV.leader L X c 7) j) := by
  obtain ⟨hS,wit⟩ := Reach.unit_content hX (probability hX rows init (c := c) s) (spin hX)
    (g := KV.leader L X c 7) (J := j) (by omega) path (fun n' hn' hlt => (ih n' hn' hlt).1 s) 0
  obtain ⟨_,⟨pc,sc,get⟩,cnt⟩ := Unit.Obj.S_rec (probability hX rows init (c := c) s) hS
  exact ⟨_,pc,sc,get,cnt,wit⟩

/-- **Score commits**: lane zero's score polls reach each later commit of the elected lane to
the slot. -/
theorem score_path (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hc : c<L.grid) {s : Fin 2} {h ic pc sp rank j}
    (reach : ToArrival L X c ((Object.score s).loc L c) h)
    (get : X.get (KV.leader L X c 7,ic)=some ⟨pc,.tc (.commit sp)⟩)
    (hm : sp.mbar=(Object.score s).loc L c)
    (mem : rank ∈ X.tcNotified (KV.leader L X c 7,ic))
    (hj : j<((X.tr (KV.leader L X c 7)).take ic).countP (commitsTo ((Object.score s).loc L c)))
    (ih : ∀ n' ∈ Reach.nodes L X, Relation.TransGen (DepStep L kernel X) n'
      (.async (KV.leader L X c 7,ic) (.tcNotify rank),false) → Goals L X c n') :
    Relation.TransGen (DepStep L kernel X)
      (.thread (h,Poll.nth X ((Object.score s).loc L c) h j),true)
      (.async (KV.leader L X c 7,ic) (.tcNotify rank),false) := by
  have hz : c*L.block<L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cta : c*L.block/L.block=c := by simp [hp.block]
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  have credit := score_commits hp hX hf rows words hy wy cy get hm
  have len := (List.getElem?_eq_some_iff.mp get).1
  have total : okPolls ((Object.prob s).loc L c) ((X.tr (KV.leader L X c 7)).take ic)≤
      okPolls ((Object.prob s).loc L c) (X.tr (KV.leader L X c 7)) := by
    have mono := countP_take_mono (okPoll ((Object.prob s).loc L c))
      (X.tr (KV.leader L X c 7)) (show ic≤(X.tr (KV.leader L X c 7)).length from len.le)
    rw [List.take_length] at mono
    exact mono
  have before : DepStep L kernel X
      (.thread (KV.leader L X c 7,Poll.nth X ((Object.prob s).loc L c) (KV.leader L X c 7) j),
        true) (.thread (KV.leader L X c 7,ic),false) :=
    Reach.poll_guard (spin hX) len (by omega)
  have path := (Relation.TransGen.single before).tail (Reach.commit_notify get mem)
  obtain ⟨ka,pc',sc,geta,cnt,wit⟩ := observe hX rows init path (by omega) ih
  obtain ⟨rfl,slot,bound⟩ := arrival_ordinal rows hz geta
  obtain ⟨_,pollsScore⟩ := Softmax.Export.arrival_polls hp hX hf geta
  have count := Scalar.count rows hz (Object.score s) ka
  simp only [roundAt,Object.pc,cta] at count
  have enough : j+1≤okPolls ((Object.score s).loc L c) ((X.tr (c*L.block)).take ka) := by
    rw [count]
    change j+1≤(pollRound 1257 ((X.tr (c*L.block)).take ka)+2-1-s.val)/2
    rw [pollsScore]
    omega
  exact (reach geta enough).tail (DepStep.of_witness L wit) |>.trans path

/-- **Output commits**: lane zero's output polls reach each later done commit of the elected
lane. -/
theorem done_path (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hc : c<L.grid) {h ic pc sp rank j}
    (reach : ToArrival L X c (Object.done.loc L c) h)
    (get : X.get (KV.leader L X c 7,ic)=some ⟨pc,.tc (.commit sp)⟩)
    (hm : sp.mbar=Object.done.loc L c)
    (mem : rank ∈ X.tcNotified (KV.leader L X c 7,ic))
    (hj : j<((X.tr (KV.leader L X c 7)).take ic).countP (commitsTo (Object.done.loc L c)))
    (ih : ∀ n' ∈ Reach.nodes L X, Relation.TransGen (DepStep L kernel X) n'
      (.async (KV.leader L X c 7,ic) (.tcNotify rank),false) → Goals L X c n') :
    Relation.TransGen (DepStep L kernel X)
      (.thread (h,Poll.nth X (Object.done.loc L c) h j),true)
      (.async (KV.leader L X c 7,ic) (.tcNotify rank),false) := by
  have hz : c*L.block<L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cta : c*L.block/L.block=c := by simp [hp.block]
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  have credit := done_commits hp hX hf rows words hy wy get hm
  have len := (List.getElem?_eq_some_iff.mp get).1
  let s : Fin 2 := ⟨(j+1)%2,Nat.mod_lt _ (by omega)⟩
  have count := Scalar.count rows hy (Object.prob s) ic
  simp only [roundAt,Object.pc,cy] at count
  have total : okPolls ((Object.prob s).loc L c) ((X.tr (KV.leader L X c 7)).take ic)≤
      okPolls ((Object.prob s).loc L c) (X.tr (KV.leader L X c 7)) := by
    have mono := countP_take_mono (okPoll ((Object.prob s).loc L c))
      (X.tr (KV.leader L X c 7)) (show ic≤(X.tr (KV.leader L X c 7)).length from len.le)
    rw [List.take_length] at mono
    exact mono
  have room : (j+1)/2+1≤okPolls ((Object.prob s).loc L c)
      ((X.tr (KV.leader L X c 7)).take ic) := by
    rw [count]
    change (j+1)/2+1≤(pollRound 2510 ((X.tr (KV.leader L X c 7)).take ic)+2-1-(j+1)%2)/2
    omega
  have before : DepStep L kernel X
      (.thread (KV.leader L X c 7,Poll.nth X ((Object.prob s).loc L c) (KV.leader L X c 7)
        ((j+1)/2)),true) (.thread (KV.leader L X c 7,ic),false) :=
    Reach.poll_guard (spin hX) len room
  have path := (Relation.TransGen.single before).tail (Reach.commit_notify get mem)
  obtain ⟨ka,pc',sc,geta,cnt,wit⟩ := observe hX rows init path (by omega) ih
  obtain ⟨rfl,slot,bound⟩ := arrival_ordinal rows hz geta
  obtain ⟨pollsDone,_⟩ := Softmax.Export.arrival_polls hp hX hf geta
  have counted := Scalar.count rows hz Object.done ka
  simp only [roundAt,Object.pc,cta] at counted
  have enough : j+1≤okPolls (Object.done.loc L c) ((X.tr (c*L.block)).take ka) := by
    rw [counted]
    change j+1≤(pollRound 2239 ((X.tr (c*L.block)).take ka)+1-1-0)/1
    rw [pollsDone]
    have : s.val=(j+1)%2 := rfl
    omega
  exact (reach geta enough).tail (DepStep.of_witness L wit) |>.trans path

/-- The goals at a node from the goals at the nodes before it. -/
theorem goals_step (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hc : c<L.grid) {n}
    (ih : ∀ n' ∈ Reach.nodes L X, Relation.TransGen (DepStep L kernel X) n' n →
      Goals L X c n') : Goals L X c n := by
  refine ⟨fun s x hx hn j hj => ?_,fun s x hx hn j hj => ?_,fun x hx hn j hj => ?_⟩
  · obtain ⟨_,⟨pc,sc,geta⟩,cnt⟩ := Unit.Obj.S_rec (probability hX rows init (c := c) s) hx
    subst hn
    exact prob_path hp hX hf rows init words hc geta (lt_of_lt_of_eq hj cnt.symm) ih
  · obtain ⟨⟨k,r,hk,hid,-,-⟩,pc,sp,getc,hm,ht,hcnt⟩ := Notify.Obj.S_rec
      (notification hp hX hf rows init (c := c) (.inl ⟨s,rfl⟩)) hx
    obtain ⟨_,_,_,_,mem⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
    subst hn
    exact score_path hp hX hf rows init words hc (ToArrival.zero hX) getc hm mem (by omega) ih
  · obtain ⟨⟨k,r,hk,hid,-,-⟩,pc,sp,getc,hm,ht,hcnt⟩ := Notify.Obj.S_rec
      (notification hp hX hf rows init (c := c) (.inr rfl)) hx
    obtain ⟨_,_,_,_,mem⟩ := Reach.notify_rec hX (List.mem_of_getElem? hk) hid
    subst hn
    exact done_path hp hX hf rows init words hc (ToArrival.zero hX) getc hm mem (by omega) ih

/-- **The reuse paths of the scalar channels hold at every node.** -/
theorem goals_all (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) :
    ∀ c, c<L.grid → ∀ n ∈ Reach.nodes L X, Goals L X c n := by
  intro c hc n hn
  exact Reach.joint hX (G := fun c n => c<L.grid → Goals L X c n)
    (fun n _ ih c hc => goals_step hp hX hf rows init words hc
      (fun n' hn' hlt => ih n' hn' hlt c hc))
    c n hn hc

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar

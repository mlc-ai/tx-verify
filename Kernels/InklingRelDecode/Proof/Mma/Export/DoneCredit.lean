-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.RankOrder
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.Machine
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Frame

private theorem done_visit {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨2548,.tc (.commit sp)⟩) :
    let i := pollRound 2510 ((X.tr g).take k)
    0 < i ∧ ((X.tr g).take k).countP Execution.isShfl =
        1+min (i+1) (Lib.blocksOf Q L (g/L.block))+i ∧
      ∃ d, stateAt (thread Q L) X g k=some (some d) ∧
        threadRank d=8+30*(Lib.blocksOf Q L (g/L.block)+1-i) := by
  obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp)
    (by decide : 2344<2548) (by decide : 2548<2557) (by decide : 2548≠2422)
  cases r with
  | loader =>
    have wrong : g%L.block/32=6 := inv.1
    omega
  | mma =>
    obtain ⟨_,ref,hq,hp',-⟩ := inv
    have hi := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs).1
    have loop : Mma.Inv d := hi.1
    have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    have bal := mma_balance hp hX hf (lt_of_get hX he) warp (noUbBefore_of_get hX he) hs
    have sh := fcount hs .shfl
    change n .shfl=((X.tr g).take k).countP Execution.isShfl at sh
    have only (site : Site) : 2548=site.pc → site=.pvCommit2 := by
      cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)
    obtain ⟨s,i,v⟩ := d
    obtain rfl := only s pc
    have limit := ref_count ref rfl
    change low v=Lib.blocksOf Q L (g/L.block) at limit
    have pv := (fcount hs (.poll 2510)).symm.trans hp'
    change pollRound 2510 _=i at pv
    change 0 < i ∧ i ≤ low v ∧ _ at loop
    dsimp only
    change n .shfl+0=1+n (.poll 2462)+n (.poll 2510) at bal
    change n (.poll 2462)=min (i+1) (low v) at hq
    change n (.poll 2510)=i at hp'
    rw [pv]
    refine ⟨loop.1,by rw [←sh,←limit]; omega,_,hs,?_⟩
    change 8+(30*(low v+1-i)+0)=_
    rw [limit,Nat.add_zero]

/-- The broadcast for a P poll precedes the elected lane's done notification. -/
public theorem done_shuffles {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨2548,.tc (.commit sp)⟩) :
    let i := pollRound 2510 ((X.tr g).take k)
    0 < i ∧ ((X.tr g).take k).countP Execution.isShfl =
      1+min (i+1) (Lib.blocksOf Q L (g/L.block))+i :=
  ⟨(done_visit hp hX hf warp he).1,(done_visit hp hX hf warp he).2.1⟩

/-- A thread notifies the output consumer at most once at each successful PV poll ordinal. -/
public theorem done_unique {Q L m X g j k a b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (first : X.get (g,j)=some ⟨2548,.tc (.commit a)⟩)
    (last : X.get (g,k)=some ⟨2548,.tc (.commit b)⟩)
    (ord : pollRound 2510 ((X.tr g).take j)=pollRound 2510 ((X.tr g).take k)) : j=k := by
  obtain ⟨_,_,d,fst,rank⟩ := done_visit hp hX hf warp first
  obtain ⟨_,_,s,snd,rank'⟩ := done_visit hp hX hf warp last
  have eq : threadRank d=threadRank s := rank.trans (ord ▸ rank'.symm)
  rcases lt_trichotomy j k with lt|eq|gt
  · exact (eq.not_gt (later_rank hp hX hf words first rfl fst lt
      (List.getElem?_eq_some_iff.mp last).1.le snd)).elim
  · exact eq
  · exact (eq.not_lt (later_rank hp hX hf words last rfl snd gt
      (List.getElem?_eq_some_iff.mp first).1.le fst)).elim

private def pvLits : List Nat := [2530,2533,2535,2537,2539,2541,2543,2545]

private theorem pv_site (s : Site) (hit : s.pc ∈ pvLits) : ∃ j, s = .pv j := by
  cases s <;> first | exact ⟨_,rfl⟩ | exact absurd hit (by decide +kernel) |
    (rename_i j; fin_cases j <;> exact absurd hit (by decide +kernel))

/-- The rank of a PV issue's state: its block's offset, and the PV poll ordinal it follows. -/
private theorem pv_issue_rank {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (second : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩) (pv : pc ∈ pvLits) :
    ∃ i jj : Nat, jj < 8 ∧ pollRound 2510 ((X.tr g).take k)=i ∧ ∃ d, stateAt (thread Q L) X g k=some
      (some d) ∧ threadRank d=8+(30*(Lib.blocksOf Q L (g/L.block)+1-i)+(28-(19+jj))) := by
  have range : ∀ p ∈ pvLits, 2422 < p ∧ p < 2557 := by decide +kernel
  obtain ⟨w,x,r,e,n,hs,pcs⟩ := mma_state hp hX hf second (fun _ => nofun) (range _ pv).1
    (range _ pv).2
  obtain ⟨-,ref,-,hp',-⟩ := (reached_table hf (lt_of_get hX second) (noUbBefore_of_get hX second)
    hs).2
  obtain ⟨st,i,v⟩ := e
  obtain ⟨jj,rfl⟩ := pv_site st (by change pc = st.pc at pcs; exact pcs ▸ pv)
  have limit : low v = Lib.blocksOf Q L (g/L.block) := ref_count ref rfl
  have pvr : pollRound 2510 ((X.tr g).take k) = i := (fcount hs (.poll 2510)).symm.trans hp'
  exact ⟨i,jj.val,jj.isLt,pvr,_,hs,by change 8+(30*(low v+1-i)+_)=_; rw [limit]; rfl⟩

/-- **A done commit before a PV issue has an earlier PV-poll ordinal.** -/
public theorem done_commit_lt {Q L m X g j k sp pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (first : X.get (g,j)=some ⟨2548,.tc (.commit sp)⟩) (lt : j<k)
    (second : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (pv : pc ∈ [2530,2533,2535,2537,2539,2541,2543,2545]) :
    pollRound 2510 ((X.tr g).take j) < pollRound 2510 ((X.tr g).take k) := by
  obtain ⟨pos,_,d,fst,rank⟩ := done_visit hp hX hf warp first
  obtain ⟨i,jj,jb,pvr,e,hs,rk⟩ := pv_issue_rank hp hX hf second pv
  have lr := later_rank hp hX hf words first rfl fst lt
    (List.getElem?_eq_some_iff.mp second).1.le hs
  rw [rank,rk] at lr
  rw [pvr]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export

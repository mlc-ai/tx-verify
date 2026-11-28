-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.RankOrder
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.Machine

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Frame

private theorem score_visit {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨2499,.tc (.commit sp)⟩) :
    let i := pollRound 2462 ((X.tr g).take k)
    0 < i ∧ i ≤ Lib.blocksOf Q L (g/L.block) ∧
      pollRound 2510 ((X.tr g).take k)=i-2 ∧
      ∃ d, stateAt (thread Q L) X g k=some (some d) ∧
        threadRank d=8+30*(Lib.blocksOf Q L (g/L.block)+1-(i-1))+15 := by
  obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp)
    (by decide : 2344<2499) (by decide : 2499<2557) (by decide : 2499≠2422)
  cases r with
  | loader =>
    have wrong : g%L.block/32=6 := inv.1
    omega
  | mma =>
    obtain ⟨_,ref,hq,hp',-⟩ := inv
    have hi := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs).1
    have loop : Mma.Inv d := hi.1
    have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    have only (site : Site) : 2499=site.pc → site=.qkCommit := by
      cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)
    obtain ⟨s,i,v⟩ := d
    obtain rfl := only s pc
    have limit := ref_count ref rfl
    change low v=Lib.blocksOf Q L (g/L.block) at limit
    have rq := (fcount hs (.poll 2462)).symm.trans hq
    have pv := (fcount hs (.poll 2510)).symm.trans hp'
    change pollRound 2462 _=i+1 at rq
    change pollRound 2510 _=i-1 at pv
    change i<low v ∧ _ at loop
    dsimp only
    rw [pv,rq]
    refine ⟨by omega,by omega,by omega,_,hs,?_⟩
    change 8+(30*(low v+1-i)+15)=_
    rw [limit]
    omega

/-- A score notification for block `r` is issued after `r+1` ready polls and `r-1` PV polls:
the PV polls trail the ready polls by two. -/
public theorem score_polls {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨2499,.tc (.commit sp)⟩) :
    0<pollRound 2462 ((X.tr g).take k) ∧
      pollRound 2462 ((X.tr g).take k)≤Lib.blocksOf Q L (g/L.block) ∧
      pollRound 2510 ((X.tr g).take k)=pollRound 2462 ((X.tr g).take k)-2 := by
  obtain ⟨a,b,c,_⟩ := score_visit hp hX hf warp he
  exact ⟨a,b,c⟩

/-- A thread notifies the score consumer at most once at each ready-poll ordinal. -/
public theorem score_unique {Q L m X g j k a b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (first : X.get (g,j)=some ⟨2499,.tc (.commit a)⟩)
    (last : X.get (g,k)=some ⟨2499,.tc (.commit b)⟩)
    (ord : pollRound 2462 ((X.tr g).take j)=pollRound 2462 ((X.tr g).take k)) : j=k := by
  obtain ⟨_,_,pj,d,fst,rank⟩ := score_visit hp hX hf warp first
  obtain ⟨_,_,pk,s,snd,rank'⟩ := score_visit hp hX hf warp last
  have eq : threadRank d=threadRank s := by
    rw [rank,rank',ord]
  rcases lt_trichotomy j k with lt|eq'|gt
  · exact (eq.not_gt (later_rank hp hX hf words first rfl fst lt
      (List.getElem?_eq_some_iff.mp last).1.le snd)).elim
  · exact eq'
  · exact (eq.not_lt (later_rank hp hX hf words last rfl snd gt
      (List.getElem?_eq_some_iff.mp first).1.le fst)).elim

private def qkLits : List Nat := [2483,2486,2488,2490,2492,2494,2496,2498]

private theorem qk_site (s : Site) (hit : s.pc ∈ qkLits) : ∃ j, s = .qk j := by
  cases s <;> first | exact ⟨_,rfl⟩ | exact absurd hit (by decide +kernel) |
    (rename_i j; fin_cases j <;> exact absurd hit (by decide +kernel))

/-- **A score commit before a QK issue has an earlier ready-poll ordinal.** -/
public theorem score_commit_lt {Q L m X g j k sp pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (first : X.get (g,j)=some ⟨2499,.tc (.commit sp)⟩) (lt : j<k)
    (second : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (qk : pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498]) :
    pollRound 2462 ((X.tr g).take j) < pollRound 2462 ((X.tr g).take k) := by
  obtain ⟨pos,_,_,d,fst,rank⟩ := score_visit hp hX hf warp first
  have range : ∀ p ∈ qkLits, 2422 < p ∧ p < 2557 := by decide +kernel
  obtain ⟨w,x,r,e,n,hs,inv⟩ := worker_event hp hX hf second (by simp)
    (by have := (range _ qk).1; change 2344 < pc; omega) (range _ qk).2
    (by have := (range _ qk).1; change pc ≠ 2422; omega)
  cases r with
  | loader =>
    have wrong : g%L.block/32=6 := inv.1
    omega
  | mma =>
    obtain ⟨_,ref,hq,hp',-⟩ := inv
    have hi := (reached_table hf (lt_of_get hX second) (noUbBefore_of_get hX second) hs).1
    have loop : Mma.Inv e := hi.1
    have pcs := event_pcU (fun g hg => thread_sound hp hg) hX second hs (by simp)
    obtain ⟨st,i,v⟩ := e
    change pc = st.pc at pcs
    obtain ⟨jj,rfl⟩ := qk_site st (pcs ▸ qk)
    have limit := ref_count ref rfl
    have qr := (fcount hs (.poll 2462)).symm.trans hq
    change low v = Lib.blocksOf Q L (g/L.block) at limit
    change pollRound 2462 _ = i+1 at qr
    have lenk := (List.getElem?_eq_some_iff.mp second).1.le
    have lr := later_rank hp hX hf words first rfl fst lt lenk hs
    rw [rank] at lr
    change 8+(30*(low v+1-i)+(28-(5+jj.val))) < _ at lr
    have jb := jj.isLt
    rw [limit] at lr
    rw [qr]
    omega

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export

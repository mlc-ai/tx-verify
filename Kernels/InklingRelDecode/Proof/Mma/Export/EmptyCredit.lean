-- SPDX-License-Identifier: Apache-2.0
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

private theorem empty_visit {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨2546,.tc (.commit sp)⟩) :
    let i := pollRound 2510 ((X.tr g).take k)
    0 < i ∧ i ≤ pollRound 2462 ((X.tr g).take k) ∧
      ∃ d, stateAt (thread Q L) X g k=some (some d) ∧
        threadRank d=8+30*(Lib.blocksOf Q L (g/L.block)+1-i)+1 := by
  obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp)
    (by decide : 2344<2546) (by decide : 2546<2557) (by decide : 2546≠2422)
  cases r with
  | loader =>
    have wrong : g%L.block/32=6 := inv.1
    omega
  | mma =>
    obtain ⟨_,ref,hq,hp',-⟩ := inv
    have hi := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs).1
    have loop : Mma.Inv d := hi.1
    have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    have only (site : Site) : 2546=site.pc → site=.pvCommit1 := by
      cases site <;> repeat' first | decide +kernel | (rename_i j; revert j)
    obtain ⟨s,i,v⟩ := d
    obtain rfl := only s pc
    have limit := ref_count ref rfl
    change low v=Lib.blocksOf Q L (g/L.block) at limit
    have rq := (fcount hs (.poll 2462)).symm.trans hq
    have pv := (fcount hs (.poll 2510)).symm.trans hp'
    change pollRound 2462 _=min (i+1) (low v) at rq
    change pollRound 2510 _=i at pv
    change 0 < i ∧ i ≤ low v ∧ _ at loop
    dsimp only
    rw [pv,rq]
    refine ⟨loop.1,by omega,_,hs,?_⟩
    change 8+(30*(low v+1-i)+1)=_
    rw [limit,Nat.add_assoc]

/-- Every empty notification spends a completed PV poll and a ready poll. -/
public theorem empty_poll_bounds {Q L m X g k sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=7) (he : X.get (g,k)=some ⟨2546,.tc (.commit sp)⟩) :
    0<pollRound 2510 ((X.tr g).take k) ∧
      pollRound 2510 ((X.tr g).take k)≤pollRound 2462 ((X.tr g).take k) := by
  obtain ⟨pos,ready,_⟩ := empty_visit hp hX hf warp he
  exact ⟨pos,ready⟩

/-- A thread returns the KV slot at most once at each successful PV poll ordinal. -/
public theorem empty_unique {Q L m X g j k a b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (first : X.get (g,j)=some ⟨2546,.tc (.commit a)⟩)
    (last : X.get (g,k)=some ⟨2546,.tc (.commit b)⟩)
    (ord : pollRound 2510 ((X.tr g).take j)=pollRound 2510 ((X.tr g).take k)) : j=k := by
  obtain ⟨_,_,d,fst,rank⟩ := empty_visit hp hX hf warp first
  obtain ⟨_,_,s,snd,rank'⟩ := empty_visit hp hX hf warp last
  have eq : threadRank d=threadRank s := rank.trans (ord ▸ rank'.symm)
  rcases lt_trichotomy j k with lt|eq|gt
  · exact (eq.not_gt (later_rank hp hX hf words first rfl fst lt
      (List.getElem?_eq_some_iff.mp last).1.le snd)).elim
  · exact eq
  · exact (eq.not_lt (later_rank hp hX hf words last rfl snd gt
      (List.getElem?_eq_some_iff.mp first).1.le fst)).elim

private def pvLits : List Nat := [2530,2533,2535,2537,2539,2541,2543,2545]

private theorem pv_site (s : Site) (hit : s.pc ∈ pvLits) :
    ∃ j, s = .pv j := by
  cases s <;> first | exact ⟨_,rfl⟩ | exact absurd hit (by decide +kernel) |
    (rename_i j; fin_cases j <;> exact absurd hit (by decide +kernel))

/-- An empty commit before a PV issue has an earlier PV ordinal: the issue of ordinal `i`
precedes the commit of ordinal `i` in the lane's rank. -/
public theorem commit_ord_lt {Q L m X g j k sp pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=7) (first : X.get (g,j)=some ⟨2546,.tc (.commit sp)⟩) (lt : j<k)
    (second : X.get (g,k)=some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (pv : pc ∈ [2530,2533,2535,2537,2539,2541,2543,2545]) :
    pollRound 2510 ((X.tr g).take j) < pollRound 2510 ((X.tr g).take k) := by
  obtain ⟨_,_,d,fst,rank⟩ := empty_visit hp hX hf warp first
  have range : ∀ p ∈ pvLits, 2422 < p ∧ p < 2557 := by decide +kernel
  obtain ⟨w,x,r,e,n,hs,inv⟩ := worker_event hp hX hf second (by simp)
    (by have := (range _ pv).1; change 2344 < pc; omega) (range _ pv).2
    (by have := (range _ pv).1; change pc ≠ 2422; omega)
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
    obtain ⟨jj,rfl⟩ := pv_site st (pcs ▸ pv)
    have limit := ref_count ref rfl
    have pvr := (fcount hs (.poll 2510)).symm.trans hp'
    change low v = Lib.blocksOf Q L (g/L.block) at limit
    change pollRound 2510 _ = i at pvr
    change 0 < i ∧ i ≤ low v ∧ _ at loop
    have lenk := (List.getElem?_eq_some_iff.mp second).1.le
    have lr := later_rank hp hX hf words first rfl fst lt lenk hs
    rw [rank] at lr
    change 8+(30*(low v+1-i)+(28-(19+jj.val))) < _ at lr
    have jb := jj.isLt
    rw [limit] at lr
    rw [pvr]
    omega


end PTX.Kernels.InklingRelDecode.Proof.Mma.Export

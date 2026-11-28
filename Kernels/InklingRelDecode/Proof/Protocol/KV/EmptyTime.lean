-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Wait
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Lib.ProducerLag
import Kernels.InklingRelDecode.Proof.Protocol.Warp.Leader
import Kernels.InklingRelDecode.Proof.Loader.Export.Time
import Kernels.InklingRelDecode.Proof.Mma.Export.Producer

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched PTX.MbarRing

theorem empty_lag {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : NoUbOutside L X) (hc : c<L.grid)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y) (s : Fin 3) :
    ∃ τ U, LagN (schedule Q L) X (Ring.empty.obj L c s) (1-preload Q L c s) (·=leader L X c 7)
      (Waiting L m X .empty c s) τ U (commitsTo (Ring.empty.obj L c s)) := by
  let pre := Iface.preloadCount Q L c
  let δ := preload Q L c s
  let N := Lib.blocksOf Q L c
  let U := (N+2-s.val)/3
  let y := leader L X c 7
  let l := Ring.empty.obj L c s
  let slot (j : Nat) := Lib.Slots.emptyWait (s.val+3*(j+δ))
  have small := s.isLt
  have atMost : δ≤1 := by unfold δ preload; split <;> decide
  have ⟨hy,cy,wy⟩ := leader_warp (X := X) hp hc (by decide : 7<8)
  change y/L.block=c at cy
  suffices ∃ τ, LagN (schedule Q L) X l (1-δ) (·=y) (Waiting L m X .empty c s) τ U
      (commitsTo l) by obtain ⟨τ,h⟩ := this; exact ⟨τ,U,h⟩
  apply Lib.producer_lag _ _ _ _ _ _ slot
  · intro a b le
    change 1000+400*(s.val+3*(a+δ)) ≤ 1000+400*(s.val+3*(b+δ))
    omega
  · rintro g ⟨cta,q,sc,hn⟩
    obtain ⟨bound,clock⟩ := Loader.Export.empty_wait_time hp hf hn
    have hg := hn.lt
    obtain ⟨Y,hY,pref,get⟩ := hn
    obtain ⟨_,_,_,warp,_,pos,_⟩ := wait_info (r := .empty) (rows Y hY) hg get
    have ord := poll_count (r := .empty) (rows Y hY) hg warp s (X.tr g).length
    change okPolls _ ((Y.tr g).take _)=visits _ (pollRound 2374 ((Y.tr g).take _)) s at ord
    change s=MbarRow.slot3
      (Iface.preloadCount Q L (g/L.block)+pollRound 2374 ((Y.tr g).take _)) at pos
    rw [pref,cta] at pos ord
    rw [cta] at clock bound
    let r := pre+pollRound 2374 (X.tr g)
    have atR : s.val=r%3 := congrArg Fin.val pos
    change r<N at bound
    change okPolls l (X.tr g)=visits pre (pollRound 2374 (X.tr g)) s at ord
    have cap : pre≤3 := Nat.min_le_left ..
    have index : s.val+3*(okPolls l (X.tr g)+δ)=r := by
      unfold visits at ord
      change s.val+3*(okPolls l (X.tr g)+(if s.val<pre then 1 else 0))=r
      dsimp [r] at atR ⊢
      split <;> omega
    dsimp only
    change okPolls l (X.tr g)<U+(1-δ) ∧ slot (okPolls l (X.tr g))≤_
    refine ⟨by dsimp [U]; omega,?_⟩
    rw [clock]
    exact le_of_eq (congrArg Lib.Slots.emptyWait index)
  · intro j jU done
    apply Lib.count_of_occurrences (fun k _ => (pollRound 2510 ((X.tr y).take k)-1)/3)
    intro i
    let r := s.val+3*i.val
    have ix := i.isLt
    have bound : r<N := by dsimp [r,U] at *; omega
    have active : r<Lib.blocksOf Q L (y/L.block) := by rw [cy]; exact bound
    have eq : (⟨r%3,by omega⟩ : Fin 3)=s := by apply Fin.ext; dsimp [r]; omega
    have seen : Mma.Export.Issued X y 2546 2510 r ⟨.shared,y/L.block,
        L.sharedBase+Iface.kvEmpty ⟨r%3,by omega⟩⟩ := by
      by_contra miss
      obtain ⟨early,live⟩ := Mma.Export.empty_short hp hX hf words hu hy wy
        (Warp.leader_wins hp hX hc (by decide : 7<8)) active miss
      rcases done with ⟨k,p,ex⟩|behind
      · exact live k p ex
      · change slot (j+(1-δ))≤threadTime (schedule Q L) X y at behind
        have order : Lib.Slots.emptyCommit r<slot (j+(1-δ)) := by
          change 1000+400*(r+1)+100+27<1000+400*(s.val+3*(j+(1-δ)+δ))
          dsimp [r]; omega
        exact (early.trans_lt order).not_ge behind
    obtain ⟨k,sp,get,bar,round⟩ := seen
    refine ⟨k,_,get,?_,?_⟩
    · rw [cy,eq] at bar
      simp [commitsTo,bar,l,Ring.obj,Ring.offset]
    · rw [round]
      dsimp [r]; omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV

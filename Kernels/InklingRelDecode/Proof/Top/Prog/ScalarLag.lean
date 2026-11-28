-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarTime
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Lib.ProducerLag
import Kernels.InklingRelDecode.Proof.Protocol.Warp.Leader
import Kernels.InklingRelDecode.Proof.Mma.Export.Producer
import Kernels.InklingRelDecode.Proof.Softmax.Export.Producer

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.Sched MbarRow

noncomputable def Object.producer (o : Object) (L : Launch) (X : Execution) (c : Nat) :=
  match o with | .prob _ => c*L.block | _ => KV.leader L X c 7

def Object.issue (o : Object) (l : Loc) := match o with | .prob _ => arrivesOn l | _ => commitsTo l

private def label (o : Object) (es : List Event) :=
  match o with
  | .prob _ => es.countP (fun e : Event => e.pc==1013)
  | .score _ => pollRound 2462 es-1
  | .done => pollRound 2510 es-1

/-- The block ordinal of an actual arrival or commit witnesses one distinct issue. -/
private theorem due {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : ¬HasUb X) (hc : c<L.grid)
    (o : Object) (r : Nat) (hi : r<Lib.blocksOf Q L c) (slot : o=o.atRound r)
    (late : let y := o.producer L X c
      (∃ k pc, X.get (y,k)=some ⟨pc,.exit⟩) ∨ o.waitSlot r≤threadTime (schedule Q L) X y) :
    ∃ k e, X.get (o.producer L X c,k)=some e ∧ o.issue (o.loc L c) e ∧
      label o ((X.tr (o.producer L X c)).take k)=r := by
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  have wins := Warp.leader_wins hp hX hc (by decide : 7<8)
  cases o with
  | prob s =>
    have hg : c*L.block<L.threads := by simp only [Launch.threads,hp.block] at *; omega
    have cta : c*L.block/L.block=c := by simp [hp.block]
    have lead : c*L.block%L.block=0 := by simp
    obtain ⟨k,get,tag⟩ : Softmax.Export.Published L X (c*L.block) r := by
      by_contra miss
      obtain ⟨early,live⟩ := Softmax.Export.prob_short hp hX hf (.of_noUb hu _) hg lead
        (by simpa only [cta] using hi) miss
      rcases late with ⟨k,p,ex⟩|clock
      · exact live k p ex
      · exact (early.trans_lt (Lib.Slots.probs r)).not_ge clock
    have same : s=slot2 r := Object.prob.inj slot
    refine ⟨k,_,get,?_,tag⟩
    simp [Object.issue,arrivesOn,sourceArrive,Object.loc,Object.offset,MbarRow.loc,cta,same]
  | score s =>
    obtain ⟨k,sp,get,bar,tag⟩ : Mma.Export.Issued X (KV.leader L X c 7) 2499 2462 r
        ((Object.score (slot2 r)).loc L ((KV.leader L X c 7)/L.block)) := by
      by_contra miss
      obtain ⟨early,live⟩ := Mma.Export.score_short hp hX hf words (.of_noUb hu) hy wy wins
        (by simpa only [cy] using hi) miss
      rcases late with ⟨k,p,ex⟩|clock
      · exact live k p ex
      · exact (early.trans_lt (Lib.Slots.scores r)).not_ge clock
    refine ⟨k,_,get,?_,by simp only [label,Object.producer,tag,Nat.add_sub_cancel]⟩
    have same : s=slot2 r := Object.score.inj slot
    simp [Object.issue,commitsTo,bar,cy,same]
  | done =>
    obtain ⟨k,sp,get,bar,tag⟩ : Mma.Export.Issued X (KV.leader L X c 7) 2548 2510 r
        (Object.done.loc L ((KV.leader L X c 7)/L.block)) := by
      by_contra miss
      obtain ⟨early,live⟩ := Mma.Export.done_short hp hX hf words (.of_noUb hu) hy wy wins
        (by simpa only [cy] using hi) miss
      rcases late with ⟨k,p,ex⟩|clock
      · exact live k p ex
      · exact (early.trans_lt (Lib.Slots.done (r+1))).not_ge clock
    refine ⟨k,_,get,?_,by simp only [label,Object.producer,tag,Nat.add_sub_cancel]⟩
    simp [Object.issue,commitsTo,bar,cy]

/-- All three scalar channels have a schedule bound from their trace rows. An unissued
block forces a live producer even if its trace ends before its election or its first issue. -/
theorem lag {Q L m X c} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : ¬HasUb X) (hc : c<L.grid)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y) (o : Object) :
    ∃ τ, LagN (schedule Q L) X (o.loc L c) 0 (·=o.producer L X c) (Waiting L m X o c) τ
      (o.visits (Lib.blocksOf Q L c)) (o.issue (o.loc L c)) := by
  apply Lib.producer_lag _ _ _ _ _ _ (fun j => o.waitSlot (o.blockOf j))
    (mono := o.wait_mono.comp o.block_mono)
  · intro g hn
    obtain ⟨bound,clock⟩ := wait_clock hp hf rows hn
    exact ⟨bound,clock.le⟩
  · intro j bound late
    apply Lib.count_of_occurrences (fun k _ => label o ((X.tr (o.producer L X c)).take k)/o.width)
    intro i
    have ij : i.val≤j := by have := i.isLt; omega
    obtain ⟨k,e,he,prod,tag⟩ := due hp hX hf words hu hc o (o.blockOf i)
      (Object.last_block.mp (ij.trans_lt bound)) (o.at_block _) (late.imp_right
        ((o.wait_mono (o.block_mono ij)).trans ·))
    refine ⟨k,e,he,prod,?_⟩
    rw [tag]
    cases o <;> simp only [Object.blockOf,Object.width,Object.index] <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar

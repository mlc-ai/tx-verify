-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarPoll
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
import Kernels.InklingRelDecode.Proof.Softmax.Export.Time
import Kernels.InklingRelDecode.Proof.Mma.Export.Time

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.Sched MbarRow

def Object.waitSlot (o : Object) (r : Nat) :=
  match o with
  | .score _ => Lib.Slots.scoreWait r | .prob _ => Lib.Slots.probWait r
  | .done => Lib.Slots.doneWait (r+1)

def Object.blockOf (o : Object) (j : Nat) := o.index + o.width*j

theorem Object.block_mono (o : Object) : Monotone o.blockOf := by
  intro a b ab
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ab) _

theorem Object.wait_mono (o : Object) : Monotone o.waitSlot := by
  intro a b ab
  cases o
  · change 1000+400*a+200+64≤1000+400*b+200+64; omega
  · change 1000+400*(a+1)+100+15≤1000+400*(b+1)+100+15; omega
  · change 1000+400*(a+1)+200+70≤1000+400*(b+1)+200+70; omega

theorem Object.at_block (o : Object) (j : Nat) : o=o.atRound (o.blockOf j) := by
  cases o <;> simp only [Object.atRound,Object.blockOf,Object.width,Object.index] <;>
    (congr 1; apply Fin.ext; dsimp [slot2]; omega)

theorem Object.block_visits {o : Object} {r : Nat} (eq : o=o.atRound r) :
    o.blockOf (o.visits r)=r ∧ o.visits r=r/o.width := by
  cases o <;> simp only [Object.atRound,Object.visits,Object.width,Object.index,Object.blockOf] at *
  all_goals first | omega | (
    injection eq with same
    have pos := congrArg Fin.val same
    change _=r%2 at pos; omega)

theorem Object.last_block {o : Object} {N j : Nat} : j<o.visits N ↔ o.blockOf j<N := by
  cases o <;> simp only [Object.visits,Object.width,Object.index,Object.blockOf] <;> omega

def Waiting (L : Launch) (m : Mem0) (X : Execution) (o : Object) (c g : Nat) :=
  ∃ q sc, NextEv L kernel Assumptions.all m X g ⟨o.pc,.wait (o.loc L c) q false true sc⟩

theorem wait_clock {Q L m X c g o} (hp : Pre Q L m) (hf : Follow Q L X)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (wait : Waiting L m X o c g) :
    let j := okPolls (o.loc L c) (X.tr g)
    j<o.visits (Lib.blocksOf Q L c) ∧ o.waitSlot (o.blockOf j)=threadTime (schedule Q L) X g := by
  obtain ⟨q,sc,hn⟩ := wait
  have hg := hn.lt
  obtain ⟨Y,hY,pref,get⟩ := id hn
  obtain ⟨cta,_,pos,_⟩ := wait_obj (rows Y hY) hg get
  have ord := count (rows Y hY) hg o (X.tr g).length
  simp only [roundAt,pref,cta] at pos ord
  have block := (Object.block_visits pos).1
  rw [←ord] at block
  dsimp only
  rw [Object.last_block,block,←cta]
  cases o with
  | score s =>
    exact ⟨Softmax.Export.wait_bound hp hf hn (.inl rfl),
      (Softmax.Export.wait_time hp hf hn (.inl rfl)).symm⟩
  | prob s =>
    obtain ⟨bound,clock⟩ := Mma.Export.wait_time hp hf hn (.inr rfl)
    exact ⟨bound,clock.symm⟩
  | done =>
    have bound := Softmax.Export.wait_bound hp hf hn (.inr rfl)
    change pollRound 2239 (X.tr g)+1<_ at bound
    exact ⟨Nat.lt_of_succ_lt bound,(Softmax.Export.wait_time hp hf hn (.inr rfl)).symm⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar

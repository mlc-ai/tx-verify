-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.SoftFixed
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.Where

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

def mandatory (es : List Event) :=
  es.countP (fun e => e.pc==2241)+es.countP (fun e => e.pc==2251)+
  es.countP (fun e => e.pc==999)+es.countP (fun e => e.pc==1012)

/-- Two plus the number of mandatory loop barriers before the site. A score
wait counts prior rounds. The other rows include the current score receipt. -/
def mandatoryAt (p score : Nat) : Option Nat :=
  let start := 4*(score-1)
  if p=1257 then some (4*score+(if score=0 then 2 else 0))
  else if p=2239 ∨ p=2241 then some start
  else if p=2250 ∨ p=2251 then some (start+1)
  else if p=2252 ∨ p=2255 ∨ p=2326 ∨ p=999 then some (start+2)
  else if p=1012 then some (start+3)
  else if p=1013 then some (start+4)
  else none

private theorem position (s : Site) (i n : Nat)
    (pos : mandatoryAt s.pc (i+s.afterS.toNat)=some n) :
    n=4*i+syncPosition s i := by
  have pre (p : Fin 64) :
      mandatoryAt (Site.pre p).pc i=none ∧ mandatoryAt (Site.nxt p).pc i=none := by
    have outside : ∀ p : Fin 64, ∀ b : Bool,
        let pc := (if b then Site.pre p else Site.nxt p).pc
        pc∉[1257,2239,2241,2250,2251,2252,2255,2326,999,1012,1013] := by decide
    have a := outside p true
    have b := outside p false
    simp only [Bool.false_eq_true,ite_true,ite_false,List.mem_cons,List.not_mem_nil,
      or_false,not_or] at a b
    simp_all [mandatoryAt]
  cases s
  case pre p =>
    change mandatoryAt (Site.pre p).pc i=some n at pos; rw [(pre _).1] at pos; cases pos
  case nxt p =>
    change mandatoryAt (Site.nxt p).pc i=some n at pos; rw [(pre _).2] at pos; cases pos
  all_goals simp [mandatoryAt,Site.pc,Site.afterS,syncPosition] at pos ⊢
  all_goals omega

/-- The round of any listed barrier, poll, store, load or branch shuffle
is recovered solely from prefix counts of trace events. -/
theorem round_barriers {Q L m X g k ev n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ev) (clean : ∀ f, ev.kind≠.ub f)
    (lo : 574<ev.pc) (hi : ev.pc<2331)
    (site : mandatoryAt ev.pc (pollRound 1257 ((X.tr g).take k))=some n) :
    mandatory ((X.tr g).take k)+2=n := by
  have hg := Frame.lt_of_get hX get
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True)
    (fun g hg => thread_sound hp hg) hX get
    (fun _ f eq => clean f (congrArg Event.kind eq))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get hs clean
  obtain ⟨w,ent,d,c,rfl⟩ := (pc ▸ state_role s).softmax lo hi
  have nu := Frame.noUbBefore_of_get hX get
  have ref := (reached_table hf hg nu hs).2
  change Ref _ d (softCounts c) at ref
  have total := soft_fixed_total hp hX (List.getElem?_eq_some_iff.mp get).1.le hs nu
  have score := congrArg Cnt.s ref.ledger
  change c (.poll 1257)=d.i+d.site.afterS.toNat at score
  have count (key : Cls) : c key=((X.tr g).take k).countP (cls key) := fcount hs key
  change ev.pc=d.site.pc at pc
  rw [pc] at site
  rw [count] at score
  change pollRound 1257 ((X.tr g).take k)=_ at score
  rw [score] at site
  have found := position _ _ _ site
  rw [count,count,count,count] at total
  exact total.trans found.symm

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

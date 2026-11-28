-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.Time
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Softmax
import Kernels.InklingRelDecode.Proof.Common.DataDeadline
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Softmax.Producer
import Kernels.InklingRelDecode.Proof.Softmax.Shape

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Frame PTX.Sched

/-- The arrival belongs to the CTA leader. Its per-lane ordinal distinguishes the
successive notifications even when their object addresses coincide. -/
@[expose] public def Published (L : Launch) (X : Execution) (g r : Nat) : Prop :=
  ∃ k, X.get (g,k)=some ⟨1013,.arrive (MbarRow.loc L g (Iface.pReady (MbarRow.slot2 r)))
    0 1 true .cta⟩ ∧ ((X.tr g).take k).countP (fun e => e.pc==1013)=r

public theorem prob_short {Q L m X g r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hu : NoUbLane X g)
    (hg : g<L.threads) (leader : g%L.block=0) (hi : r<Lib.blocksOf Q L (g/L.block))
    (missing : ¬Published L X g r) :
    threadTime (schedule Q L) X g≤Lib.Slots.probArrival r ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
  have issue {w ent d n k e} (get : X.get (g,k)=some e)
      (hs : stateAt (thread Q L) X g k=some (some (softState w ent d n)))
      (site : d.site=.arrive) (iter : d.i=r) : False := by
    have nu (f : Fault) : e.kind≠.ub f := by
      cases e with | mk p kd => rintro rfl; exact hu.kind get f rfl
    obtain ⟨t,ins,o,ht,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX get hs nu
    have pc := event_pcU (fun g h => thread_sound hp h) hX get hs nu
    have ref : Ref _ d (softCounts n) := (reached_table hf hg (noUbBefore_of_get hX get) hs).2
    obtain ⟨s,i,v⟩ := d
    obtain rfl : s=.arrive := site
    change i=r at iter
    subst i
    have shape := object_shape (L := L) (g := g) (e := ent) (i := r) (v := v) (s := .arrive)
      hp ht hc fire
    have eq : e=⟨1013,.arrive (MbarRow.loc L g (Iface.pReady (MbarRow.slot2 r)))
        0 1 true .cta⟩ := by
      cases e; congr 1
    have prev := (fcount hs (.atPc 1013)).symm.trans (congrArg Cnt.p ref.ledger)
    change _ = (if g%L.block%128=0 then r else 0) at prev
    exact missing ⟨k,eq ▸ get,by simpa only [cls,leader,Nat.zero_mod,ite_true] using prev⟩
  apply data_deadline hp hX hu hg (by omega)
    (by unfold Lib.Slots.probArrival Lib.Slots.softmax Lib.Slots.frame; omega)
    (beforeArrival r) ⟨Nat.zero_le _,by decide⟩ (fun _ h => (arrival_clock h).1)
  · intro w ent d n k e get hs old eq
    obtain ⟨site,iter⟩ := (arrival_clock old).2 eq
    exact issue get hs site iter
  · intro w ent d n k e dn get hs old go
    have limit := reached_limit hp hX hg (List.getElem?_eq_some_iff.mp get).1.le hs
    have step := before_arrival_step leader (limit ▸ hi) old (issue get hs) go
    exact ⟨step,step.2⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

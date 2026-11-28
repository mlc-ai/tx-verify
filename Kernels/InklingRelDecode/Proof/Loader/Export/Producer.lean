-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.ElectLead
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerDeadline
import Kernels.InklingRelDecode.Proof.Loader.Producer
import Kernels.InklingRelDecode.Proof.Loader.CopyShape
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.Final
import Lemmas.Flow.TensorIssue
import Lemmas.Flow.NotBulk

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Sched PTX.Flow PTX.Frame

/-- A packet instruction in block r. The number of completed polls identifies
the block even when two different blocks reuse the same ready object. -/
@[expose] public def Issued (Q : Params) (L : Launch) (X : Execution) (g pc r : Nat)
    (kind : Event → Prop) := ∃ k e, X.get (g,k)=some e ∧ e.pc=pc ∧ kind e ∧
      pollRound 2374 ((X.tr g).take k)=r-Iface.preloadCount Q L (g/L.block)+1

private def kind (op : Issue) (Q : Params) (L : Launch) (g r : Nat) (e : Event) : Prop :=
  let obj := Iface.kvReadyLoc L (g/L.block) ⟨r%3,by omega⟩
  match op with
  | .arrival => e.kind=.arrive obj 65536 1 true .cta
  | .copy .. => ∃ sp, e.kind=.tensorIssue Q.kvMap sp ∧ sp.mbar=obj ∧
      TensorTransfer.bytes sp.descriptor=8192

private theorem issue {Q L m X g w x call d n k e r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some e)
    (hs : stateAt (thread Q L) X g k=some (some (workerState w x (.loader call) d n)))
    (nu : ∀ f, e.kind≠.ub f) (op : Issue) (site : d.site=op.site)
    (atBlock : (bits d.counter).toNat=r) (lim : r<2^31) :
    Issued Q L X g op.site.pc r (kind op Q L g r) := by
  have count := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs).2
  obtain ⟨_,_,ord,_⟩ := count
  have p := event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  change e.pc=d.site.pc at p
  rw [site] at p
  obtain ⟨t,ins,o,hat,_,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs nu
  have hc' := (fcount hs (.poll 2374)).symm.trans ord
  obtain ⟨s,i,v,a,b⟩ := d
  change s=op.site at site
  subst s
  refine ⟨k,e,he,p,?_,?_⟩
  · cases op with
    | arrival =>
      have hit := arrive_slot (regs := inputs Q L g (dispatchRegs Q L g w x))
        (w := w) (i := i) (n := v) (a := a) (b := b) hp (atBlock ▸ lim) hat hc fire
      simpa only [kind,←atBlock] using hit
    | copy z half =>
      obtain ⟨guard,dst,coords,code⟩ := copy_instr z half
      obtain rfl := Option.some.inj (hc.symm.trans code)
      have live : ∃ t, o=some t := by
        cases o with
        | some u => exact ⟨_,rfl⟩
        | none =>
          rcases fires_none_ends fire with ⟨f,h⟩|exit
          · exact (nu f h).elim
          · have ret := Lib.ret_pc' code fire exit
            have no : ∀ p b, (Site.copy p b).pc ∉ Lib.retPcs := by decide
            exact (no z half ret).elim
      obtain ⟨u,rfl⟩ := live
      obtain ⟨addr,sp,ev,_,_⟩ := fires_cpTensor_issue fire
      have kd := congrArg Event.kind ev
      obtain ⟨rfl,bar,bytes⟩ := copy_slot (regs := inputs Q L g (dispatchRegs Q L g w x))
        (w := w) (p := z) (half := half) (i := i) (n := v) (a := a) (b := b)
        hp (atBlock ▸ lim) rfl hat code fire kd
      exact ⟨sp,kd,by simpa only [←atBlock] using bar,bytes⟩
  · cases op <;> exact atBlock ▸ hc'

private theorem short {Q L m X g r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (hg : g<L.threads) (warp : g%L.block/32=6)
    (lo : Iface.preloadCount Q L (g/L.block)≤r) (hi : r<Lib.blocksOf Q L (g/L.block))
    (op : Issue) (owns : ∀ e ∈ X.tr g, op.producer L g e)
    (missing : ¬Issued Q L X g op.site.pc r (kind op Q L g r)) :
    threadTime (schedule Q L) X g≤op.slot r ∧ ∀ k p, X.get (g,k)≠some ⟨p,.exit⟩ := by
  have size := Lib.blocksOf_lt hp hg
  apply worker_deadline hp hX words (hu.worker (by omega)) hg (.inl warp) (by
    unfold Issue.slot slotTime Lib.Slots.frame; omega) (op.before r) (fun _ => False)
    (fun _ => trivial) (by omega) (fun _ => Issue.early) (fun _ => False.elim)
  · intro w x call d n k e he hs old eq
    obtain ⟨site,pos⟩ := Issue.at_slot old eq
    have nu (f : Fault) : e.kind≠.ub f := by
      obtain ⟨pc,kd⟩ := e; rintro rfl; exact (hu.worker (by omega)).kind he _ rfl
    exact missing (issue hp hX hf he hs nu op site pos (by omega))
  · intros; contradiction
  · intro w x call d n k e dn he hs nu old step
    obtain ⟨_,ref,_,_⟩ := (reached_table hf hg (noUbBefore_of_get hX he) hs).2
    have next := Issue.before_next step ref size lo hi old (owns e (List.mem_of_getElem? he))
      (fun site pos => missing (issue hp hX hf he hs nu op site pos (by omega)))
    exact ⟨next,by obtain ⟨s,i,v,a,b⟩ := dn; rintro rfl; exact next⟩
  · intros; contradiction

/-- A missing recurrent arrival bounds the producer's clock without a next event.
A producer that has exited issued the arrival in every assigned block. -/
public theorem arrival_short {Q L m X g r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (hg : g<L.threads) (warp : g%L.block/32=6)
    (lane : laneOf L g=0) (lo : Iface.preloadCount Q L (g/L.block)≤r)
    (hi : r<Lib.blocksOf Q L (g/L.block))
    (missing : ¬Issued Q L X g 2378 r fun e =>
      e.kind=.arrive (Iface.kvReadyLoc L (g/L.block) ⟨r%3,by omega⟩) 65536 1 true .cta) :
    threadTime (schedule Q L) X g≤Lib.Slots.readyArrival r ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ :=
  short hp hX hf words hu hg warp lo hi .arrival (fun _ _ => lane) missing

/-- The winning loader owes both copies of each of four pairs per assigned block. -/
public theorem copy_short {Q L m X g r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (hg : g<L.threads) (warp : g%L.block/32=6)
    (wins : ElectLead L g (X.tr g)) (lo : Iface.preloadCount Q L (g/L.block)≤r)
    (hi : r<Lib.blocksOf Q L (g/L.block)) (p : Fin 4) (b : Bool)
    (missing : ¬Issued Q L X g ([2389,2394,2404,2410][p.val]! + (if b then 2 else 0)) r
      fun e => ∃ sp, e.kind=.tensorIssue Q.kvMap sp ∧
        sp.mbar=Iface.kvReadyLoc L (g/L.block) ⟨r%3,by omega⟩ ∧
        TensorTransfer.bytes sp.descriptor=8192) :
    threadTime (schedule Q L) X g≤Lib.Slots.readyCopy r p b ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
  have bound := short hp hX hf words hu hg warp lo hi (.copy p b)
    (fun e mem mask inst lead kd => (wins e mem mask inst lead kd).symm) missing
  have eq : (Issue.copy p b).slot r=Lib.Slots.readyCopy r p b := by
    rfl
  exact ⟨eq ▸ bound.1,bound.2⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export

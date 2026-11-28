-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Mma.Export.Broadcast
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Lemmas.Flow.PollRounds
public import Lemmas.Flow.ElectLead
import Kernels.InklingRelDecode.Proof.Common.WorkerDeadline
import Kernels.InklingRelDecode.Proof.Mma.Producer

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Proof PTX.Flow PTX.Sched PTX.Frame

/-- A commit from block r. The successful wait ordinal distinguishes successive
uses of the same barrier by this lane. -/
@[expose] public def Issued (X : Execution) (g pc wait r : Nat) (obj : Loc) : Prop :=
  ∃ k sp, X.get (g,k)=some ⟨pc,.tc (.commit sp)⟩ ∧ sp.mbar=obj ∧
    pollRound wait ((X.tr g).take k)=r+1

private def waitPc : LoopIssue → Nat | .score => 2462 | .empty | .done => 2510

private theorem short {Q L m X g r} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : NoUbOutside L X) (hg : g<L.threads)
    (warp : g%L.block/32=7) (wins : ElectLead L g (X.tr g)) (hi : r<Lib.blocksOf Q L (g/L.block))
    (op : LoopIssue) (missing : ¬Issued X g op.commit.site.pc (waitPc op) r
      (op.commit.spec L g (op.iter r)).mbar) :
    threadTime (schedule Q L) X g≤op.slot r ∧ ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
  have issue {w x call d n k e} (get : X.get (g,k)=some e)
      (hs : stateAt (thread Q L) X g k=some (some (workerState w x (.mma call) d n)))
      (site : d.site=op.commit.site) (atR : d.i=op.iter r) : False := by
    have nu (f : Fault) : e.kind≠.ub f := by
      cases e with | mk p kd => rintro rfl; exact (hu.worker (by omega)).kind get _ rfl
    obtain ⟨_,_,q,p,-⟩ := (reached_table hf hg (noUbBefore_of_get hX get) hs).2
    obtain ⟨t,ins,o,hat,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX get hs nu
    have pc := event_pcU (fun g h => thread_sound hp h) hX get hs nu
    obtain ⟨s,i,v⟩ := d
    obtain rfl : s=op.commit.site := site
    obtain rfl : i=op.iter r := atR
    have kd := commit_shape (regs := dispatchRegs Q L g w x) (w := w) (v := v)
      hp hg op.commit hat hc fire
    have eq : e=⟨op.commit.site.pc,.tc (.commit (op.commit.spec L g (op.iter r)))⟩ := by
      cases e; congr 1
    apply missing
    refine ⟨k,_,eq ▸ get,rfl,?_⟩
    cases op with
    | score => exact (fcount hs (.poll 2462)).symm.trans q
    | empty | done => exact (fcount hs (.poll 2510)).symm.trans p
  apply worker_deadline hp hX words (hu.worker (by omega)) hg (.inr warp)
    (by unfold LoopIssue.slot slotTime Lib.Slots.mma Lib.Slots.frame; omega)
    (fun _ => False) (op.before r) (by omega) (fun _ => trivial) (fun _ => False.elim)
    (fun _ h => (LoopIssue.cut h).1)
  · intros; contradiction
  · intro w x call d n k e get hs old eq
    obtain ⟨site,atR⟩ := (LoopIssue.cut old).2 eq
    exact issue get hs site atR
  · intros; contradiction
  · intro w x call d n k e dn get hs nu old go
    obtain ⟨machine,_,ref,_⟩ := reached_table hf hg (noUbBefore_of_get hX get) hs
    have next := LoopIssue.before_next go old (fun read => by
      rw [ref_count ref read]; exact ⟨hi,Lib.iter_admitted hp hg⟩)
      (fun m i ld kd => (wins e (List.mem_of_getElem? get) m i ld kd).symm)
      (fun md a b c v ok kd => by
        have src := event_pcU (fun g h => thread_sound hp h) hX get hs nu
        obtain ⟨t,ins,o,_,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hX get hs nu
        have sh : Execution.isShfl e=true := by cases e with | mk p k => cases kd; rfl
        have code := fires_shfl_op fire sh
        have enabled : Lib.canShuffle d.site.pc=true := by simp [Lib.canShuffle,hc,code]
        have pcs (s : Site) : Lib.canShuffle s.pc=true → s.pc=2464 ∨ s.pc=2512 := by
          cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
        cases e with | mk pc k =>
          cases kd
          change pc=d.site.pc at src
          rw [broadcast_seven hp hX hf words warp get (src ▸ pcs d.site enabled)]
          decide)
      (issue get hs) machine.1
    refine ⟨next,?_⟩
    obtain ⟨s,i,v⟩ := dn
    rintro rfl
    exact next

public theorem score_short {Q L m X g r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X)
    (hg : g<L.threads) (warp : g%L.block/32=7) (wins : ElectLead L g (X.tr g))
    (hi : r<Lib.blocksOf Q L (g/L.block))
    (missing : ¬Issued X g 2499 2462 r
      ⟨.shared,g/L.block,L.sharedBase+Iface.sReady ⟨r%2,by omega⟩⟩) :
    threadTime (schedule Q L) X g≤Lib.Slots.scoreCommit r ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ :=
  short hp hX hf words hu hg warp wins hi .score missing

public theorem empty_short {Q L m X g r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X)
    (hg : g<L.threads) (warp : g%L.block/32=7) (wins : ElectLead L g (X.tr g))
    (hi : r<Lib.blocksOf Q L (g/L.block))
    (missing : ¬Issued X g 2546 2510 r
      ⟨.shared,g/L.block,L.sharedBase+Iface.kvEmpty ⟨r%3,by omega⟩⟩) :
    threadTime (schedule Q L) X g≤Lib.Slots.emptyCommit r ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ :=
  short hp hX hf words hu hg warp wins hi .empty missing

public theorem done_short {Q L m X g r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X)
    (hg : g<L.threads) (warp : g%L.block/32=7) (wins : ElectLead L g (X.tr g))
    (hi : r<Lib.blocksOf Q L (g/L.block))
    (missing : ¬Issued X g 2548 2510 r
      ⟨.shared,g/L.block,L.sharedBase+Iface.oDone⟩) :
    threadTime (schedule Q L) X g≤Lib.Slots.doneCommit (r+1) ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ :=
  short hp hX hf words hu hg warp wins hi .done missing

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export

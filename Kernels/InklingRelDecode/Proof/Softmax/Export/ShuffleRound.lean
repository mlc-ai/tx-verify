-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Lib.ShuffleRounds
import Kernels.InklingRelDecode.Proof.Softmax.ShuffleCount
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.Where

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

private theorem score_site (s : Site) (h : s.pc=1257) : s=.waitS := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- At a score poll the shuffles made so far are one for the startup, one for each
preloaded block, and the rounds before the poll's round. -/
public theorem score_shuffles {Q L m X g k l q ok ac sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨1257,.wait l q ok ac sc⟩) :
    ((X.tr g).take k).countP Execution.isShfl=
      1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase (pollRound 1257 ((X.tr g).take k)) := by
  have clean : ∀ f, (Event.mk 1257 (.wait l q ok ac sc)).kind≠.ub f := fun _ => nofun
  have hg := Frame.lt_of_get hX get
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True)
    (fun g hg => thread_sound hp hg) hX get
    (fun _ f h => clean f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get hs clean
  have pc' : (thread Q L g).pc s=1257 := pc.symm
  obtain ⟨w,ent,d,c,rfl⟩ := (state_role s).softmax (by omega) (by omega)
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  have ref := (reached_table hf hg nu hs).2
  change Ref _ d (softCounts c) at ref
  have total := shfl_ordinal hp hX len hs nu
  have score := congrArg Cnt.s ref.ledger
  change c (.poll 1257)=d.i+d.site.afterS.toNat at score
  have count (key : Cls) : c key=((X.tr g).take k).countP (cls key) := fcount hs key
  change 1257=d.site.pc at pc
  have site : d.site=.waitS := score_site _ pc.symm
  rw [count] at score total
  have waitS : d.site.afterS.toNat=0 := by rw [site]; rfl
  rw [waitS] at score
  change pollRound 1257 ((X.tr g).take k)=d.i+0 at score
  have inRound : shflInRound d.site d.i=0 := by rw [site]; rfl
  simp only [shflCount,inRound,Nat.add_zero] at total
  rw [score]
  exact total

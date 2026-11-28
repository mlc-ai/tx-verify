-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataStart
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Prologue.HistoryNext
public import Kernels.InklingRelDecode.Proof.Softmax.RefNext
public import Kernels.InklingRelDecode.Proof.Epilogue.RefNext
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

def softRef {ent L g} (s : (softCode ent L g).D) (n : Cls → Nat) : Prop :=
  match s with
  | .inl d => Softmax.Ref (g%L.block) d (softCounts n) ∧ n (.poll 2565)=0
  | .inr ⟨_,d⟩ => Epilogue.Ref d (n (.poll 2565))

def dataRef {Q L g w} (s : (dataCode Q L g w).D) (n : Cls → Nat) : Prop :=
  match s with
  | .inl d => Prologue.History Q L g d (proCounts L g n) ∧
    softCounts n=⟨0,0,0⟩ ∧ n (.poll 2565)=0
  | .inr ⟨_,s⟩ => softRef s n

private theorem soft_enter {ent L g n} (d : Softmax.Control.D)
    (ref : Softmax.Ref (g%L.block) d (softCounts n)) (zero : n (.poll 2565)=0) :
    softRef (Code.enter (Softmax.Control.code ent L g)
      (fun _ : Unit => Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit d) n := by
  by_cases ex : d.site=.epilogue
  · simpa [Code.enter,epiExit,ex,softRef,zero] using Epilogue.ref_init
  · simpa only [Code.enter,epiExit,ex,↓reduceIte,softRef] using And.intro ref zero

private theorem pro_enter {Q L g w n} (d : Prologue.Control.D)
    (hist : Prologue.History Q L g d (proCounts L g n)) (clear : softCounts n=⟨0,0,0⟩)
    (final : n (.poll 2565)=0) :
    dataRef (Code.enter (Prologue.Control.checkedCode Q L g w) (fun ent => softCode ent L g)
      (dataExit Q L g w) d) n := by
  by_cases ex : d.site=.exit
  · simp only [Code.enter,dataExit,ex,↓reduceIte,dataRef]
    change @softRef (dataEntry Q L g w d) L g (softCode (dataEntry Q L g w d) L g).init n

    exact ⟨clear ▸ Softmax.initial_ref _,final⟩
  · simpa only [Code.enter,dataExit,ex,↓reduceIte,dataRef] using And.intro hist ⟨clear,final⟩

private theorem poll_off {p ev} (ne : ev.pc≠p) : okPollAt p ev=false := by
  cases ev with | mk pc kd =>
    cases kd <;> try rfl
    rename_i yes _ _
    cases yes <;> simp_all [okPollAt]

theorem data_ref_next {Q L m X g k w s n ev sn} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ev) (hu : ∀ f, ev.kind≠.ub f)
    (hs : stateAt (thread Q L) X g k=some (some (.inr ⟨.inl (.prologue w),s⟩,n)))
    (old : dataRef s n) (move : (dataCode Q L g w).next s ev=some (some sn)) :
    dataRef sn (Code.bump cls n ev) := by
  obtain ⟨t,ins,o,ht,inv,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs hu
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs hu
  rcases s with d|⟨ent,s⟩
  · obtain ⟨dn,step,rfl⟩ := Code.glue_inl_some move
    obtain ⟨hist,clear,final⟩ := old
    change ev.pc=d.site.pc at pc
    have small (s : Prologue.Site) (h : s≠.exit) : s.pc<574 := by
      revert h
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    have live : d.site≠.exit := by
      intro ex
      have h : dataExit Q L g w d=none := inv.2
      simp [dataExit,ex] at h
    have hi := pc ▸ small d.site live
    have stay (p : Nat) (big : 574≤p) : Code.bump cls n ev (.poll p)=n (.poll p) := by
      simp [Code.bump,cls,poll_off (show ev.pc≠p by omega)]
    apply pro_enter
    · rw [pro_count_bump]
      exact Prologue.history_next hp hX he ht hc fire pc hi hist step
    · simpa only [softCounts,poll_off (show ev.pc≠1257 by omega),
        poll_off (show ev.pc≠2239 by omega),
        Code.bump,cls,show (ev.pc==1013)=false from beq_eq_false_iff_ne.mpr (by omega),
        Bool.false_eq_true,↓reduceIte,Nat.add_zero] using clear
    · exact (stay 2565 (by decide)).trans final
  · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some move
    rcases s with d|⟨_,d⟩
    · obtain ⟨dn,localStep,rfl⟩ := Code.glue_inl_some step
      obtain ⟨ref,final⟩ := old
      change ev.pc=d.site.pc at pc
      have clear (s : Softmax.Site) (h : s≠.epilogue) : s.pc≠2565 := by
        revert h
        cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
      have live : d.site≠.epilogue := by
        intro ex
        have h : epiExit d=none := inv.2
        simp [epiExit,ex] at h
      have bump (c) : Code.bump cls n ev c=n c+(cls c ev).toNat := by
        unfold Code.bump
        cases cls c ev <;> rfl
      apply soft_enter
      · simpa only [softCounts,Softmax.Cnt.bump,bump,cls] using
          Softmax.ref_next inv.1 ref pc localStep
      · simp [bump,cls,poll_off (pc ▸ clear d.site live),final]
    · obtain ⟨dn,localStep,rfl⟩ := Code.glue_inr_some step
      have next := Epilogue.ref_next old pc localStep
      change Epilogue.Ref dn (n (.poll 2565) + (if okPollAt 2565 ev then 1 else 0))
      cases hh : okPollAt 2565 ev <;> simpa [hh] using next

end PTX.Kernels.InklingRelDecode.Proof

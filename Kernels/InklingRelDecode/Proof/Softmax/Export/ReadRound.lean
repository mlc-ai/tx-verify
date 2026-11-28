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
import Kernels.InklingRelDecode.Proof.Common.SoftSite

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow

private theorem load_site (s : Site) (h : s.pc=2252) : s=.ldL := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- At a scratch read the round, the score polls made and the shuffles made are tied. -/
private theorem read_facts {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨2252,.rd a bs⟩) :
    ∃ i, 0 < i ∧ pollRound 1257 ((X.tr g).take k)=i+1 ∧
      ((X.tr g).take k).countP Execution.isShfl=
        1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase i+7 := by
  have clean : ∀ f, (Event.mk 2252 (.rd a bs)).kind≠.ub f := fun _ => nofun
  have hg := Frame.lt_of_get hX get
  obtain ⟨w,ent,d,c,hs,pc⟩ := at_site hp hX get clean (by show 574<2252; decide)
    (by show 2252<2331; decide)
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  have ref := (reached_table hf hg nu hs).2
  change Ref _ d (softCounts c) at ref
  have total := shfl_ordinal hp hX len hs nu
  have score := congrArg Cnt.s ref.ledger
  change c (.poll 1257)=d.i+d.site.afterS.toNat at score
  have count (key : Cls) : c key=((X.tr g).take k).countP (cls key) := fcount hs key
  have site : d.site=.ldL := load_site _ pc.symm
  have prev : 0<d.i := shfl_previous hp hX len hs nu (by rw [site]; rfl)
  rw [count] at score total
  have after : d.site.afterS.toNat=1 := by rw [site]; rfl
  rw [after] at score
  have inRound : shflInRound d.site d.i=7 := by rw [site]; rfl
  simp only [shflCount,inRound] at total
  change ((X.tr g).take k).countP Execution.isShfl=_ at total
  exact ⟨d.i,prev,score,by omega⟩

/-- Two scratch reads of data lanes of one CTA with the same number of earlier shuffles are in
the same round of the loop. -/
public theorem read_round {Q L m X g k h j a bs a' bs'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (one : X.get (g,k)=some ⟨2252,.rd a bs⟩) (two : X.get (h,j)=some ⟨2252,.rd a' bs'⟩)
    (cta : g/L.block=h/L.block)
    (count : ((X.tr g).take k).countP Execution.isShfl=((X.tr h).take j).countP Execution.isShfl) :
    pollRound 1257 ((X.tr g).take k)=pollRound 1257 ((X.tr h).take j) := by
  obtain ⟨i,pos,round,shfl⟩ := read_facts hp hX hf one
  obtain ⟨i',pos',round',shfl'⟩ := read_facts hp hX hf two
  rw [cta] at shfl
  have : Lib.shflBase i=Lib.shflBase i' := by omega
  have : i=i' := by
    unfold Lib.shflBase at this
    split at this <;> split at this <;> omega
  rw [round,round',this]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

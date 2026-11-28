-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Publication
public import Lemmas.Kernel.Safety.Handoff
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.HandoffPhased
import Lemmas.Protocol.NamedBarExitCycle
import Lemmas.Kernel.Frame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame

theorem participant {Q L m} (hp : Pre Q L m) (g : Nat) :
    (g%L.block)/32 ∈ Finset.range (CtaBarrier.warps L.block) := by
  simp only [Finset.mem_range,CtaBarrier.warps,hp.block]
  omega

theorem sources {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    NamedBar.Sources L X none (Finset.range (CtaBarrier.warps L.block)) 1 :=
  fun _ _ _ ⟨_,he⟩ _ => ⟨participant hp _,(Lib.publication_kind hX hp.block he).1⟩

theorem shape {Q L m} (hp : Pre Q L m) :
    NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) 1 := by
  refine ⟨by simp [CtaBarrier.warps,hp.block],?_,?_,by decide⟩
  · rw [Finset.card_range]; rfl
  · intro w h
    simpa [CtaBarrier.warps,hp.block] using h

/-- Every write of either publication in the prologue happens before every
later worker read of the same CTA. Later writes to these addresses require a
separate reuse argument. -/
theorem publish_before_read {Q L m X g h j k p r a b bs data}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (store : X.get (g,j) = some ⟨p,.wr a bs⟩) (pub : p=570 ∨ p=571)
    (read : X.get (h,k) = some ⟨r,.rd b data⟩) (worker : r=2340 ∨ r=2345 ∨ r=2423)
    (cta : g/L.block = h/L.block) : baseCausality L X (g,j) (h,k) := by
  have hand := Handoff.of_bar_upTo hX (sources hp hX) (shape hp) (syncs := fun _ => True)
    (fun _ _ _ _ _ _ he => (Lib.publication_kind hX hp.block he).2) 1
    (fun _ _ _ ⟨_,_,he⟩ => Export.publication_exit hp hX he)
  have zero : Export.publishedAt p = some 0 := by rcases pub with rfl|rfl <;> rfl
  have writer := Export.publication_store hp hX store zero
  have reader := Export.publication_read hp hX read worker
  apply hand g h j k
    ⟨⟨Frame.lt_of_get hX store,Frame.lt_of_get hX read,cta⟩,participant hp g,trivial⟩
    (List.getElem?_eq_some_iff.mp read).1
  change ((X.tr g).take (j+1)).countP _ < min (((X.tr h).take k).countP _) 1
  rw [List.take_add_one,show (X.tr g)[j]? = _ from store,List.countP_append,writer]
  change 0 < min (((X.tr h).take k).countP (Execution.isBarId 1)) 1
  omega

/-- A first-round read precedes a reuse unless the reader's exit itself witnessed
the release of the reuser's second synchronization. The exceptional case exposes
the actual release and exit events for the final-barrier cycle argument. -/
theorem read_before_reuse_or_exit {Q L m X g h j k p r a b bs data}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (read : X.get (g,j) = some ⟨r,.rd a data⟩)
    (first : ((X.tr g).take j).countP (Execution.isBarId 1) = 1)
    (store : X.get (h,k) = some ⟨p,.wr b bs⟩) (reuse : p=2250 ∨ p=2848)
    (cta : g/L.block = h/L.block) :
    baseCausality L X (g,j) (h,k) ∨
      ∃ v u pc pc', u<k ∧ X.get (g,v)=some ⟨pc,.exit⟩ ∧
        X.get (h,u)=some ⟨pc',.bar 1 none .sync⟩ ∧
        ((X.tr h).take u).countP (Execution.isBarId 1)=1 ∧
        Witness L X (.thread (g,v)) (h,u) := by
  have phase : 2 ≤ ((X.tr h).take k).countP (Execution.isBarId 1) := by
    rcases reuse with rfl|rfl
    · exact (Export.publication_store hp hX store (phase := 2) rfl).ge
    · have := Export.publication_store hp hX store (phase := 3) rfl
      omega
  obtain ⟨u,pc,cnt,md,uk,sync,ord⟩ := nth_bar (q := 1) phase
  obtain ⟨rfl,rfl⟩ := Lib.publication_kind hX hp.block sync
  have len : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp store).1
  have passed : u+1<(X.tr h).length := by omega
  have same : SameCta L g h := ⟨Frame.lt_of_get hX read,Frame.lt_of_get hX store,cta⟩
  rcases (sources hp hX).arrival_or_exit hX (shape hp) (f := (h,u)) sync passed cta
    (participant hp g) with ⟨i,pc',mode,arr,idx⟩ | ⟨⟨_,v⟩,pc',rfl,ex,wit⟩
  · left
    refine (sources hp hX).arrive_sync_baseCausality hX (shape hp) same arr sync
      passed idx ?_ uk len
    by_contra! le
    have bound := Handoff.countP_take_succ_ge (e := j) arr
      (by rfl : Execution.isBarId 1 ⟨pc',.bar 1 none mode⟩ = true) le
    rw [List.take_add_one,show (X.tr g)[j]? = _ from read,List.countP_append,first] at bound
    change ((X.tr g).take i).countP (Execution.isBarId 1) + 1 ≤ 1+0 at bound
    change ((X.tr g).take i).countP _ = ((X.tr h).take u).countP _ at idx
    omega
  · exact .inr ⟨v,u,pc',pc,uk,ex,sync,ord,wit⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared

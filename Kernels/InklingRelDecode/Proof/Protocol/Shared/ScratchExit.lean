-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchPublish
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Lemmas.Protocol.NamedBarGenLedger
import Lemmas.Kernel.Safety.HandoffPhased
import Lemmas.Flow.NthEv
import Lemmas.Kernel.Frame
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame PTX.CtaBarrier

private theorem count_record {L m X key i pc cnt} (hX : Consistent L kernel Assumptions.all m X)
    (keyed : CtaBarK L X i key) (bar : X.IsBarrier i 0 cnt pc) :
    ∃ j s w lanes, (X.barriers (i.1/L.block))[j]?=some (.arrival 0 w cnt lanes) ∧
      At L.block (X.barriers (i.1/L.block)) j s ∧ (s.slots 0).generation=key/16 := by
  obtain ⟨lt,⟨_,_,get⟩,gen⟩ := keyed
  have eq := (Kind.bar.inj (Event.mk.inj (Option.some.inj (get.symm.trans bar))).2).1
  rw [eq] at gen
  obtain ⟨j,s,w,c,lanes,t,lookup,atJ,mem,phase,_⟩ := gen
  obtain ⟨_,_,p,mode,actual⟩ := (hX.ctaBar.2 _ (NamedBar.cta_lt lt)).2.1 _
    (List.mem_of_getElem? lookup) (t,i) mem
  have same := (Kind.bar.inj (Event.mk.inj (Option.some.inj (actual.symm.trans bar))).2).2.1
  exact ⟨j,s,w,lanes,same ▸ lookup,atJ,phase⟩

/-- Data peers at the same ordinal requested the same warp count. -/
theorem peer_target {Q L m X g h i j p q c d u v} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (one : X.IsBarrier (g,i) 0 c p) (last : X.IsBarrier (h,j) 0 d q)
    (passed : j+1<(X.tr h).length) (lg : g%L.block<128) (lh : h%L.block<128)
    (cta : g/L.block=h/L.block) (ord : barOrdinal X g i=barOrdinal X h j)
    (first : target L.block c=.ok u) (second : target L.block d=.ok v) : u=v := by
  obtain ⟨key,_,a,b,_⟩ := NamedBar.D_same_key (e := (g,i)) (f := (h,j)) hX
    (Export.barZeroSources hp hX)
    (by simp [warps,hp.block]) (Finset.card_range _) (by simp [warps,hp.block])
    (by simp [target])
    ⟨lt_of_get (g := g) (k := i) hX one,lt_of_get (g := h) (k := j) hX last,cta⟩ one last passed
    (Finset.mem_range.mpr (by dsimp; omega)) (Finset.mem_range.mpr (by dsimp; omega)) ord
  obtain ⟨i',s,w,ls,ai,asi,agi⟩ := count_record hX a one
  obtain ⟨j',t,v,ms,bj,btj,bgj⟩ := count_record hX b last
  dsimp only at ai asi bj btj
  rw [cta] at ai asi
  obtain ⟨_,_,_,run⟩ := hX.ctaBar.2 _ (NamedBar.cta_lt b.1)
  exact NamedBar.GenLedger.same_gen_target run ai asi agi bj btj bgj first second

/-- A counted data rendezvous cannot share its ordinal with a released final
full-CTA rendezvous. Both would be records of one generation whose requested
warp counts are respectively four and eight. -/
private theorem full_peer {Q L m X g h i j p q c} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (one : X.IsBarrier (g,i) 0 c p) (last : X.IsBarrier (h,j) 0 none q)
    (passed : j+1<(X.tr h).length) (lg : g%L.block<128) (lh : h%L.block<128)
    (cta : g/L.block=h/L.block) (ord : barOrdinal X g i=barOrdinal X h j) : c=none := by
  obtain ⟨_,bad|full|half⟩ := Lib.recorded_bar hX hp.block one
  · cases bad.1
  · exact full.2.1
  · have cn : c=some 128 := by simpa [BarRow.recCnt,hp.block] using half.2.1
    subst c
    have clash := peer_target hp hX one last passed lg lh cta ord
      (show target L.block (some 128)=.ok 4 by rw [hp.block]; rfl)
      (show target L.block none=.ok 8 by rw [hp.block]; rfl)
    contradiction

/-- Every data peer which has exited has passed more barrier-zero instances than any data lane
has before an event that precedes the final rendezvous in control flow, even if that lane has
since exited as well. The final generation cannot be an earlier counted generation. -/
theorem exit_ordinal {Q L m X g h k v pc e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some e) (nu : ∀ f, e.kind≠.ub f) (early : Lib.afterFinal e.pc=0)
    (other : Lib.finalSync e.pc=false) (ex : X.get (h,v)=some ⟨pc,.exit⟩)
    (lg : g%L.block<128) (lh : h%L.block<128) (cta : g/L.block=h/L.block) :
    barOrdinal X g k < barOrdinal X h v := by
  obtain ⟨j,q,jv,last,late⟩ := Export.exit_final_bar hp hX ex
  have mono := Flow.countP_take_mono (Execution.isBarId 0) (X.tr h) (Nat.succ_le_of_lt jv)
  rw [List.take_add_one,show (X.tr h)[j]?=_ from last,List.countP_append] at mono
  change barOrdinal X h j+1≤barOrdinal X h v at mono
  by_contra! le
  obtain ⟨i,p,c,mode,ik,one,ord⟩ := nth_bar (mono.trans le)
  obtain ⟨rfl,_⟩ := Lib.recorded_bar hX hp.block one
  have pass : j+1<(X.tr h).length := by
    have vv : v<(X.tr h).length := (List.getElem?_eq_some_iff.mp ex).1
    omega
  obtain rfl := full_peer hp hX one last pass lg lh cta ord
  have sooner := Export.before_final_sync hp hX one (ord ▸ late) get nu early other
  omega

/-- Every data peer which has exited has passed more barrier-zero instances
than any data lane has before its scratch read, even if that reader has since
exited as well. -/
theorem scratch_exit_ordinal {Q L m X g h k v pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩) (ex : X.get (h,v)=some ⟨pc,.exit⟩)
    (lg : g%L.block<128) (lh : h%L.block<128) (cta : g/L.block=h/L.block) :
    barOrdinal X g k < barOrdinal X h v :=
  exit_ordinal hp hX read (by simp) rfl rfl ex lg lh cta

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared

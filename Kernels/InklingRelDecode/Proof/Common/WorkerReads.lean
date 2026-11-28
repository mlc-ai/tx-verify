-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.WorkerCall
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Lib.CountLoad
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Loader.RefNext
public import Kernels.InklingRelDecode.Proof.Loader.PageValue
public import Kernels.InklingRelDecode.Proof.Mma.RefNext
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.AllocTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Proof

theorem loader_response {Q L m X g k w x r d n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (pair : CountBytes Q L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (workerState w x (.loader r) d n))) :
    Loader.PairResponse (Iface.preloadCount Q L (g/L.block)) (iterCount Q L (g/L.block))
      d.site ev := by
  have atRead (site : d.site=.first ∨ d.site=.second) {a bs} (kind : ev.kind=.rd a bs) :
      bs=(b32 (if d.site=.second then iterCount Q L (g/L.block)
        else Iface.preloadCount Q L (g/L.block))).toBytes.map some := by
    obtain ⟨t,ins,o,ht,_,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs
      (by rw [kind]; simp)
    have pos : d.site.pc=2345 := by rcases site with h|h <;> rw [h] <;> rfl
    change kernel.code[d.site.pc]?=some ins at hc
    change Fires d.site.pc _ ev o at fire
    rw [pos] at hc fire
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2345)
    change Fires 2345 (eventTmpl Assumptions.all L g t (.mem (Lib.countLoad 2345))) ev o at fire
    have eq : ev=⟨2345,.rd a bs⟩ := by
      have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by rw [kind]; simp)
      change ev.pc=d.site.pc at pc
      rw [pos] at pc
      cases ev; congr
    obtain ⟨j,_,loc,val⟩ := pair (eq ▸ he) (.inl rfl)
    rw [eq] at fire
    generalize Assumptions.all = A at fire
    have read := @Lib.count_load_shape A L g t 2345 a bs o Q m hp (.inl rfl)
    generalize eventTmpl A L g t (.mem (Lib.countLoad 2345)) = tmpl at read fire
    obtain ⟨addr,_⟩ := read fire
    obtain ⟨_,sub,_,_,_⟩ := ht
    change t.sub=(if d.site=.second then 1 else 0) at sub
    have same := congrArg Loc.addr (addr.symm.trans loc)
    change L.sharedBase+212992+4*t.sub=L.sharedBase+212992+4*j.val at same
    by_cases second : d.site=.second
    · have nonzero : j≠0 := by simp [second] at sub; intro z; subst j; simp_all
      simpa [second,nonzero,iterCount] using val
    · have zero : j=0 := Fin.ext (by simp [second] at sub; omega)
      simpa [second,zero] using val
  unfold Loader.PairResponse
  split
  · rename_i ss kk
    simpa [ss] using atRead (.inl ss) kk
  · rename_i ss kk
    simpa [ss] using atRead (.inr ss) kk
  · trivial

/-- A block-table load of the loader returns the page of an existing slab. -/
theorem loader_page_response {Q L m X g k w x r d n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ev)
    (hs : stateAt (thread Q L) X g k = some (some (workerState w x (.loader r) d n)))
    (ref : Loader.Ref (Iface.preloadCount Q L (g/L.block)) (iterCount Q L (g/L.block)) d) :
    Loader.PageResponse (Lib.PageAt Q ((L.ctaidOf (g/L.block)).get .z)
      ((L.ctaidOf (g/L.block)).get .x)) d ev := by
  unfold Loader.PageResponse
  split
  · rename_i u a bs ss kk
    intro v hv
    have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by rw [kk]; simp)
    obtain ⟨t,ins,o,ht,_,hc,fire⟩ := fired_siteU (fun g hg => thread_sound hp hg) hX he hs
      (by rw [kk]; simp)
    change ev.pc = d.site.pc at pc
    have eq : ev = ⟨d.site.pc, .rd a bs⟩ := by cases ev; congr
    rw [eq] at he fire
    have := Loader.page_read hp hX (lt_of_get hX he) he ht hc fire rfl ref
      (by rw [ss]; cases u <;> simp [Loader.Site.pc]) hv
    rw [ss] at this
    cases u <;> simpa [Loader.Site.pc] using this
  · trivial

theorem mma_response {Q L m X g k w x r d n ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (pair : CountBytes Q L X)
    (he : X.get (g,k)=some ev) (hs : stateAt (thread Q L) X g k =
      some (some (workerState w x (.mma r) d n))) (site : d.site=.ldNum)
    {a bs v} (kind : ev.kind=.rd a bs) (rebuilds : rebuild 3 bs=.ok v) :
    Mma.readsCount v (iterCount Q L (g/L.block)) := by
  have pc := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by rw [kind]; simp)
  change ev.pc=d.site.pc at pc
  rw [site] at pc
  have eq : ev=⟨2423,.rd a bs⟩ := by cases ev; congr
  obtain ⟨j,second,_,val⟩ := pair (eq ▸ he) (.inr rfl)
  obtain rfl := second rfl
  simp only [Fin.isValue,one_ne_zero,↓reduceIte] at val
  rw [val,rebuild_b32] at rebuilds
  cases rebuilds
  have bound := Lib.blocksOf_lt hp (lt_of_get hX he)
  refine ⟨rfl,?_⟩
  simp [Mma.low,Value.regBits,b32,truncBits,iterCount]
  omega

end PTX.Kernels.InklingRelDecode.Proof

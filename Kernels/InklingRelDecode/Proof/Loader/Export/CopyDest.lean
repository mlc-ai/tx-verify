-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Kernels.InklingRelDecode.Proof.Iface.CopyIndex
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Loader.CopyFoot
import Kernels.InklingRelDecode.Proof.Loader.CopyShape
import Kernels.InklingRelDecode.Proof.Lib.IterRange

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof

private def packetPcs : List Nat := [2389,2391,2394,2396,2404,2406,2410,2412]

private theorem not_mma (s : Mma.Site) : s.pc ∉ packetPcs := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- A tensor load of the worker routine is issued by a loader warp. -/
public theorem copy_warp {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) : g%L.block/32=6 := by
  have range : 2344<pc ∧ pc<2422 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,x,r,d,n,hs,inv⟩ := worker_event hp hX hf he (by simp) (by change 2344<pc; omega)
    (by change pc<2557; omega) (by change pc≠2422; omega)
  cases r with
  | loader => exact inv.1
  | mma =>
    have ep := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    change pc=d.site.pc at ep
    exact (not_mma _ (ep ▸ site)).elim

/-- **A loader copy lands in one ring slot**: the copy of a worker site on the ready barrier
of slot `s` of its CTA writes only bytes of that CTA's slot `s`. The counter is below `2^31`,
so the tile is slot `counter % 3` rather than the signed remainders the footprint alone
allows. -/
public theorem copy_dest {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) :
    ∃ s : Fin 3, sp.mbar=Iface.kvReadyLoc L (g/L.block) s ∧
      ∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
        l.cta=g/L.block ∧ Iface.InSlot L s.val l.addr ∧
        L.sharedBase+32768*s.val+Iface.copyOff pc ≤ l.addr ∧
        l.addr < L.sharedBase+32768*s.val+Iface.copyOff pc+8192 := by
  have warp := copy_warp hp hX hf he site
  have range : 2344<pc ∧ pc<2422 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,x,⟨s,i,n,a,b⟩,t,ins,o,hat,hpc,hc,fire,hr,_⟩ :=
    loader_event hp hX hf warp he (by simp) range.1 range.2
  change pc=s.pc at hpc
  obtain ⟨p,half,rfl⟩ := copy_site s (hpc ▸ site)
  have lim := Lib.iter_range hp (Frame.lt_of_get hX he)
  have small : (bits i).toNat<2^31 :=
    ref_counter_lt hr (by rfl) lim
  obtain ⟨_,hmbar,_⟩ := copy_slot (regs := Loader.inputs Q L g (dispatchRegs Q L g w x))
    (w := w) hp small rfl hat hc fire rfl
  obtain ⟨_,_,slot,_⟩ := copy_footprint (regs := Loader.inputs Q L g (dispatchRegs Q L g w x))
    (w := w) hp rfl hat hc fire rfl
  have off : boxOffset p half = Iface.copyOff (Site.copy p half).pc := by
    fin_cases p <;> cases half <;> rfl
  refine ⟨⟨(bits i).toNat%3,by omega⟩,hmbar,fun byte => ?_⟩
  obtain ⟨cta,inslot,lo,hi⟩ := slot small byte
  rw [off, ← hpc] at lo hi
  exact ⟨cta,inslot,lo,hi⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export

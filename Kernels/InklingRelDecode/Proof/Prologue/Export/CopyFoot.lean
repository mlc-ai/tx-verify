-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Prologue.CopyFoot
import Kernels.InklingRelDecode.Proof.Prologue.ShapeCopy
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Prologue.History
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Kernels.InklingRelDecode.Proof.Iface.PreloadBox
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.RawArith

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof

private def sites : List Nat := [211,217,226,231,253,259,268,273,295,301,310,315]

private theorem issue_site (s : Site) : s.pc ∈ sites → ∃ b j, s=.ptc b j := by
  cases s <;> first | exact fun _ => ⟨_,_,rfl⟩ |
    (repeat' first | decide +kernel | (rename_i j; revert j))

private theorem preload_core {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [211,217,226,231,253,259,268,273,295,301,310,315]) :
    (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ ∧
    (∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
      L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608) ∧
    ∃ b : Fin 3, sp.mbar=Iface.kvReadyLoc L (g/L.block) b ∧
      ∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
        l.cta=g/L.block ∧ Iface.InSlot L b.val l.addr := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change pc=_ at pos
  have region : 27<pc ∧ pc<574 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,d,n,rfl⟩ := (pos ▸ state_role s).prologue region.1 region.2
  change pc=d.site.pc at pos
  change pc ∈ sites at site
  obtain ⟨b,j,kind⟩ := issue_site d.site (pos ▸ site)
  obtain ⟨_,_,_,hat,_,fetch,step⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  obtain ⟨_,_,kd,bar,_⟩ := copy_shape hp hat b j kind fetch step rfl
  obtain ⟨-,rfl⟩ := Kind.tensorIssue.inj kd
  obtain ⟨desc,foot,slot,_⟩ := preload_footprint hp hat b j kind fetch step rfl
  exact ⟨desc,foot,b,bar,slot⟩

/-- Every byte of a prologue preload is below the query tile, before either
publication is consumed and independently of all tensor source coordinates. -/
public theorem preload_map {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [211,217,226,231,253,259,268,273,295,301,310,315]) :
    (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ ∧
    ∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
    L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608 := by
  obtain ⟨desc,foot,_⟩ := preload_core hp hX he site
  exact ⟨desc,foot⟩

/-- **A prologue preload lands in one ring slot**: the copy of a preload site on the ready
barrier of slot `b` of its CTA writes only bytes of that CTA's slot `b`. -/
public theorem preload_dest {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [211,217,226,231,253,259,268,273,295,301,310,315]) :
    ∃ b : Fin 3, sp.mbar=Iface.kvReadyLoc L (g/L.block) b ∧
      ∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
        l.cta=g/L.block ∧ Iface.InSlot L b.val l.addr := by
  obtain ⟨_,_,dest⟩ := preload_core hp hX he site
  exact dest

public theorem preload_byte {Q L m X g k pc addr sp x y z l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [211,217,226,231,253,259,268,273,295,301,310,315])
    (byte : TensorCopy.writeLoc sp x y z=some l) :
    L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+196608 :=
  (preload_map hp hX he site).2 byte

/-- **A preload copy site is visited once per thread**: no earlier event of the thread is at
the copy's position. -/
public theorem preload_fresh {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩) (site : pc ∈ Iface.preloadSites) :
    ((X.tr g).take k).countP (fun e => e.pc==pc)=0 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pos := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change pc=_ at pos
  have region : 27<pc ∧ pc<574 := by
    simp only [Iface.preloadSites,List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,d,n,rfl⟩ := (pos ▸ state_role s).prologue region.1 region.2
  change pc=d.site.pc at pos
  change pc ∈ sites at site
  obtain ⟨b,j,kind⟩ := issue_site d.site (pos ▸ site)
  obtain ⟨-,hist⟩ := (reached_table hf hg (Frame.noUbBefore_of_get hX he) hs).2
  have bounds : ∀ b j, 130≤ptcPc b j ∧ ptcPc b j≤315 := by decide +kernel
  have fresh := hist.visits.fresh (ptcPc b j) (bounds b j).1 (bounds b j).2 (by rw [kind]; rfl)
  have count : n (.atPc pc)=((X.tr g).take k).countP (fun e => e.pc==pc) := fcount hs _
  rw [←count]
  have : pc=ptcPc b j := by rw [pos,kind]; rfl
  subst this
  exact fresh

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

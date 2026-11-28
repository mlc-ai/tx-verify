-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Loader.CopyFoot

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Proof

private def packetPcs : List Nat := [2389,2391,2394,2396,2404,2406,2410,2412]

private theorem packet (s : Loader.Site) :
    s.pc ∈ packetPcs → ∃ p half, s=.copy p half := by
  cases s <;> first | exact fun _ => ⟨_,_,rfl⟩ |
    (repeat' first | decide +kernel | (rename_i j; revert j))

/-- Every destination byte from the worker's eight tensor loads misses both
shared publications, including in executions with arbitrary dispatch and count reads. -/
public theorem copy_map {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) :
    (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ ∧
    ∀ {x y z l}, TensorCopy.writeLoc sp x y z=some l →
    l.addr<L.sharedBase+196608 ∨ L.sharedBase+213340≤l.addr := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have ep := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change pc=_ at ep
  have range : 2344<pc ∧ pc<2422 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at site
    omega
  obtain ⟨w,v,r,d,n,rfl⟩ := (ep ▸ state_role s).worker range.1 (by omega) (by omega)
  cases r with
  | mma =>
    have miss (s : Mma.Site) : s.pc ∉ packetPcs := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    change pc=d.site.pc at ep
    exact (miss _ (ep ▸ site)).elim
  | loader =>
    change pc=d.site.pc at ep
    obtain ⟨p,half,spos⟩ := packet _ (ep ▸ site)
    obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
      (by simp)
    obtain ⟨s,i,n,a,b⟩ := d
    dsimp only at spos
    subst s
    obtain ⟨desc,foot,_⟩ := copy_footprint hp rfl ht hc fire rfl
    exact ⟨desc,foot⟩

public theorem copy_byte {Q L m X g k pc addr sp x y z l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩)
    (site : pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412])
    (byte : TensorCopy.writeLoc sp x y z=some l) :
    l.addr<L.sharedBase+196608 ∨ L.sharedBase+213340≤l.addr :=
  (copy_map hp hX he site).2 byte

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export

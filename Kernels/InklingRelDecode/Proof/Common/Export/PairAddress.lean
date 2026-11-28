-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Gen.StepLoader
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Proof.Lib.CountLoad

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

/-- The loader reads either word of the pair. MMA always reads the second.
The address and width hold before either control decision uses the bytes. -/
public theorem pair_address {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2345 ∨ p=2423) :
    ∃ j : Fin 2, (p=2423 → j=1) ∧
      a.loc=⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ ∧ a.size=4 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change p=_ at pc
  obtain ⟨w,x,r,d,n,rfl⟩ := (pc ▸ state_role s).worker (by omega) (by omega) (by omega)
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  rw [←pc] at hc fire
  have fetch : kernel.code[p]?=some ⟨none,.mem (Lib.countLoad p)⟩ := by
    rcases site with rfl|rfl
    · exact Flow.code_2345
    · exact Flow.code_2423
  obtain rfl := Option.some.inj (hc.symm.trans fetch)
  have ⟨addr,size⟩ := Lib.count_load_shape hp site fire
  obtain ⟨_,sub,_,_,_⟩ := ht
  cases r with
  | loader =>
    change p=d.site.pc at pc
    have ne (s : Loader.Site) : s.pc≠2423 := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    have only : p=2345 := by have := ne d.site; omega
    change t.sub=(if d.site=.second then 1 else 0) at sub
    have small : t.sub<2 := by split at sub <;> omega
    exact ⟨⟨t.sub,small⟩,by omega,by simpa [only] using addr,size⟩
  | mma =>
    change p=d.site.pc at pc
    have ne (s : Mma.Site) : s.pc≠2345 := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    have only : p=2423 := by have := ne d.site; omega
    change t.sub=0 at sub
    exact ⟨1,fun _ => rfl,by simpa [only,sub,Nat.add_assoc] using addr,size⟩

end PTX.Kernels.InklingRelDecode.Proof.Export

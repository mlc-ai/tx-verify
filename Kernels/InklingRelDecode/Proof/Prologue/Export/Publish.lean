-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
import Kernels.InklingRelDecode.Proof.Common.FollowSub
import Kernels.InklingRelDecode.Proof.Prologue.ShapePublish
import Lemmas.Flow.Final

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof

private theorem pair_site (s : Site) : s.pc=571 → ∃ j, s=.st9 j := by
  cases s <;> repeat' first | exact fun _ => ⟨_,rfl⟩ | (rename_i j; revert j)
  all_goals decide +kernel

/-- The writer publishes the preload count and the iteration count at the two
substeps of PC 571. Both values come from the launch arrays. -/
public theorem pair_bytes {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨571,.wr a bs⟩) :
    ∃ j : Fin 2, a.elem = j.val ∧ a.size = 4 ∧
      a.loc = ⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ ∧
      bs = (b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
        else Q.numIters ((L.ctaidOf (g/L.block)).get .z)
          ((L.ctaidOf (g/L.block)).get .x))).toBytes := by
  have hg := Frame.lt_of_get hX he
  have ht := control_tracked hp hX g k hg
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨ht,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role s).prologue
    (by decide : 27<571) (by decide : 571<574)
  obtain ⟨t,ins,o,hat,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg)
    hX he hs (by simp)
  change 571=d.site.pc at pc
  obtain ⟨j,site⟩ := pair_site _ pc.symm
  have known := pro_known hp hX (List.getElem?_eq_some_iff.mp he).1.le hs
  change kernel.code[d.site.pc]? = _ at hc
  change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨571,.wr a bs⟩ o at fire
  rw [←pc] at hc fire
  cases o with
  | none =>
    have ends := fires_none_ends fire
    rcases ends with ⟨_,bad⟩ | bad <;> cases bad
  | some u =>
    have eq := pair_store hp hg j site hat known hc fire
    obtain ⟨eqA,rfl⟩ := Kind.wr.inj (congrArg Event.kind eq)
    subst a
    refine ⟨j,rfl,rfl,rfl,?_⟩
    fin_cases j <;> rfl

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

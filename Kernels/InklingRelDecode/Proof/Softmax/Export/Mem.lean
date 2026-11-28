-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.LoadSharedSize
import Lemmas.Flow.Final
import Lemmas.Flow.Store

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow

/-- Every observed event in the interior of the Softmax code is issued
by one of the four data warps. -/
public theorem data_site {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some e)
    (nu : ∀ f, e.kind≠.ub f) (lo : 574<e.pc) (hi : e.pc<2331) : g%L.block<128 := by
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun _ f h => nu f (congrArg Event.kind h))
    ⟨control_tracked hp hX g k (Frame.lt_of_get hX he),fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  obtain ⟨_,_,_,_,rfl⟩ := (pc ▸ state_role s).softmax lo hi
  exact data_warp hp hX (List.getElem?_eq_some_iff.mp he).1.le hs

/-- The four warps publish their minima into consecutive shared words.
Warps 0 and 1 reuse the two words that the Prologue published at PC 571. -/
public theorem scratch_store {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨2250,.wr a bs⟩) :
    a.loc = ⟨.shared,g/L.block,L.sharedBase+212992+(g%L.block/32%4)*4⟩ ∧ a.size=4 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨entW,ent,d,n,rfl⟩ := (pc ▸ state_role s).softmax
    (by decide : 574<2250) (by decide : 2250<2331)
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  change 2250=d.site.pc at pc
  change kernel.code[d.site.pc]? = _ at hc
  change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨2250,.wr a bs⟩ o at fire
  rw [←pc] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2250)
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have key : 1533 ∈ Control.ctlLive d.site.pc := by rw [←pc]; decide +kernel
  have reg := holds_mem regs (mem_factsFrom key)
  let addr := L.sharedBase+212992+(g%L.block/32%4)*4
  have bound := hp.sharedRange
  change L.sharedBase+213340≤2^18 at bound
  have small : addr<2^32 := by dsimp [addr]; omega
  change t.regs 1533 = some (b32 (addr%2^32)) at reg
  rw [Nat.mod_eq_of_lt small] at reg
  generalize Assumptions.all = A at fire
  have shape := fires_stv32 (A := A) (g := g) (L := L) (e := ⟨2250,.wr a bs⟩)
    (pc := 2250) (srcs := [.reg 1534]) (ik := .b) (o := o) reg small (Or.inl rfl)
  generalize eventTmpl A L g t _ = tmpl at shape fire
  obtain ⟨loc,size⟩ := shape (by assumption) a bs rfl
  have zero : t.sub=0 := sub
  simpa [zero,addr] using And.intro loc size

/-- Each lane reads the four-byte word indexed by its lane number modulo four. -/
public theorem scratch_read {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨2252,.rd a bs⟩) :
    a.loc = ⟨.shared,g/L.block,L.sharedBase+212992+(g%L.block%4)*4⟩ ∧ a.size=4 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  obtain ⟨entW,ent,d,n,rfl⟩ := (pc ▸ state_role s).softmax
    (by decide : 574<2252) (by decide : 2252<2331)
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  change 2252=d.site.pc at pc
  change kernel.code[d.site.pc]? = _ at hc
  change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) ⟨2252,.rd a bs⟩ o at fire
  rw [←pc] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2252)
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have key : 500 ∈ Control.ctlLive d.site.pc := by rw [←pc]; decide +kernel
  have reg := holds_mem regs (mem_factsFrom key)

  let addr := L.sharedBase+(g%L.block%4)*4
  have bound := hp.sharedRange
  change L.sharedBase+213340≤2^18 at bound
  have small : addr+212992<2^32 := by dsimp [addr]; omega
  change t.regs 500 = some (b32 (addr%2^32)) at reg
  rw [Nat.mod_eq_of_lt (show addr<2^32 by omega)] at reg
  cases o with
  | none => rcases fires_none_ends fire with ⟨_,bad⟩|bad <;> cases bad
  | some u =>
    generalize Assumptions.all = A at fire
    have loc := fires_ld_shared (A := A) (L := L) (g := g) (ik := .b) (d := 1542)
      (pc := 2252) (e := ⟨2252,.rd a bs⟩) (u := u) reg small sub
    have size := fires_ld_shared_size (A := A) (L := L) (g := g) (ik := .b) (d := 1542)
      (pc := 2252) (e := ⟨2252,.rd a bs⟩) (u := u) reg small sub
    generalize eventTmpl A L g t _ = tmpl at loc size fire
    obtain ⟨_,_,eq,addrEq,_⟩ := loc (by assumption)
    cases eq
    exact ⟨by simpa [addr,Nat.add_right_comm] using addrEq, size (by assumption) _ _ rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

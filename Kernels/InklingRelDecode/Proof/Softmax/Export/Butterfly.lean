-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Lib.RescaleWord
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.StoreBytes32
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Softmax.Operand
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.Where
import Lemmas.Kernel.Frame
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.MinSwap
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Butterfly
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleData
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShufflePartner

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control

/-- The shuffle of stage `k` of the minimum butterfly (offset `8 >> k`) of lane `g` at index `j`
sends `a` and receives `r`. -/
def Stage (X : Execution) (k g j : Nat) (a r : Value) : Prop :=
  ∃ ok, X.get (g,j)=some ⟨2242+2*k,.shfl .bfly a (8>>>k) 31 r ok⟩

private theorem fold_site (s : Site)
    (h : s.pc=2244 ∨ s.pc=2246 ∨ s.pc=2248 ∨ s.pc=2250) :
    s=.shfl8 ∨ s=.shfl9 ∨ s=.shfl10 ∨ s=.store10 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

set_option maxRecDepth 10000 in
private theorem pred_fold {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn))
    (site : dn.site=.shfl8 ∨ dn.site=.shfl9 ∨ dn.site=.shfl10 ∨ dn.site=.store10) :
    d.site.pc+2=dn.site.pc ∧ ∃ m a b c ok, ev.kind=.shfl m a b c dn.held.peer ok ∧
      dn.held.word=a := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | exact ⟨rfl,_,_,_,_,_,by assumption,rfl⟩

private theorem fold_eq {s s' : Site} (hs : s=.shfl8 ∨ s=.shfl9 ∨ s=.shfl10 ∨ s=.store10)
    (hs' : s'=.shfl8 ∨ s'=.shfl9 ∨ s'=.shfl10 ∨ s'=.store10) (h : s.pc=s'.pc) : s=s' := by
  rcases hs with rfl|rfl|rfl|rfl <;> rcases hs' with rfl|rfl|rfl|rfl <;>
    first | rfl | (exfalso; revert h; decide)

/-- The event before a shuffle or store of the butterfly's later stages is the previous stage's
shuffle, whose operand and received value the machine has carried. -/
private theorem fold_prev {Q L m X g k ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ev)
    (clean : ∀ f, ev.kind≠.ub f) {s : Site}
    (hs : s=.shfl8 ∨ s=.shfl9 ∨ s=.shfl10 ∨ s=.store10) (pc : ev.pc=s.pc) :
    ∃ u w ent d cnt a' r' mo b' c' ok', u+1=k ∧ d.site=s ∧ d.held.word=a' ∧ d.held.peer=r' ∧
      Frame.stateAt (thread Q L) X g k=some (some (softState w ent d cnt)) ∧
      X.get (g,u)=some ⟨s.pc-2,.shfl mo a' b' c' r' ok'⟩ := by
  have range : 574<ev.pc ∧ ev.pc<2331 := by rw [pc]; rcases hs with rfl|rfl|rfl|rfl <;> decide
  obtain ⟨w,ent,d,n,hs0,pcd⟩ := at_site hp hX get clean range.1 range.2
  have pcs : d.site.pc=s.pc := pcd.symm.trans pc
  have site : d.site=s := by
    refine fold_eq (fold_site d.site ?_) hs pcs
    rw [pcs]; rcases hs with rfl|rfl|rfl|rfl <;> decide
  have later : d≠{} := by
    rintro rfl
    rw [←site] at hs
    exact absurd hs (by decide)
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  obtain ⟨u,old,cnt,ev1,eq,st1,get1,step⟩ := soft_prev len later hs0
  obtain ⟨gap,mo,a',b',c',ok',kind,word⟩ := pred_fold step (by rwa [site])
  have clean1 := Frame.noUbBefore_of_get hX get u (by omega) ev1 get1
  have pc1 := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get1 st1 clean1
  have e1 : ev1=⟨s.pc-2,.shfl mo a' b' c' d.held.peer ok'⟩ := by
    obtain ⟨p1,k1⟩ := ev1
    change p1=old.site.pc at pc1
    rw [site] at gap
    cases kind
    simp only [pc1]
    congr
    omega
  exact ⟨u,w,ent,d,n,a',d.held.peer,mo,b',c',ok',eq,site,word,rfl,hs0,e1 ▸ get1⟩

/-- The butterfly shuffles are `bfly` shuffles with offsets 8, 4, 2, 1 and clamp 31. -/
public theorem stage_shape {Q L m X g j k mode a b c r ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k≤3)
    (get : X.get (g,j)=some ⟨2242+2*k,.shfl mode a b c r ok⟩) :
    mode=.bfly ∧ b=8>>>k ∧ c=31 := by
  have clean : ∀ f, (Event.mk (2242+2*k) (.shfl mode a b c r ok)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<2242+2*k; omega)
    (by show 2242+2*k<2331; omega)
  interval_cases k
  · obtain ⟨-,mode',bval,cval⟩ := operand hX hp get (ev := ⟨2242,.shfl mode a b c r ok⟩) rfl
      (show d.site.pc=2242 from pc.symm) hs Flow.code_shfl_7 (fun _ => ⟨_,rfl,rfl⟩)
    exact ⟨mode',bval,cval⟩
  · obtain ⟨-,mode',bval,cval⟩ := operand hX hp get (ev := ⟨2244,.shfl mode a b c r ok⟩) rfl
      (show d.site.pc=2244 from pc.symm) hs Flow.code_shfl_8 (fun _ => ⟨_,rfl,rfl⟩)
    exact ⟨mode',bval,cval⟩
  · obtain ⟨-,mode',bval,cval⟩ := operand hX hp get (ev := ⟨2246,.shfl mode a b c r ok⟩) rfl
      (show d.site.pc=2246 from pc.symm) hs Flow.code_shfl_9 (fun _ => ⟨_,rfl,rfl⟩)
    exact ⟨mode',bval,cval⟩
  · obtain ⟨-,mode',bval,cval⟩ := operand hX hp get (ev := ⟨2248,.shfl mode a b c r ok⟩) rfl
      (show d.site.pc=2248 from pc.symm) hs Flow.code_shfl_10 (fun _ => ⟨_,rfl,rfl⟩)
    exact ⟨mode',bval,cval⟩

private theorem back_core {Q L m X g j k a r ok} {s : Site} {src dst : Nat} {n : Int}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hs : s=.shfl8 ∨ s=.shfl9 ∨ s=.shfl10) (pc : s.pc=2242+2*(k+1))
    (code : kernel.code[s.pc]?=some ⟨none,.warp ⟨.shfl .bfly,some (.int .b 32),[some dst],
      [.reg src,.imm n,.imm 31],some (.imm (-1))⟩⟩)
    (src_min : src ∈ minRegs) (live : src ∈ ctlLive s.pc)
    (one : ∀ t : TState, ∃ m, readBits L g t 32 (.imm n)=.ok m ∧ m.toNat=8>>>(k+1))
    (get : X.get (g,j)=some ⟨s.pc,.shfl .bfly a (8>>>(k+1)) 31 r ok⟩) (hk : k<3) :
    ∃ j' a' r', j=j'+1 ∧ Stage X k g j' a' r' ∧ a=Lib.minWord a' r' := by
  obtain ⟨u,w,ent,d,cnt,a',r',mo,b',c',ok',eq,site,wd,pd,hs0,getu⟩ :=
    fold_prev hp hX get (fun _ => nofun) (s := s) (by rcases hs with h|h|h <;> simp [h]) rfl
  obtain ⟨val,-,-,-⟩ := operand hX hp get (ev := ⟨s.pc,.shfl .bfly a (8>>>(k+1)) 31 r ok⟩) rfl
    (show d.site.pc=s.pc by rw [site]) hs0 code one
  have e : s.pc-2=2242+2*k := by omega
  rw [e] at getu
  obtain ⟨rfl,rfl,rfl⟩ := stage_shape hp hX (by omega) getu
  exact ⟨u,a',r',eq.symm,⟨ok',getu⟩,by rw [val live,val_min _ src_min,wd,pd]⟩

/-- Each later stage sends the minimum of the previous stage's operand and received value. -/
public theorem stage_back {Q L m X g j k a r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hk : k<3) (st : Stage X (k+1) g j a r) :
    ∃ j' a' r', j=j'+1 ∧ Stage X k g j' a' r' ∧ a=Lib.minWord a' r' := by
  obtain ⟨ok,get⟩ := st
  interval_cases k
  · exact back_core (s := .shfl8) (src := 1536) (dst := 1537) (n := 4) hp hX (by simp) rfl
      Flow.code_shfl_8 (by decide) (by decide +kernel) (fun _ => ⟨_,rfl,rfl⟩) get (by omega)
  · exact back_core (s := .shfl9) (src := 1538) (dst := 1539) (n := 2) hp hX (by simp) rfl
      Flow.code_shfl_9 (by decide) (by decide +kernel) (fun _ => ⟨_,rfl,rfl⟩) get (by omega)
  · exact back_core (s := .shfl10) (src := 1540) (dst := 1541) (n := 1) hp hX (by simp) rfl
      Flow.code_shfl_10 (by decide) (by decide +kernel) (fun _ => ⟨_,rfl,rfl⟩) get (by omega)

/-- The scratch store writes the bytes of the last stage's minimum. -/
public theorem store_back {Q L m X g j dst ys} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,j)=some ⟨2250,.wr dst ys⟩) :
    ∃ j' a' r', j=j'+1 ∧ Stage X 3 g j' a' r' ∧ ys=storedBytes (Lib.minWord a' r') := by
  obtain ⟨u,w,ent,d,cnt,a',r',mo,b',c',ok',eq,site,wd,pd,hs0,getu⟩ :=
    fold_prev hp hX get (fun _ => nofun) (s := .store10) (by simp) rfl
  have e : Site.store10.pc-2=2242+2*3 := rfl
  rw [e] at getu
  obtain ⟨rfl,rfl,rfl⟩ := stage_shape hp hX (by omega) getu
  refine ⟨u,a',r',eq.symm,⟨ok',getu⟩,?_⟩
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs0
    (fun _ => nofun)
  change kernel.code[d.site.pc]?=some ins at hc
  change Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) _ o at fire
  have pc : d.site.pc=2250 := site ▸ rfl
  rw [pc] at hc fire
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2250)
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have k1 : 1533 ∈ ctlLive d.site.pc := by rw [pc]; decide +kernel
  have k2 : 1534 ∈ ctlLive d.site.pc := by rw [pc]; decide +kernel
  have r1 := holds_mem regs (mem_factsFrom k1)
  have r2 := holds_mem regs (mem_factsFrom k2)
  change t.regs 1533=some (b32 ((L.sharedBase+212992+(g%L.block/32%4)*4)%2^32)) at r1
  rw [val_min _ (by decide),wd,pd] at r2
  exact fires_stv32_bytes1 r1 (Nat.mod_lt _ (by decide)) r2 sub fire dst ys rfl

/-- The partner of a butterfly shuffle: the lane of the same warp with the lane index flipped at
the stage's offset has the stage's shuffle at the same ordinal and sent what this lane received. -/
public theorem stage_partner {Q L m X g j k a r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hk : k≤3)
    (lane : g%L.block<128) (st : Stage X k g j a r) :
    ∃ j' r', Stage X k (g-g%32+(g%32 ^^^ 8>>>k)) j' r r' ∧
      ((X.tr (g-g%32+(g%32 ^^^ 8>>>k))).take j').countP Execution.isShfl=
        ((X.tr g).take j).countP Execution.isShfl ∧
      (g-g%32+(g%32 ^^^ 8>>>k))%L.block<128 := by
  obtain ⟨ok,get⟩ := st
  have late : 2242+2*k=1838 ∨ 2242+2*k=2242 ∨ 2242+2*k=2244 ∨ 2242+2*k=2246 ∨
      2242+2*k=2248 ∨ 2242+2*k=2253 ∨ 2242+2*k=2255 ∨ 2242+2*k=2234 := by omega
  have small : 8>>>k<32 := by
    have : 8>>>k≤8 := Nat.shiftRight_le _ _
    omega
  obtain ⟨j',b',c',r',o',got,low,-,count⟩ := late_partner hp hX hf get late small lane
  obtain ⟨-,rfl,rfl⟩ := stage_shape hp hX hk got
  exact ⟨j',r',⟨o',got⟩,count,low⟩

/-- The minimum of two words does not depend on their order. -/
public theorem minWord_comm (x y : Value) : Lib.minWord x y=Lib.minWord y x := by
  unfold Lib.minWord
  cases h : MinCore.minE [x,y] with
  | error f =>
    cases h2 : MinCore.minE [y,x] with
    | error g => rfl
    | ok v => exact absurd ((MinCore.minE_comm x y v).2 h2) (by rw [h]; simp)
  | ok v => rw [(MinCore.minE_comm x y v).1 h]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export

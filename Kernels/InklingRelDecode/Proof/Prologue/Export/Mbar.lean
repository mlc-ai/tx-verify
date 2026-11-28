-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Prologue
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent
import Kernels.InklingRelDecode.Proof.Prologue.ShapeMbar
import Kernels.InklingRelDecode.Proof.Lib.Elect
import Lemmas.Protocol.MbarRowSource

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow Control MbarRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event} {l : Loc}

private noncomputable def counts (L : Launch) (X : Execution) (g k : Nat) :=
  proCounts L g fun c => ((X.tr g).take k).countP (cls c)

private theorem observed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (he : X.get (g,k)=some e) (lo : 27≤e.pc) (hi : e.pc<574)
    (hm : Frame.MbarOf e l) :
    ∃ d, g%L.block<128 ∧ Inv (g%L.block) d ∧ e.pc=d.site.pc ∧
      History Q L g d (counts L X g k) ∧ Use L g d.site e l := by
  obtain ⟨s,mem,pos,_⟩ := PTX.MbarRow.region_source prologue_sites hX he hm lo hi
  have lob : ∀ s ∈ prologueSites, 27<s.pc := by decide
  have nonub : ∀ f, e.kind≠.ub f := by
    have := PTX.MbarRow.objectKind hm
    intro f h; rw [h] at this; exact this.elim
  obtain ⟨w,d,t,ins,u,ht,inv,pc,hc,fire,warp,hist⟩ :=
    prologue_event hp hX hf he nonub (pos ▸ lob s mem) hi
  exact ⟨_,warp,inv,pc,hist,use_of_fires hp hX he hm ht pc hi hc fire⟩

private theorem vote {p : Nat} (hX : Consistent L kernel Assumptions.all m X)
    (h : 0<(counts L X g k).vote p) :
    ∃ j inst, j<k ∧ X.get (g,j)=some ⟨p,.elect 4294967295 inst (laneOf L g)⟩ := by
  obtain ⟨⟨pc,kd⟩,mem,won⟩ := List.countP_pos_iff.mp h
  obtain ⟨whereAt,leader⟩ := Bool.and_eq_true_iff.mp won
  obtain rfl := beq_iff_eq.mp whereAt
  cases kd <;> try contradiction
  rename_i mask inst leaderId
  obtain rfl := beq_iff_eq.mp leader
  obtain ⟨j,hj,atJ⟩ := List.getElem_of_mem mem
  have len := List.length_take (l := X.tr g) (i := k)
  have lt : j<k := by omega
  have get : X.get (g,j)=some ⟨pc,.elect mask inst (laneOf L g)⟩ := by
    change (X.tr g)[j]?=_
    rw [←List.getElem?_take_of_lt lt,List.getElem?_eq_getElem hj,atJ]
  have full := Lib.elect_full hX (e := (g,j)) get
  exact ⟨j,inst,lt,full ▸ get⟩

private theorem selected {d b} (hp : Pre Q L m) (hg : g<L.threads)
    (hist : History Q L g d (counts L X g k)) (block : d.site.block=some b) (lo : 41<d.site.pc) :
    b.val<Iface.preloadCount Q L (g/L.block) := by
  have h := hist.block b block
  have eq := preload_count hp hg (hist.known.first (by omega)) (hist.known.last (by omega))
    (hist.known.seq lo)
  rw [←eq]; omega

private theorem copy_elected {d b j} (hX : Consistent L kernel Assumptions.all m X)
    (hist : History Q L g d (counts L X g k)) (hs : d.site=.ptc b j) :
    Elected ((X.tr g).take k) (laneOf L g) := by
  obtain ⟨i,inst,lt,he⟩ := vote hX (hist.won (pelPc b j) (by rw [hs]; rfl))
  have mem : ((X.tr g).take k)[i]? = some ⟨pelPc b j,.elect 4294967295 inst (laneOf L g)⟩ := by
    rw [List.getElem?_take_of_lt lt]; exact he
  exact ⟨_,List.mem_of_getElem? mem,_,_,rfl⟩

private theorem preload (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : Iface.KvPreload Q L X := by
  constructor
  · intro g k pc c b tx n rel sc lo hi get
    obtain ⟨d,warp,inv,pos,hist,use⟩ :=
      observed hp hX hf get lo hi (l := Iface.kvReadyLoc L c b) rfl
    cases use with
    | init _ _ _ kd => cases kd
    | copy _ _ _ _ kd => obtain ⟨_,_,kd,_⟩ := kd; cases kd
    | arr s site loc kd =>
      have cta := congrArg Loc.cta loc
      change c=g/L.block at cta
      subst c
      have addr := congrArg Loc.addr loc
      change L.sharedBase+(213216+8*b.val)=L.sharedBase+(213216+8*s.val) at addr
      obtain rfl : b=s := Fin.ext (by omega)
      obtain ⟨rfl,rfl,rfl,rfl⟩ := by exact (Kind.arrive.inj kd).2
      unfold Control.Inv at inv
      rw [site] at inv pos
      have tid : g%L.block%128=0 := inv
      have hp' : pc=arrPc b := pos
      have ar : ∀ b, 130≤arrPc b ∧ arrPc b≤315 := by decide
      have fresh := hist.visits.fresh (arrPc b) (ar b).1 (ar b).2 (by rw [site]; rfl)
      have value := hist.arrive b
      have small := selected hp (Frame.lt_of_get hX get) hist
        (by rw [site]; rfl : d.site.block=some b)
        (by rw [site]; exact lt_of_lt_of_le (by decide : 41<130) (ar b).1)
      have pcs : ∀ b, arrPc b = ([193,237,279] : List Nat)[b.val]! := by decide
      exact ⟨rfl,by omega,small,hp'.trans (pcs b),rfl,rfl,
        Nat.eq_zero_of_le_zero (value.trans fresh.le)⟩
  · intro g k pc c b a sp lo hi get bar
    obtain ⟨d,warp,inv,pos,hist,use⟩ := observed hp hX hf get lo hi bar
    cases use with
    | init _ _ _ kd => cases kd
    | arr _ _ _ kd => cases kd
    | copy s j site loc kd =>
      have cta := congrArg Loc.cta loc
      change c=g/L.block at cta
      subst c
      have addr := congrArg Loc.addr loc
      change L.sharedBase+(213216+8*b.val)=L.sharedBase+(213216+8*s.val) at addr
      obtain rfl : b=s := Fin.ext (by omega)
      obtain ⟨_,_,kd,_,bytes⟩ := kd
      cases kd
      have lower : ∀ b j, 41<(Site.ptc b j).pc := by decide
      have small := selected hp (Frame.lt_of_get hX get) hist
        (by rw [site]; rfl : d.site.block=some b)
        (site ▸ lower b j)
      unfold Control.Inv at inv
      rw [site] at inv
      have eligible : g%L.block%128<64 := inv.1
      exact ⟨rfl,small,by omega,copy_elected hX hist site,bytes,hist.copy_lt b j site⟩

public theorem mbarRow (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : MbarRow.Prologue Q L X := by
  refine ⟨preload hp hX hf,?_⟩
  intro g k ev l hg he atPc hm
  obtain ⟨d,_,inv,pos,hist,use⟩ := observed hp hX hf he atPc.2.1 atPc.2.2 hm
  cases use with
  | init j site addr kd =>
    have pcs : ∀ j, elPc j = (if j.val=0 then 130 else (Site.init j).pc-3) := by decide
    have bound : ∀ j, 130≤(Site.init j).pc ∧ (Site.init j).pc≤178 := by decide
    unfold Control.Inv at inv
    rw [site] at pos inv
    have item := vote hX (hist.won (elPc j) (by rw [site]; rfl))
    have fresh := hist.visits.fresh ev.pc (by rw [pos]; exact (bound j).1)
      (by rw [pos]; have := (bound j).2; omega) (by rw [site,pos]; rfl)
    have bars := hist.bars (by
      rw [site]; change 4*(Site.init j).pc+0 ≤ _; have := (bound j).2; omega)
    have eq (i) : cls (.bar i) = Execution.isBarId i := by
      funext ⟨p,k⟩; cases k <;> rfl
    refine .init j pos addr kd inv.1 ?_ fresh ?_ ?_
    · rwa [pos,←pcs j]
    · simpa only [counts,proCounts,eq] using bars.1
    · simpa only [counts,proCounts,eq] using bars.2
  | arr b site addr kd =>
    have pcs : ∀ b, arrPc b = ([193,237,279] : List Nat)[b.val]! := by decide
    exact .preloadArrive b (pos.trans ((congrArg Site.pc site).trans (pcs b))) addr kd
  | copy b j site addr kd =>
    have pcs : ∀ b j, ptcPc b j ∈ preloadCopies b := by decide
    exact .preloadCopy b (by rw [pos,site]; exact pcs b j) addr kd

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export

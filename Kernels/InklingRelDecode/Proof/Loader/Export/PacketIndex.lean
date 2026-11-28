-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.RankOrder
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Lib.IterRange

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Frame PTX.Proof

private def sites := [2378,2389,2391,2394,2396,2404,2406,2410,2412]

private def position (pc : Nat) := [2,6,7,10,11,15,16,19,20][sites.idxOf pc]!

private theorem site_info (s : Site) (h : s.pc ∈ sites) :
    (s=.arrive ∨ ∃ p b, s=.copy p b) ∧ s.position=position s.pc := by
  cases s <;> first
    | exact False.elim ((by decide : ¬ _ ∈ sites) h)
    | exact ⟨.inl rfl,rfl⟩
    | (rename_i p b; exact ⟨.inr ⟨p,b,rfl⟩,by fin_cases p <;> cases b <;> rfl⟩)
    | (rename_i p; fin_cases p <;> contradiction)

private theorem visit {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=6) (he : X.get (g,k)=some e)
    (nu : ∀ f, e.kind≠.ub f) (pc : e.pc ∈ sites) :
    (e.pc=2378 → laneOf L g=0) ∧ ∃ d, stateAt (thread Q L) X g k=some (some d) ∧
      threadRank d=8+(22*iterationsLeft
        (b32 (Iface.preloadCount Q L (g/L.block)+pollRound 2374 ((X.tr g).take k)-1))
        (b32 (iterCount Q L (g/L.block)))+(21-position e.pc)) := by
  have bound : ∀ p ∈ sites, 2344<p ∧ p<2422 := by decide
  obtain ⟨w,x,r,d,n,hs,hi⟩ := worker_event hp hX hf he nu
    (bound _ pc).1 (by have := (bound _ pc).2; omega) (by have := (bound _ pc).2; omega)
  cases r with
  | mma =>
    have wrong : g%L.block/32=7 := hi.1
    omega
  | loader =>
    obtain ⟨_,hr,hct,_⟩ := hi
    have inv := (reached_table hf (lt_of_get hX he) (noUbBefore_of_get hX he) hs).1
    have good : d.site=.arrive → laneOf L g=0 := inv.1
    have atpc := event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
    change e.pc=d.site.pc at atpc
    obtain ⟨pack,pos⟩ := site_info d.site (atpc ▸ pc)
    obtain ⟨s,i,v,a,b⟩ := d
    change s=.arrive ∨ ∃ p b, s=.copy p b at pack
    obtain ⟨j,lo,hi,rfl,rfl⟩ := ref_loop hr (by rcases pack with rfl|⟨_,_,rfl⟩ <;> rfl)
    have hn := Lib.iter_range hp (lt_of_get hX he)
    change iterCount Q L (g/L.block)<2^31 at hn
    have bitsj : (bits (b32 j)).toNat=j := by
      rw [bits_b32 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have count := (fcount hs (.poll 2374)).symm.trans hct
    change pollRound 2374 _=polls _ _ _ at count
    have num : pollRound 2374 ((X.tr g).take k)=j-Iface.preloadCount Q L (g/L.block)+1 := by
      rcases pack with rfl|⟨_,_,rfl⟩ <;> simpa only [polls,bitsj] using count
    change e.pc=s.pc at atpc
    constructor
    · intro eq
      apply good
      rcases pack with rfl|⟨p,b,rfl⟩
      · rfl
      · rw [eq] at atpc
        have neq : ∀ (u : Fin 4) (v : Bool), 2378≠(Site.copy u v).pc := by decide
        exact False.elim (neq p b atpc)
    · refine ⟨_,hs,?_⟩
      rw [show Iface.preloadCount Q L (g/L.block)+pollRound 2374 ((X.tr g).take k)-1=j by omega]
      rw [atpc,←pos]
      rcases pack with rfl|⟨_,_,rfl⟩ <;> rfl


/-- Only lane zero of the loader warp announces a packet. -/
public theorem announce_lane {Q L m X g k obj tx n rel sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (warp : g%L.block/32=6) (he : X.get (g,k)=some ⟨2378,.arrive obj tx n rel sc⟩) :
    laneOf L g=0 :=
  (visit hp hX hf warp he (by simp) (by decide : 2378 ∈ sites)).1 rfl

/-- One event per packet site and successful poll ordinal, including on partial traces. -/
public theorem packet_unique {Q L m X g j k e v} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (warp : g%L.block/32=6) (first : X.get (g,j)=some e) (last : X.get (g,k)=some v)
    (pc : e.pc ∈ [2378,2389,2391,2394,2396,2404,2406,2410,2412]) (same : e.pc=v.pc)
    (nu : ∀ f, e.kind≠.ub f) (nv : ∀ f, v.kind≠.ub f) (ec : e.counts) (vc : v.counts)
    (ord : pollRound 2374 ((X.tr g).take j)=pollRound 2374 ((X.tr g).take k)) : j=k := by
  obtain ⟨_,d,fst,rank⟩ := visit hp hX hf warp first nu pc
  obtain ⟨_,s,snd,rank'⟩ := visit hp hX hf warp last nv (same ▸ pc)
  rw [same,ord] at rank
  have eq := rank.trans rank'.symm
  rcases lt_trichotomy j k with lt|eq|gt
  · exact (eq.not_gt (later_rank hp hX hf words first ec fst lt
      (List.getElem?_eq_some_iff.mp last).1.le snd)).elim
  · exact eq
  · exact (eq.not_lt (later_rank hp hX hf words last vc snd gt
      (List.getElem?_eq_some_iff.mp first).1.le fst)).elim

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export

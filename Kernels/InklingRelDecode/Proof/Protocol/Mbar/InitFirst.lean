-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar
public import Kernels.InklingRelDecode.Proof.Lib.MbarInit
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
open PTX PTX.Flow MbarRow PTX.MbarRow

/-- The Prologue row identifies the initializer's election, count, ordinal and CTA. -/
theorem init_info {Q L X g k pc l n} (rows : MbarRows Q L X) (hg : g < L.threads)
    (he : X.get (g,k) = some ⟨pc,.mbInit l n⟩) :
    ∃ j : Fin 12, pc = 134 + 4*j.val ∧ l = loc L g (initOffset j) ∧ n = 1 ∧
      g % L.block < 32 ∧ (∃ i ep inst, X.get (g,i) = some ⟨ep,.elect 4294967295 inst (laneOf L g)⟩)
      ∧ ((X.tr g).take k).countP (fun a => a.pc == pc) = 0 := by
  cases mbar_use rows hg he (l := l) rfl with
  | startup _ h | dispatch _ h => cases h
  | prologue _ h =>
    cases h with
    | init j hp hl hk hw hel h0 _ _ =>
      obtain ⟨i,inst,_,hi⟩ := hel
      exact ⟨j,hp,hl,(Kind.mbInit.inj hk).2,hw,⟨i,_,inst,hi⟩,h0⟩
    | preloadArrive _ _ _ hk => cases hk
    | preloadCopy _ _ _ hk => obtain ⟨_,_,hk,_⟩ := hk; cases hk
  | loader _ h | mma _ h | softmax _ h | epilogue _ h =>
    cases h <;> simp_all [Wait,Commit,Arrive,Issue]

private theorem offset_inj : Function.Injective initOffset := by
  intro i j
  exact (by decide : ∀ i j : Fin 12, initOffset i = initOffset j → i = j) i j

theorem init_unique {Q L m X g h k j pc pc' l n n'} (rows : MbarRows Q L X)
    (hX : Consistent L kernel Assumptions.all m X)
    (ha : X.get (g,k) = some ⟨pc,.mbInit l n⟩) (hb : X.get (h,j) = some ⟨pc',.mbInit l n'⟩) :
    (g,k) = (h,j) ∧ n = 1 := by
  have hg := Frame.lt_of_get hX ha
  have hh := Frame.lt_of_get hX hb
  obtain ⟨i,rfl,hl,rfl,hw,⟨a,p,x,hea⟩,h0⟩ := init_info rows hg ha
  obtain ⟨i',rfl,hl',rfl,hw',⟨b,q,y,heb⟩,h0'⟩ := init_info rows hh hb
  obtain ⟨_,hc,hoff⟩ := Loc.mk.inj (hl.symm.trans hl')
  obtain rfl := offset_inj (Nat.add_left_cancel hoff)
  have sw : SameWarp L g h := ⟨⟨hg,hh,hc⟩,by omega⟩
  have hlane := hX.elect.2.2 (g,a) (h,b) _ _ _ _ _ _ _ hea heb sw
  change g % L.block % 32 = h % L.block % 32 at hlane
  rw [Nat.mod_eq_of_lt hw,Nat.mod_eq_of_lt hw'] at hlane
  have heq : g = h := by
    have hg' := Nat.div_add_mod g L.block
    rw [hc,hlane,Nat.div_add_mod] at hg'
    exact hg'.symm
  subst h
  let pred := fun a : Event => a.pc == 134 + 4*i.val
  have hk := nthEv_eq (p := pred) ha (by simp [pred])
  have hj := nthEv_eq (p := pred) hb (by simp [pred])
  rw [show ((X.tr g).take k).countP pred = 0 from h0] at hk
  rw [show ((X.tr g).take j).countP pred = 0 from h0'] at hj
  exact ⟨congrArg (g,·) (hk.symm.trans hj),rfl⟩

/-- Prologue and CTA barrier producer contracts. Every object user sees an initializer;
the named-barrier handoff publishes it to every noninitializing issuer. -/
structure InitRows (L : Launch) (X : Execution) : Prop where
  /-- The elected Prologue initializer's write is published before every other use. -/
  publication : ∀ {i e l}, X.get i=some e → Frame.MbarOf e l →
    (∀ count, e.kind≠.mbInit l count) → ∃ v n, X.MbInit v l n ∧ InitPublished L X v i l

private theorem InitRows.existsAt {L X i e l} (hb : InitRows L X)
    (he : X.get i=some e) (use : Frame.MbarOf e l) : ∃ v n, X.MbInit v l n := by
  by_cases ini : ∃ n, e.kind=.mbInit l n
  · obtain ⟨n,eq⟩ := ini
    obtain ⟨pc,k⟩ := e
    cases eq
    exact ⟨i,n,pc,he⟩
  · obtain ⟨v,n,hv,_⟩ := hb.publication he use (fun n h => ini ⟨n,h⟩)
    exact ⟨v,n,hv⟩

private theorem issuer {L m X l r} (hX : Consistent L kernel Assumptions.all m X)
    (hr : r ∈ X.objects l) : ∃ ev, X.get r.id.issuer = some ev ∧ Frame.MbarOf ev l ∧
      ((∃ c, ev.kind = .mbInit l c) → ∃ n, r.action = .init n) := by
  cases AsyncCopy.record_source hX.tma.2.2.1 hr with
  | init hid he ha => exact hid ▸ ⟨_,he,rfl,fun _ => ⟨_,ha⟩⟩
  | arrive hid he _ | wait hid he _ | inval hid he _ | increment hid he _ =>
    rw [hid]; exact ⟨_,he,rfl,fun ⟨_,bad⟩ => by cases bad⟩
  | tensor hid he hm _ | bulk hid he hm _ _ =>
    rw [hid]; exact ⟨_,he,hm,fun ⟨_,bad⟩ => by cases bad⟩
  | arriveOn hid he hm _ _ => rw [hid]; exact ⟨_,he,hm.symm,fun ⟨_,bad⟩ => by cases bad⟩
  | commit hid he ht _ => rw [hid]; exact ⟨_,he,⟨_,ht⟩,fun ⟨_,bad⟩ => by cases bad⟩
  | clc hid he hm ht _ => rw [hid]; exact ⟨_,he,⟨_,ht,hm⟩,fun ⟨_,bad⟩ => by cases bad⟩

private theorem history_init {Q L m X l r} (hX : Consistent L kernel Assumptions.all m X)
    (rows : MbarRows Q L X) (hb : InitRows L X) (hr : r ∈ X.objects l) :
    ∃ i, X.MbInit i l 1 ∧ (∀ j pc n, X.get j=some ⟨pc,.mbInit l n⟩ → j=i ∧ n=1) ∧
      ∀ s ∈ X.objects l, (∀ n, s.action≠.init n) → InitPublished L X i s.id.issuer l := by
  obtain ⟨_,he,hu,_⟩ := issuer hX hr
  obtain ⟨⟨g,k⟩,n,pc,hi⟩ := hb.existsAt he hu
  obtain ⟨_,rfl⟩ := init_unique rows hX hi hi
  refine ⟨_,⟨pc,hi⟩,fun ⟨_,_⟩ _ _ h => init_unique rows hX h hi,?_⟩
  intro rec hrec hn
  obtain ⟨ev,hev,hm,hk⟩ := issuer hX hrec
  obtain ⟨⟨g',k'⟩,n,⟨p,hinit⟩,published⟩ := hb.publication hev hm (by
    intro n hk'
    obtain ⟨n',ha⟩ := hk ⟨n,hk'⟩
    exact hn n' ha)
  exact (init_unique rows hX hinit hi).1 ▸ published

/-- Every object with a log entry belongs to the CTA of one of the twelve initializers. -/
theorem record_loc {Q L m X l r} (hX : Consistent L kernel Assumptions.all m X)
    (rows : MbarRows Q L X) (hb : InitRows L X) (hr : r ∈ X.objects l) :
    ∃ c < L.grid, ∃ j : Fin 12, l=⟨.shared,c,L.sharedBase+initOffset j⟩ := by
  obtain ⟨⟨g,k⟩,⟨pc,get⟩,_,_⟩ := history_init hX rows hb hr
  have hg := Frame.lt_of_get hX get
  obtain ⟨j,_,addr,_⟩ := init_info rows hg get
  exact ⟨_,Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg),j,addr⟩

theorem initFirst {Q L m X} (hX : Consistent L kernel Assumptions.all m X)
    (rows : MbarRows Q L X) (hb : InitRows L X) (l : Loc) : PairTmaRing.InitFirst X l 1 := by
  intro r hr
  obtain ⟨_,init,unique,pub⟩ := history_init hX rows hb hr
  exact Lib.initFirst_of_published hX init (by decide) unique pub r hr

/-- All records belong to the same published initialization lifetime. -/
theorem published {Q L m X l r} (hX : Consistent L kernel Assumptions.all m X)
    (rows : MbarRows Q L X) (hb : InitRows L X) (hr : r ∈ X.objects l) :
    ObjectPublished L X l r := by
  obtain ⟨_,init,unique,pub⟩ := history_init hX rows hb hr
  exact Lib.objectPublished_of_init hX init (by decide) unique
    (fun _ _ ⟨_,he⟩ => Lib.no_inval hX he) pub r hr

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar

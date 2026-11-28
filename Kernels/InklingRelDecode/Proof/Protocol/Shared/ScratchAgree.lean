-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchSample
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.WeakAccess
import Lemmas.Flow.NotBulk
import Lemmas.Protocol.NamedBarLedger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow

private theorem weak_store {L m X h u dst ys} (hX : Consistent L kernel Assumptions.all m X)
    (wr : X.get (h,u)=some ⟨2250,.wr dst ys⟩) : ¬ dst.Strong := by
  obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX wr
  · cases bad
  cases Option.some.inj (code.symm.trans Flow.code_2250)
  exact fires_write_weak fire rfl

/-- One reader excludes an order from its reads-from source to the other
reader's source: both stores were already published to this reader. -/
private theorem not_hidden {Q L m X g k b a bs n h u dst ys h' u' dst' ys'}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩) (ord : barOrdinal X g k=n+1)
    (byte : b<a.size) (one : ScratchByte L X g k b a bs n h u dst ys)
    (store : X.get (h',u')=some ⟨2250,.wr dst' ys'⟩) (cta : h'/L.block=g/L.block)
    (sync : X.IsBarrier (h',u'+1) 0 (some 128) 2251) (epoch : barOrdinal X h' (u'+1)=n)
    (cov : dst'.Covers (a.loc.at b)) :
    ¬ ByteCausality L X (a.loc.at b) (.thread (h,u)) (.thread (h',u')) := by
  obtain ⟨j,rfl,wait⟩ := Softmax.Export.read_sync hp hX read
  have bump : barOrdinal X g (j+1)=barOrdinal X g j+1 := by
    unfold barOrdinal
    rw [List.take_add_one,show (X.tr g)[j]?=_ from wait,List.countP_append]
    rfl
  have lg := Softmax.Export.data_site hp hX read (by simp) (by dsimp; decide) (by dsimp; decide)
  have lh := Softmax.Export.data_site hp hX store (by simp) (by dsimp; decide) (by dsimp; decide)
  have edge := scratch_handoff hp hX sync wait cta lh lg (by omega : barOrdinal X h' (u'+1)=
    barOrdinal X g j) (Nat.lt_succ_self _) (Nat.lt_succ_self _)
    (List.getElem?_eq_some_iff.mp read).1
  have rd : X.MemReads (.thread (g,j+1)) a bs := .inl ⟨_,read⟩
  have wr : X.MemWrites (.thread (h',u')) dst' ys' := .inl ⟨_,store⟩
  have hidden := hX.hidden _ _ _ b _ _ _ rd byte wr cov (.direct (.inl edge))
  rwa [one.rf] at hidden

/-- Two stores of one scratch word in one round, from different lanes and unordered at a byte,
write the same bytes: the premise of the agreement of the scratch reads, which race freedom
(`StoreAgree.of_safe`) or the equal stores of a warp supply. -/
def StoreAgree (L : Launch) (X : Execution) (n : Nat) : Prop :=
  ∀ {h u t v dst ys acc zs l}, X.get (h,u)=some ⟨2250,.wr dst ys⟩ →
    X.get (t,v)=some ⟨2250,.wr acc zs⟩ → barOrdinal X h u=n → barOrdinal X t v=n → h≠t →
    dst.Covers l →
    acc.Covers l → dst.SameFootprint acc →
    ¬ByteCausality L X l (.thread (h,u)) (.thread (t,v)) →
    ¬ByteCausality L X l (.thread (t,v)) (.thread (h,u)) → ys=zs

/-- A store is no barrier: the ordinal after it is the ordinal before it. -/
theorem ord_store {X : Execution} {h u dst ys} (get : X.get (h,u)=some ⟨2250,.wr dst ys⟩) :
    barOrdinal X h (u+1)=barOrdinal X h u := by
  unfold barOrdinal
  rw [List.take_add_one,show (X.tr h)[u]?=_ from get,List.countP_append]
  rfl

theorem StoreAgree.of_safe {L m X n} (hX : Consistent L kernel Assumptions.all m X)
    (safe : ¬Race L X) : StoreAgree L X n := by
  intro h u t v dst ys acc zs l one two _ _ ne hit hit' footprint hab hba
  by_contra diff
  apply safe
  refine ⟨.thread (h,u),.thread (t,v),dst,acc,l,⟨?_,true,true,
    .inr (.inl ⟨_,⟨_,one⟩,rfl⟩),
    .inr (.inl ⟨_,⟨_,two⟩,rfl⟩),.inl rfl,_,hit,hit'⟩,footprint,hit,?_,hab,hba,?_⟩
  · rintro eq
    cases eq
    exact ne rfl
  · rintro ⟨⟨i,j,ei,ej,st⟩|⟨strong,_⟩,_,_⟩
    · cases ei
      cases ej
      exact ne st
    · exact weak_store hX one strong.2.1
  · rintro ⟨_,_,_,values⟩
    exact diff (values _ _ (.inl ⟨_,one⟩) (.inl ⟨_,two⟩))

/-- Equal words for two reads of the same scratch slot in a published
generation. For each byte, different unordered writers have the same payload by
`StoreAgree`; either strict order would hide one of the actual source writes. -/
theorem scratch_reads_agree {Q L m X g k a bs g' k' a' bs' n}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (agree : StoreAgree L X n)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩) (peer : X.get (g',k')=some ⟨2252,.rd a' bs'⟩)
    (cta : g/L.block=g'/L.block) (slot : g%L.block%4=g'%L.block%4)
    (ord : barOrdinal X g k=n+1) (ord' : barOrdinal X g' k'=n+1)
    (pub : PublishesAt L X (g/L.block) n) : bs=bs' := by
  obtain ⟨loc,size⟩ := Softmax.Export.scratch_read hp hX read
  obtain ⟨loc',size'⟩ := Softmax.Export.scratch_read hp hX peer
  have addr : a.loc=a'.loc := by rw [loc,loc',cta,slot]
  have rd : X.MemReads (.thread (g,k)) a bs := .inl ⟨_,read⟩
  have rd' : X.MemReads (.thread (g',k')) a' bs' := .inl ⟨_,peer⟩
  have len := (hX.rf _ _ _ rd).1
  have len' := (hX.rf _ _ _ rd').1
  apply List.ext_getElem?
  intro b
  by_cases byte : b<4
  swap
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
  obtain ⟨h,u,dst,ys,one⟩ := scratch_sample hp hX read ord pub (by omega : b<a.size)
  obtain ⟨t,v,acc,zs,two⟩ := scratch_sample hp hX peer ord' (cta ▸ pub) (by omega : b<a'.size)
  rw [one.value,two.value]
  suffices ys=zs by rw [this]
  by_cases same : h=t
  · subst t
    have ix := NamedBar.source_ordinal_unique one.sync two.sync (one.epoch.trans two.epoch.symm)
    have eq : u=v := by omega
    subst v
    exact (Kind.wr.inj (Event.mk.inj (Option.some.inj (one.store.symm.trans two.store))).2).2
  have hit : dst.Covers (a.loc.at b) := by
    simp [Acc.Covers,Loc.InRange,one.addr,one.size,Loc.at,byte]
  have hit' : acc.Covers (a.loc.at b) := by
    simp [Acc.Covers,Loc.InRange,two.addr,←addr,two.size,Loc.at,byte]
  have footprint : dst.SameFootprint acc :=
    ⟨one.addr.trans (addr.trans two.addr.symm),one.size.trans two.size.symm⟩
  have hab := not_hidden hp hX read ord (by omega) one two.store (two.cta.trans cta.symm)
    two.sync two.epoch hit'
  have hba := not_hidden hp hX peer ord' (by omega) two one.store (one.cta.trans cta)
    one.sync one.epoch (addr ▸ hit)
  rw [←addr] at hba
  exact agree one.store two.store ((ord_store one.store).symm.trans one.epoch)
    ((ord_store two.store).symm.trans two.epoch) same hit hit' footprint hab hba

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared

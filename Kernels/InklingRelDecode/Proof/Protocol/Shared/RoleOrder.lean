-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.OperandRead
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Reuse
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress
import Kernels.InklingRelDecode.Proof.Lib.RoleWord
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Kernel.Frame
import Lemmas.Kernel.IdenticalWrites
import Lemmas.Protocol.Region

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame PTX.Proof

private abbrev phase (X : Execution) (i : EvId) :=
  ((X.tr i.1).take i.2).countP (Execution.isBarId 1)

private def payload (n : Nat) := (b32 (if n=0 then 16777730 else 50529027)).toBytes

private structure Touch (L : Launch) (X : Execution) (i : EvId) (w : Bool) (a : Acc) (l : Loc) :
    Prop where
  launched : i.1<L.threads
  present : i.2<(X.tr i.1).length
  cta : i.1/L.block=l.cta
  same : phase X (i.1,i.2+1)=phase X i
  version : if w then phase X i%3=0 else phase X i%3=1
  value : w=true → a=Lib.wordAcc ⟨.shared,l.cta,L.sharedBase+213336⟩ ∧
    X.MemWrites (.thread i) a (payload (phase X i))

private theorem phase_same {X g k e} (get : X.get (g,k)=some e)
    (quiet : Execution.isBarId 1 e=false) :
    phase X (g,k+1)=phase X (g,k) := by
  unfold phase
  simp only
  rw [List.take_add_one,show (X.tr g)[k]?=_ from get,List.countP_append]
  simp [quiet]

private theorem touch {Q L m X ref a w l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (intent : X.Intent ref a w)
    (cov : a.Covers l) (loc : Iface.InRole L l) : ∃ i, ref=.thread i ∧ Touch L X i w a l := by
  obtain ⟨sp,lo,hi⟩ := loc
  rcases Execution.shared_intent intent cov sp with
    ⟨⟨g,k⟩,rfl,acc⟩|⟨i,b,j,rfl⟩|⟨i,x,y,z,rfl⟩|⟨i,x,y,z,rfl⟩|⟨_,_,_,_,_,⟨_,get⟩,_⟩|
      ⟨_,_,_,_,⟨_,get⟩⟩|⟨_,_,⟨_,get⟩⟩
  · refine ⟨_,rfl,?_⟩
    rcases acc with ⟨bs,⟨pc,get⟩,rfl⟩|⟨bs,⟨pc,get⟩,rfl⟩|⟨old,new,pc,get⟩
    · have tag := (read_outside_arena hp hX get cov sp).resolve_left (by omega)
      obtain rfl := tag.2
      obtain ⟨_,_,_,addr⟩ := Dispatch.Export.role_address hp hX get
      have ct := cov.2.1
      rw [addr] at ct
      exact ⟨Frame.lt_of_get hX get,(List.getElem?_eq_some_iff.mp get).1,ct.symm,
        phase_same get rfl,Export.publication_read hp hX get (.inl rfl),nofun⟩
    · obtain ⟨sp',ct,first,last⟩ := cov
      have sites := (publication_writers (b := l.addr-L.sharedBase) hp hX get (sp' ▸ sp)
        (by omega) (by omega)).2 (by omega) (by omega)
      rcases sites with rfl|rfl
      all_goals
        first
          | obtain ⟨addr,bytes⟩ := Lib.role_word hp hX get (.inl ⟨rfl,rfl⟩)
          | obtain ⟨addr,bytes⟩ := Lib.role_word hp hX get (.inr ⟨rfl,rfl⟩)
        rw [addr] at ct
        change l.cta=g/L.block at ct
        refine ⟨Frame.lt_of_get hX get,(List.getElem?_eq_some_iff.mp get).1,ct.symm,
          phase_same get rfl,?_,fun _ => ⟨ct ▸ addr,?_⟩⟩
      · have ph : phase X (g,k)=0 := Export.publication_store hp hX get rfl
        rw [ph]
        decide
      · have ph : phase X (g,k)=0 := Export.publication_store hp hX get rfl
        rw [ph]
        exact .inl ⟨_,bytes ▸ get⟩
      · have ph : phase X (g,k)=3 := Export.publication_store hp hX get rfl
        rw [ph]
        decide
      · have ph : phase X (g,k)=3 := Export.publication_store hp hX get rfl
        rw [ph]
        exact .inl ⟨_,bytes ▸ get⟩
    · have wr : X.Intent (.thread (g,k)) a true := .inr (.inr ⟨old,new,pc,get⟩)
      rcases Lib.write_intents hX wr with ⟨i,q,bs,eq,h⟩|⟨_,_,_,_,_,_,eq,_⟩
      · cases eq
        rw [get] at h
        cases h
      · cases eq
  · obtain ⟨_,size,foot⟩ := intent
    have lim := operand_byte hp hX hf foot
    obtain ⟨_,_,_,end'⟩ := cov
    omega
  · obtain ⟨_,_,_,⟨_,get⟩,_⟩ := intent
    exact (Lib.no_tensorStore hX get).elim
  · obtain ⟨_,sp',addr,issue,byte,size⟩ := intent
    have := cov.2.2
    exact (outside_tiles (l := a.loc) hp hX (by omega) (by omega)
      ⟨i,addr,sp',issue,x,y,z,byte⟩).elim
  · exact (Lib.no_clc hX get).elim
  · exact (Lib.no_copy hX get).elim
  · exact (Lib.no_bulkPrefetch hX get).elim

/-- The two role-word publications and both dispatch reads are ordered by barrier
one. Writers of one generation store the identical four bytes. -/
theorem role_ordered {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : ByteOrdered L X (Iface.InRole L) := by
  rintro e f a b l ⟨_,we,wf,he,hf',write,_⟩ ha hb role diff
  obtain ⟨i,rfl,ti⟩ := touch hp hX hf he ha role
  obtain ⟨j,rfl,tj⟩ := touch hp hX hf hf' hb role
  have edge {i j a b w v} (x : Touch L X i w a l) (y : Touch L X j v b l)
      (lt : phase X i < phase X j) : ByteCausality L X l (.thread i) (.thread j) := by
    apply ByteCausality.direct
    apply Or.inl
    apply publication_handoff hp hX i.1 j.1 i.2 j.2
      ⟨x.launched,y.launched,x.cta.trans y.cta.symm⟩ y.present
    exact x.same.trans_lt lt
  rcases lt_trichotomy (phase X i) (phase X j) with lt|eq|gt
  · exact .inl (edge ti tj lt)
  · exfalso
    apply diff
    have vi := ti.version
    have vj := tj.version
    rw [eq] at vi
    have both : we=true ∧ wf=true := by
      cases we <;> cases wf <;> simp_all
    obtain ⟨rfl,rfl⟩ := both
    obtain ⟨ai,wi⟩ := ti.value rfl
    obtain ⟨aj,wj⟩ := tj.value rfl
    refine ⟨he,hf',by rw [ai,aj]; exact ⟨rfl,rfl⟩,?_⟩
    intro xs ys wx wy
    rw [(wx.unique wi).2,(wy.unique wj).2,eq]
  · exact .inr (edge tj ti gt)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared

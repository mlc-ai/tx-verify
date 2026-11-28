-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.RoleOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Ordered
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.QueryOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalWrites
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalInject
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalReads
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchOrdered
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchPlace
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchButterfly
public import Kernels.InklingRelDecode.Proof.Protocol.Alpha.Agree

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- The conflicts of a pair the class guard admits are ordered at every byte: every conflict is
ordered (`Protocol.Shared.role_ordered`, `mbar_ordered`, `query_ordered`, `kv_ordered`,
`base_ordered`, `scratch_ordered`, with `warp_stores_equal` for the stores of one warp, whose first
stage is `alpha_agree`) or an input read of global memory or two stores of one epilogue site. The
kernel has no atomic and no `.relaxed`/`.acquire`/`.release`/`.volatile` access outside the
mbarriers. -/
theorem Safe.ordered (hp : Pre Q L m)
    {X : Execution} (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (gr : Iface.GlobalReads Q X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    {e f a b l} (con : Conflict X e f a b) (ca : a.Covers l) (cb : b.Covers l)
    (ne : ¬ SameValueWrites X e f a b) (guard : ¬ (a.SameFootprint b ∧ MorallyStrong L X e f a b)) :
    ByteCausality L X l e f ∨ ByteCausality L X l f e := by
  by_cases reg : Iface.InRole L l ∨ Iface.InMbar L l ∨ Iface.InQ L l ∨ Iface.InKv L l ∨
      Iface.InBase L l
  · rcases reg with word|mbar|query|kv|base
    · exact Protocol.Shared.role_ordered hp hX hf e f a b l con ca cb word ne
    · exact Protocol.Shared.mbar_ordered hp hX e f a b l con ca cb mbar ne
    · exact Protocol.Shared.query_ordered hp hX hf e f a b l con ca cb query ne
    · exact Protocol.Shared.kv_ordered hp hX hf rows init words
        hu e f a b l con ca cb kv ne
    · exact Protocol.Shared.base_ordered hp hX hf rows init words
        hu e f a b l con ca cb base ne
  by_cases gw : l.space = .global
  · exfalso
    obtain ⟨_,we,wf,ie,jf,hw,_⟩ := con
    cases we <;> cases wf
    · simp at hw
    · have inp := gr e a l ie ca gw
      exact nub ⟨Q,f,b,l,hp,jf,cb,gw,inp.2.1,inp.2.2⟩
    · have inp := gr f b l jf cb gw
      exact nub ⟨Q,e,a,l,hp,ie,ca,gw,inp.2.1,inp.2.2⟩
    · obtain ⟨i,pc,bs,rfl,geti,si⟩ := Protocol.Shared.global_writer hp hX ie (ca.1.symm.trans gw)
      obtain ⟨j,pc',bs',rfl,getj,sj⟩ := Protocol.Shared.global_writer hp hX jf
        (cb.1.symm.trans gw)
      have site : ∀ {p}, p ∈ Protocol.Shared.outputSites → Protocol.Shared.IsStoreSite p := by
        intro p hp'
        simp only [Protocol.Shared.outputSites, List.mem_cons, List.mem_map, List.mem_range] at hp'
        rcases hp' with rfl | ⟨n,hn,rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨⟨n,hn⟩,rfl⟩
      obtain ⟨same,fp⟩ := Protocol.Shared.store_pair hp hX hf geti getj (site si) (site sj) ca cb
      exact guard ⟨fp,Or.inl ⟨i,j,rfl,rfl,same⟩,Iff.rfl,a,b,rfl,rfl,fp⟩
  · have off : ¬(Iface.InRole L l ∨ Iface.InQ L l ∨ Iface.InKv L l ∨ Iface.InBase L l) :=
      fun x => reg (by rcases x with x|x|x|x <;> simp [x])
    obtain ⟨_,we,wf,ie,jf,hw,_⟩ := id con
    have scratch : Iface.InCount L l ∨ Iface.InScratch L l := by
      cases we <;> cases wf
      · simp at hw
      · exact Protocol.Shared.write_place hp hX hf jf cb gw off
      · exact Protocol.Shared.write_place hp hX hf ie ca gw off
      · exact Protocol.Shared.write_place hp hX hf ie ca gw off
    exact Protocol.Shared.scratch_ordered hp hX hf
      (Protocol.Shared.warp_stores_equal hp hX hf (Protocol.Shared.alpha_agree hp hX hf))
      e f a b l con ca cb scratch ne

theorem Safe.noRace (hp : Pre Q L m)
    {X : Execution} (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (gr : Iface.GlobalReads Q X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ¬ Race L X := by
  rintro ⟨e,f,a,b,l,con,size,ca,weak,left,right,ne⟩
  have cb := (size.covers l).mp ca
  exact (Safe.ordered hp hX hf rows init words hu gr nub con ca cb ne
    fun ⟨_,ms⟩ => weak ms).elim left right

end PTX.Kernels.InklingRelDecode.Proof.Top

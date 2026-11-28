-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Scratch
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Reuse
import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Lemmas.Protocol.NamedBarPhaseKeys
import Lemmas.Kernel.Frame
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame

/-- Every scratch writer follows the count-pair publication of its CTA, even in
prefixes in which other data lanes have yet to reach the scratch read. -/
theorem pair_before_scratch {Q L m X g h u v a b xs ys} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (pair : X.get (g,u)=some ⟨571,.wr a xs⟩) (scratch : X.get (h,v)=some ⟨2250,.wr b ys⟩)
    (cta : g/L.block=h/L.block) : baseCausality L X (g,u) (h,v) := by
  have early := Export.publication_store hp hX pair (phase := 0) rfl
  have late := Export.publication_store hp hX scratch (phase := 2) rfl
  apply publication_handoff hp hX g h u v ⟨lt_of_get hX pair,lt_of_get hX scratch,cta⟩
    (List.getElem?_eq_some_iff.mp scratch).1
  change ((X.tr g).take (u+1)).countP _ < ((X.tr h).take v).countP _
  rw [List.take_add_one,show (X.tr g)[u]? = _ from pair,List.countP_append,early,late]
  change 0 < 2
  decide

/-- Two observed arrivals at the same barrier-zero ordinal order events on their
respective sides. Only the four data warps participate in counted instances. -/
theorem scratch_handoff {Q L m X g h u v i j pc pc' cn cn'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (a : X.get (g,i)=some ⟨pc,.bar 0 cn .sync⟩) (b : X.get (h,j)=some ⟨pc',.bar 0 cn' .sync⟩)
    (cta : g/L.block=h/L.block) (lg : g%L.block<128) (lh : h%L.block<128)
    (ord : ((X.tr g).take i).countP (Execution.isBarId 0)=
      ((X.tr h).take j).countP (Execution.isBarId 0))
    (left : u < i) (right : j < v) (present : v < (X.tr h).length) :
    baseCausality L X (g,u) (h,v) := by
  apply NamedBar.D_same_ordinal_baseCausality hX (Export.barZeroSources hp hX)
    (by simp [CtaBarrier.warps,hp.block]) (Finset.card_range _)
    (by simp [CtaBarrier.warps,hp.block]) (by simp [CtaBarrier.target])
    ⟨lt_of_get hX a,lt_of_get hX b,cta⟩ a b (by omega)
    (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega)) ord left right present

/-- Once the selected warp has published a matching word through barrier 2251,
every byte actually comes from a scratch store. Initialization, the count-pair
store, overwritten stores, and future stores are all excluded. -/
theorem scratch_byte {Q L m X g h k v i j ac dst bs ys cn cn' byte} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (read : X.get (g,k)=some ⟨2252,.rd ac bs⟩) (writer : X.get (h,v)=some ⟨2250,.wr dst ys⟩)
    (pub : X.get (h,i)=some ⟨2251,.bar 0 cn .sync⟩)
    (sync : X.get (g,j)=some ⟨2251,.bar 0 cn' .sync⟩)
    (lg : g%L.block<128) (lh : h%L.block<128) (cta : h/L.block=g/L.block)
    (ord : ((X.tr h).take i).countP (Execution.isBarId 0)=
      ((X.tr g).take j).countP (Execution.isBarId 0))
    (before : v < i) (after : j < k) (inWord : byte < ac.size)
    (covers : dst.Covers (ac.loc.at byte)) :
    ∃ t u acc data, X.rf (.thread (g,k)) byte=some (.thread (t,u)) ∧
      X.get (t,u)=some ⟨2250,.wr acc data⟩ ∧ t/L.block=g/L.block ∧
      t%L.block/32%4=g%L.block%4 ∧ bs[byte]?=some data[byte]? ∧
      ¬baseCausality L X (t,u) (h,v) ∧ ¬baseCausality L X (g,k) (t,u) := by
  have edge := scratch_handoff hp hX pub sync cta lh lg ord before after
    (List.getElem?_eq_some_iff.mp read).1
  have rd : X.MemReads (.thread (g,k)) ac bs := .inl ⟨_,read⟩
  have wr : X.MemWrites (.thread (h,v)) dst ys := .inl ⟨_,writer⟩
  have hide := hX.hidden _ _ _ byte (.thread (h,v)) dst ys rd inWord wr covers (.direct (.inl edge))
  have source := (hX.rf _ _ _ rd).2 byte inWord
  cases rf : X.rf (.thread (g,k)) byte with
  | none => simp [rf] at hide
  | some ref =>
    rw [rf] at source hide
    obtain ⟨acc,data,w,cov,val⟩ := source
    obtain ⟨t,u,rfl,ct,addr,_,origin⟩ := scratch_source hp hX read inWord w cov
    have old : ¬baseCausality L X (t,u) (h,v) := fun x => hide (.direct (.inl x))
    rcases origin with ⟨_,pair⟩|⟨lane,get⟩
    · exact (old (pair_before_scratch hp hX pair writer (ct.trans cta.symm))).elim
    · exact ⟨t,u,acc,data,rfl,get,ct,lane,by simpa [wbyte,addr,Loc.at] using val,old,
        fun x => hX.noFuture _ _ _ byte _ rd inWord rf (.direct (.inl x))⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
